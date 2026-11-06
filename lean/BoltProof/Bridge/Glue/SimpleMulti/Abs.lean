import BoltProof.Bridge.Glue.SimpleMulti.Lock
import BoltProof.Bridge.Glue.MinSimple.Abs

/-!
# The `SimpleMultiBOLT` abstraction into the model

A real fungible spend read in the model's vocabulary (`Model/Spend.lean`), as `MinSimple/Abs.lean` reads an NFT
spend: a lock's fields become a `Token` (`tokenOf`), an output becomes an `Out` by its script (`outOf`), a
transaction a `TxDesc` (`absTx`), and the spend of the token at input `i` a `Spend` (`spendOf`).

Two readings are the fungible family's own. The balances are script numbers (the covenant reads them with
`OP_BIN2NUM` and bounds them below by zero), so a balance field reads as the natural number it decodes to. The
second commitment the bytes write as twenty zero bytes when there is none, where `Spend.commitToken` and
`Spend.settleToken` write `[]`; `com2Of` reads the zero hash as `[]`.

`spendOf` takes the merge's other token input and the two rebuilt ancestors as arguments: the refinement states
that the choice the run's facts determine (the other input's fields its own run pins, the transactions whose
hashes the rebuilds compare with the grandparent outpoints) makes `Accepts` hold.
-/

set_option autoImplicit false

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget BsvScript.Tx
open BoltProof.Bridge.Generated
open BoltProof.Glue.MinSimple (outpointOf proofScript p2pkhScript)

/-- A balance field as the model's balance: the script number it decodes to (non-negative on every path the
covenant accepts). -/
def balOf (b : Bytes) : Nat := (decode b).toNat

/-- The second commitment as the model writes it: the zero hash is no commitment. -/
def com2Of (b : Bytes) : PKH := if b = zeroPKH then [] else b

/-- The token a lock's fields describe. -/
def tokenOf (f : Fields) : Token Bytes :=
  { owner := f.pkh, commitment := f.com, commitment2 := com2Of f.com2, txoType := f.ty.headD 0,
    parent := outpointOf f.parent, grandparent := outpointOf f.gp, otherGrandparent := outpointOf f.ogp,
    issuer := f.issuer, balance := balOf f.bal, balanceCommit := balOf f.balCommit }

/-- An output as the model sees it, by its script alone: a decodable fungible lock is a token, the pay-to-proof
template is a proof output, P2PKH is P2PKH, anything else is other. -/
def outOf (o : TxOut) : Out Bytes :=
  match decodeLock o.scriptPubKey with
  | some f => .token (tokenOf f)
  | none =>
    if o.scriptPubKey.length = 29 ∧ o.scriptPubKey.take 7 = [2, 0xb0, 0x17, 0x88, 0x76, 0xa9, 0x14] ∧
        o.scriptPubKey.drop 27 = [0x88, 0xac] then .proof ((o.scriptPubKey.drop 7).take 20)
    else if o.scriptPubKey.length = 25 ∧ o.scriptPubKey.take 3 = [0x76, 0xa9, 0x14] ∧
        o.scriptPubKey.drop 23 = [0x88, 0xac] then .p2pkh ((o.scriptPubKey.drop 3).take 20)
    else .other

/-- A transaction as the model sees it. -/
def absTx (tx : Tx) : TxDesc Bytes :=
  { version := tx.version, inputs := tx.inputs.map fun i => ⟨i.prevHash, i.prevIndex⟩,
    outputs := tx.outputs.map outOf, lockTime := tx.lockTime }

/-- The settled (even) types. -/
def settledTy (b : Bytes) : Prop := b = [0x20] ∨ b = [0x22] ∨ b = [0x24]

instance (b : Bytes) : Decidable (settledTy b) := by unfold settledTy; exact inferInstance

/-- The kind of a spend: a melt presents no preimage; otherwise the spent type's parity says which half of the
state machine runs. -/
def kindOf (f : Fields) (a : Args) : Kind :=
  if castToBool a.pre then (if settledTy f.ty then .commit else .settle) else .melt

/-- The mode a commit names by its next type. -/
def modeOfNext (b : Bytes) : Mode := if b = [0x23] then .split else if b = [0x25] then .merge else .transfer

/-- The mode of a spend: chosen by a commit's next type, forced by the spent commit type on a settle. -/
def modeOf (f : Fields) (a : Args) : Mode :=
  if kindOf f a = .commit then modeOfNext a.nty
  else (Fam.modeOfCommitType .fungible (f.ty.headD 0)).getD .transfer

/-- The spend of the token `f` at input `i` of `tx` with the unlocking arguments `a`, as the model sees it,
given the merge commit's other token input and the two rebuilt ancestors. -/
def spendOf (tx : Tx) (i : Nat) (f : Fields) (a : Args) (other : Option (Fields × Outpoint Bytes))
    (ancA ancB : Option Tx) : Spend Bytes :=
  { tx := absTx tx, inputIndex := i, kind := kindOf f a, mode := modeOf f a, spent := tokenOf f,
    spentOutpoint := ⟨(Sighash.inputAt tx i).prevHash, (Sighash.inputAt tx i).prevIndex⟩,
    other := other.map fun o => (tokenOf o.1, o.2), signer := a.pk, sig := a.sig,
    sigHashType := a.sig.getLast?.getD 0, recipient := a.pkh1, recipient2 := com2Of a.pkh2,
    piece := balOf a.nbc, anc := ancA.map absTx, ancB := ancB.map absTx }

end BoltProof.Glue.SimpleMulti
