import BoltProof.Model.Token

/-!
# BoltProof.Model.Spend

A transition `τ : T(n) → T(n+1)` (`docs/formal-proof.md` §1.4): the transaction that spends a
token, seen from the covenant that runs on that input. `expectedOuts` is the deterministic
output list of Lemma 2 / Lemma 6 / Lemma 7: the covenant reconstructs exactly these outputs
and welds them to the transaction through `hashOutputs`.
-/

namespace BoltProof

/-- The transition class (§1.4). -/
inductive Kind
  | commit
  | settle
  | melt
deriving DecidableEq, Repr

/-- A transaction output as the model sees it. -/
inductive Out (Txid : Type)
  /-- A BOLT token output. -/
  | token (t : Token Txid)
  /-- The `b017` pay-to-proof marker output a commit emits to a recipient. -/
  | proof (pkh : PKH)
  /-- A plain P2PKH output (change, or a melt payout). -/
  | p2pkh (pkh : PKH)
  /-- Anything else. -/
  | other
deriving DecidableEq, Repr

namespace Out

variable {Txid : Type}

def isToken : Out Txid → Bool
  | .token _ => true
  | _ => false

def isP2pkh : Out Txid → Bool
  | .p2pkh _ => true
  | _ => false

def token? : Out Txid → Option (Token Txid)
  | .token t => some t
  | _ => none

end Out

/-- A transaction, abstracted: the fields the covenant reads through the sighash preimage. -/
structure TxDesc (Txid : Type) where
  version : Int
  inputs : List (Outpoint Txid)
  outputs : List (Out Txid)
  lockTime : Nat
deriving DecidableEq, Repr

namespace TxDesc

variable {Txid : Type}

/-- The token outputs of a transaction, in output order. -/
def tokens (tx : TxDesc Txid) : List (Token Txid) := tx.outputs.filterMap Out.token?

end TxDesc

/-- One covenant execution: the spend of token `spent` at input `inputIndex` of `tx`, with
everything the unlocking script supplies. -/
structure Spend (Txid : Type) where
  tx : TxDesc Txid
  /-- The input the spent token sits at (the covenant runs there). -/
  inputIndex : Nat
  kind : Kind
  /-- The mode: chosen by a commit, forced by the spent `txoType` on a settle. -/
  mode : Mode
  /-- The token being spent (the fields of the locking script that runs). -/
  spent : Token Txid
  spentOutpoint : Outpoint Txid
  /-- The second token input of a merge commit, with its outpoint. -/
  other : Option (Token Txid × Outpoint Txid)
  /-- The public key presented to `OP_CHECKSIG` (Lemma 1). -/
  signer : PubKey
  sig : Sig
  /-- The sighash flag byte (`0x41`, Lemma 1). -/
  sigHashType : Nat
  /-- The recipient a commit names (`pubKeyHashCommit`). -/
  recipient : PKH
  /-- The second recipient of a split commit. -/
  recipient2 : PKH
  /-- The split piece a split commit names. -/
  piece : Nat
  /-- The rebuilt grandparent transaction a settle supplies (Lemma 3), or `none` (Lemma 4). -/
  anc : Option (TxDesc Txid)
  /-- The rebuilt other-grandparent transaction of a merge settle. -/
  ancB : Option (TxDesc Txid)

namespace Spend

variable {Txid : Type}

/-- The token a commit produces (Lemma 2): ownership stays with the holder, the recipient is
*named* in `commitment`, lineage pointers shift by one, the issuer is copied verbatim. -/
def commitToken (s : Spend Txid) : Token Txid :=
  { owner := s.spent.owner
    commitment := s.recipient
    commitment2 := if s.mode = .split then s.recipient2 else []
    txoType := s.mode.commitType
    parent := some s.spentOutpoint
    grandparent := s.spent.parent
    otherGrandparent :=
      match s.mode, s.other with
      | .merge, some (o, _) => o.parent
      | _, _ => none
    issuer := s.spent.issuer
    balance := s.spent.balance
    balanceCommit :=
      match s.mode, s.other with
      | .split, _ => s.piece
      | .merge, some (o, _) => o.balance
      | _, _ => 0 }

/-- The token(s) a settle produces at output index `i` (Lemma 2 / Lemma 6): ownership moves
to the committed recipient, the commitment is cleared to the zero hash the bytes write, the type
is the matching settle type, the balance is `settledBalance`. -/
def settleToken (fam : Fam) (s : Spend Txid) (i : Nat) : Token Txid :=
  { owner := if i = 0 then s.spent.commitment else s.spent.commitment2
    commitment := zeroPKH
    commitment2 := []
    txoType := fam.settleOf s.spent.txoType
    parent := some s.spentOutpoint
    grandparent := s.spent.parent
    otherGrandparent := none
    issuer := s.spent.issuer
    balance := s.spent.settledBalance fam i
    balanceCommit := 0 }

/-- **Lemma 2 (output determinism).** The outputs the covenant reconstructs and welds to the
transaction through `hashOutputs`, before any change output. -/
def expectedOuts (fam : Fam) (s : Spend Txid) : List (Out Txid) :=
  match s.kind with
  | .commit =>
      .token s.commitToken :: .proof s.recipient ::
        (if s.mode = .split then [.proof s.recipient2] else [])
  | .settle =>
      if fam.modeOfCommitType s.spent.txoType = some .split then
        [.token (s.settleToken fam 0), .token (s.settleToken fam 1)]
      else
        [.token (s.settleToken fam 0)]
  | .melt => []

/-- The outputs a spend may carry before its change (Lemma 2): the reconstructed ones in the covenant's
order or, for a split settle only, its two settled tokens in the other order. The fungible script lets
the spender choose that order (`lean/GLUE-PLAN.md` §7 Q3). It is safe to admit: both tokens still go to
the committed recipients with the committed balances, a token's outpoint is wherever it sits, and no
later check reads the order (the anchor names its proof, not a position, `Accepts.l3_rebuild`), so
nothing a theorem depends on changes. -/
def OutsOK (fam : Fam) (s : Spend Txid) (outs : List (Out Txid)) : Prop :=
  outs = s.expectedOuts fam ∨
    (s.kind = .settle ∧ fam.modeOfCommitType s.spent.txoType = some .split ∧
      outs = [.token (s.settleToken fam 1), .token (s.settleToken fam 0)])

/-- The token outputs the transaction actually carries. -/
def tokenOuts (s : Spend Txid) : List (Token Txid) := s.tx.tokens

/-- The token outpoints this spend consumes. -/
def consumed (s : Spend Txid) : List (Outpoint Txid) :=
  s.spentOutpoint :: (match s.other with | some (_, o) => [o] | none => [])

end Spend

end BoltProof
