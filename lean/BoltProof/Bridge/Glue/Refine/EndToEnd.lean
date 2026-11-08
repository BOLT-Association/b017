import BoltProof.Bridge.Glue.Refine.MinSimple
import BoltProof.Theorems.Ownership
import BoltProof.Theorems.StateMachine
import BoltProof.Theorems.Balance
import BoltProof.Theorems.Authenticity

/-!
# `MinSimpleBOLT`: what is proved end to end

The refinement (`Refine/MinSimple.lean`) composed with Layer 1's per-input theorems, so the
claim is explicit: a spend of a `MinSimpleBOLT` token that the consensus rules judge valid is a
spend `Accepts` admits, hence Lemma 1 (the owner signed this transaction), Theorem 2
(ownership, under A2), Theorem 4's step (every token output is typed by an edge of the NFT
machine), Theorem 3's step (value is conserved) and Theorem 1's step (every token output carries the
spent token's issuer and names the spent outpoint as its parent; a genesis moves only under the issuer's
key) hold of the shipped bytes. The hypotheses are
`RealSpend`: the spend's well-formedness, its verdict, and `Residual` (the cryptographic
assumptions, the lineage link, and the clauses the bytes do not enforce, as
`Refine/MinSimple.lean` lays them out). The run-level theorems (Theorem 1's authenticity over a
chain, Theorem 5's proof gating) follow once a chain of real spends is read as a model `Run`,
the composition `lean/GLUE-PLAN.md` leaves open.
-/

set_option autoImplicit false

namespace BoltProof.Glue.MinSimple

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Tx BsvScript.Sighash
  BsvScript.TxContext
open BoltProof.Glue.Serial
open BoltProof.Bridge (params)

/-- A real spend of a `MinSimpleBOLT` token, as `minSimple_refines` takes it: the lock's fields and
the unlocking arguments are well-formed, the transaction is well-formed, the token sits at a real
input of positive value, the residual assumptions hold, the unlocking script leaves the arguments
on the stack, and the consensus rules judge the spend valid. -/
structure RealSpend (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args) (S : List Bytes)
    (scriptSig : Bytes) : Prop where
  hwf : WF f
  hargs : castToBool a.pre = true → ArgsWF a
  hty : f.ty = [0x00] ∨ f.ty = [0x21]
  htx : TxWF tx
  hamt : amt < 2 ^ 64
  hi : i < tx.inputs.length
  hnz : decode (serOutPoint (inputAt tx i)) ≠ 0
  hres : Residual P tx i amt f a
  hstack : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust (some (lockOf f)))
    scriptSig [] 0).2).stack = a.stack ++ S
  hvalid : Eval.verifyScript params (txContext tx i amt) scriptSig (lockOf f) = .valid

variable {P : Prims Bytes} {tx : Tx} {i amt : Nat} {f : Fields} {a : Args} {S : List Bytes} {scriptSig : Bytes}

/-- **The bytes accept only what the model accepts.** -/
theorem accepts_of_real (h : RealSpend P tx i amt f a S scriptSig) : Accepts P .nft (spendOf tx i f a) :=
  minSimple_refines P tx i amt f a S scriptSig h.hwf h.hargs h.hty h.htx h.hamt h.hi h.hnz h.hres h.hstack
    h.hvalid

/-- **Lemma 1 of the shipped bytes.** The key presented hashes to the owner, the signature verifies
over this transaction's digest, and the flag byte is `0x41`. -/
theorem real_presented (h : RealSpend P tx i amt f a S scriptSig) :
    P.h160 a.pk = f.pkh ∧ P.verify a.pk (P.sighash (absTx tx) i) a.sig = true ∧ a.sig.getLast?.getD 0 = 0x41 :=
  t2_presented (accepts_of_real h)

/-- **Theorem 2 of the shipped bytes (ownership).** Under A2 for the owner's key, a valid spend
means the owner signed this very transaction. -/
theorem real_ownership {pkO : PubKey} {signed : Msg → Prop} (hO : P.h160 pkO = f.pkh)
    (hS : OwnerSecrecy P pkO signed) (h : RealSpend P tx i amt f a S scriptSig) :
    signed (P.sighash (absTx tx) i) :=
  t2_ownership hO hS (accepts_of_real h)

/-- **Theorem 2, contrapositive, of the shipped bytes.** Without the owner's signature on this
transaction, the consensus rules do not judge the spend valid. -/
theorem real_no_keyless_spend {pkO : PubKey} {signed : Msg → Prop} (hO : P.h160 pkO = f.pkh)
    (hS : OwnerSecrecy P pkO signed) (hn : ¬ signed (P.sighash (absTx tx) i))
    (hwf : WF f) (hargs : castToBool a.pre = true → ArgsWF a) (hty : f.ty = [0x00] ∨ f.ty = [0x21])
    (htx : TxWF tx) (hamt : amt < 2 ^ 64) (hi : i < tx.inputs.length)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0) (hres : Residual P tx i amt f a)
    (hS1 : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust (some (lockOf f)))
      scriptSig [] 0).2).stack = a.stack ++ S) :
    Eval.verifyScript params (txContext tx i amt) scriptSig (lockOf f) ≠ .valid :=
  fun hv => t2_no_keyless_spend hO hS hn
    (accepts_of_real ⟨hwf, hargs, hty, htx, hamt, hi, hnz, hres, hS1, hv⟩)

/-- **Theorem 4's step of the shipped bytes.** Every token output of a valid spend is typed by an
edge of the NFT state machine from the spent token's type. -/
theorem real_state_machine (h : RealSpend P tx i amt f a S scriptSig) :
    ∀ t ∈ (absTx tx).tokens, Fam.edge .nft (tokenOf f).txoType t.txoType :=
  t4_step (accepts_of_real h)

/-- **Theorem 3's step of the shipped bytes.** The value the token outputs carry, plus what a melt
destroys, is the value consumed. -/
theorem real_value_conserved (h : RealSpend P tx i amt f a S scriptSig) :
    ((absTx tx).tokens.map Token.value).sum + (if kindOf f a = .melt then (tokenOf f).value else 0) =
      (tokenOf f).value + 0 :=
  Spend.value_conserved (accepts_of_real h)

/-- **Theorem 1's step of the shipped bytes.** Every token output of a valid spend carries the spent
token's issuer and names the spent outpoint as its parent: one hop of a lineage is what the covenant
wrote from the token it spent. -/
theorem real_issuer_carried (h : RealSpend P tx i amt f a S scriptSig) :
    ∀ t ∈ (absTx tx).tokens, t.issuer = (tokenOf f).issuer ∧
      t.parent = some ⟨(inputAt tx i).prevHash, (inputAt tx i).prevIndex⟩ :=
  t1_step (accepts_of_real h)

/-- **Lemma 5 of the shipped bytes.** A parentless token, the genesis, moves only under the issuer's
key: the key presented is the issuer's. -/
theorem real_genesis_needs_issuer (h : RealSpend P tx i amt f a S scriptSig) (hg : (tokenOf f).isGenesis) :
    a.pk = (tokenOf f).issuer :=
  t1_genesis_signer (accepts_of_real h) hg

end BoltProof.Glue.MinSimple
