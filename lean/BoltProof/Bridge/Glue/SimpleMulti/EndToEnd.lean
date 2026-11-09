import BoltProof.Bridge.Glue.SimpleMulti.Refine
import BoltProof.Bridge.Glue.SimpleMulti.RefineGp
import BoltProof.Bridge.Glue.SimpleMulti.RefineMerge
import BoltProof.Bridge.Glue.SimpleMulti.RefineMergeSettle
import BoltProof.Theorems.Ownership
import BoltProof.Theorems.StateMachine
import BoltProof.Theorems.Balance
import BoltProof.Theorems.Authenticity

/-!
# `SimpleMultiBOLT`: what is proved end to end

The fungible refinement's four stages (`Refine.lean`, `RefineGp.lean`, `RefineMerge.lean`,
`RefineMergeSettle.lean`) composed with Layer 1's per-input theorems, so the claim is explicit, as
`Refine/EndToEnd.lean` makes it for `MinSimpleBOLT`: a spend of a `SimpleMultiBOLT` token that the
consensus rules judge valid is a spend `Accepts` admits, hence Lemma 1 (the owner signed this
transaction), Theorem 2 (ownership, under A2), Theorem 4's step (every token output is typed by an
edge of the fungible machine), Theorem 3's step (value is conserved) and Theorem 1's step (every token
output carries the spent token's issuer and names the spent outpoint as its parent; a genesis moves only
under the issuer's key) hold of the shipped bytes.

Each stage's hypotheses are one structure: `RealSpend` (a commit, a settle without a grandparent, or a
melt), `RealSettleGp` (a transfer or split settle with a grandparent), `RealMergeCommit` (a merge commit
at its first token input, with the second token input's run) and `RealMergeSettle` (a merge settle). They
carry the spend's well-formedness, its verdict, and the residual assumptions `Residual`, `ResidualGp`
and `GpRealB` as the refinement files lay them out: the cryptographic ones, the lineage links, the clauses
the bytes do not enforce, and the fungible family's open questions (`lean/README.md`, "The glue"). The
consequences are stated once, of any spend read from the bytes, so each stage reaches them through its
`accepts_of_*` theorem. The run-level theorems (Theorem 1's authenticity over a chain, Theorem 3's
conservation over a history, Theorem 5's proof gating) follow once a chain of real spends is read as a
model `Run` (`Chain.lean`).
-/

set_option autoImplicit false

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget BsvScript.Tx
  BsvScript.Sighash BsvScript.TxContext
open BoltProof.Glue.Serial
open BoltProof.Bridge (params)

/-! ## The four stages, each as one structure of hypotheses -/

/-- A real spend of a `SimpleMultiBOLT` token as `simpleMulti_refines_basic` takes it: a commit, a settle
of a token without a grandparent, or a melt. The lock's fields and the unlocking arguments are
well-formed, the types are protocol types, no merge is involved, the transaction is well-formed, the token
sits at a real input of positive value, the residual assumptions hold, the unlocking script leaves the
arguments on the stack, and the consensus rules judge the spend valid. -/
structure RealSpend (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args) (S : List Bytes)
    (scriptSig : Bytes) : Prop where
  hwf : WF f
  hargs : castToBool a.pre = true → ArgsWF a
  hty : SmbType f.ty
  hnty : castToBool a.pre = true → SmbType a.nty
  hnm : f.ty ≠ [0x25] ∧ a.nty ≠ [0x25]
  hgp0 : ¬ settledTy f.ty → decode f.gp = 0
  hgen : decode f.parent = 0 → settledTy f.ty
  hogp : decode f.ogp = 0
  hbal : 0 ≤ decode f.bal ∧ decode f.bal ≤ maxBalance
  hcom2 : f.ty = [0x23] → f.com2 ≠ zeroPKH
  hpkh2 : a.nty = [0x23] → a.pkh2 ≠ zeroPKH
  htx : TxWF tx
  hamt : amt < 2 ^ 64
  hi : i < tx.inputs.length
  hnz : decode (serOutPoint (inputAt tx i)) ≠ 0
  hres : Residual P tx i amt f a
  hstack : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust
    (some (lockScript f))) scriptSig [] 0).2).stack = a.stack ++ S
  hvalid : Eval.verifyScript params (txContext tx i amt) scriptSig (lockScript f) = .valid

/-- **The bytes accept only what the model accepts** (first stage). -/
theorem accepts_of_real {P : Prims Bytes} {tx : Tx} {i amt : Nat} {f : Fields} {a : Args} {S : List Bytes}
    {scriptSig : Bytes} (h : RealSpend P tx i amt f a S scriptSig) :
    Accepts P .fungible (spendOf tx i f a none none none) :=
  simpleMulti_refines_basic P tx i amt f a S scriptSig h.hwf h.hargs h.hty h.hnty h.hnm h.hgp0 h.hgen
    h.hogp h.hbal h.hcom2 h.hpkh2 h.htx h.hamt h.hi h.hnz h.hres h.hstack h.hvalid

/-- A real transfer or split settle of a token with a grandparent, as `simpleMulti_refines_settle_gp`
takes it, with `G` the grandparent transaction and `ResidualGp` its lineage link, the rebuild's piece widths
and the anchor index. -/
structure RealSettleGp (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args) (S : List Bytes)
    (scriptSig : Bytes) (G : Tx) : Prop where
  hwf : WF f
  hA : ArgsWF a
  hty : SmbType f.ty
  hnty : SmbType a.nty
  hpre : castToBool a.pre = true
  hset : ¬ settledTy f.ty
  hnm : f.ty ≠ [0x25]
  hgp : decode f.gp ≠ 0
  hgen : decode f.parent = 0 → settledTy f.ty
  hogp : decode f.ogp = 0
  hcom2 : f.ty = [0x23] → f.com2 ≠ zeroPKH
  htx : TxWF tx
  hamt : amt < 2 ^ 64
  hi : i < tx.inputs.length
  hnz : decode (serOutPoint (inputAt tx i)) ≠ 0
  hres : Residual P tx i amt f a
  hgr : ResidualGp P f a G
  hstack : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust
    (some (lockScript f))) scriptSig [] 0).2).stack = a.stack ++ S
  hvalid : Eval.verifyScript params (txContext tx i amt) scriptSig (lockScript f) = .valid

/-- **The bytes accept only what the model accepts** (second stage, the settle with a grandparent). -/
theorem accepts_of_real_settle_gp {P : Prims Bytes} {tx : Tx} {i amt : Nat} {f : Fields} {a : Args}
    {S : List Bytes} {scriptSig : Bytes} {G : Tx} (h : RealSettleGp P tx i amt f a S scriptSig G) :
    Accepts P .fungible (spendOf tx i f a none (some G) none) :=
  simpleMulti_refines_settle_gp P tx i amt f a S scriptSig G h.hwf h.hA h.hty h.hnty h.hpre h.hset h.hnm
    h.hgp h.hgen h.hogp h.hcom2 h.htx h.hamt h.hi h.hnz h.hres h.hgr h.hstack h.hvalid

/-- A real merge commit at its first token input, as `simpleMulti_refines_merge_commit` takes it: this
input's spend and the second token input's (`i'`, `f'`, `a'`), both valid, each with its residuals. That
the second input presents a preimage (`hpre'`) is open question Q8 of `lean/README.md`: the bytes accept a merge
commit whose other input takes the melt branch, and anchor the carried balance only at the settle. -/
structure RealMergeCommit (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args) (S : List Bytes)
    (scriptSig : Bytes) (i' amt' : Nat) (f' : Fields) (a' : Args) (S' : List Bytes) (scriptSig' : Bytes) :
    Prop where
  hwf : WF f
  hA : ArgsWF a
  hwf' : WF f'
  hA' : ArgsWF a'
  hty : SmbType f.ty
  hnty : SmbType a.nty
  hty' : SmbType f'.ty
  hnty' : SmbType a'.nty
  hpre : castToBool a.pre = true
  hpre' : castToBool a'.pre = true
  hset : settledTy f.ty
  hmrg : a.nty = [0x25]
  hidx0 : decode a.inIdx = 0
  hgen : decode f.parent = 0 → settledTy f.ty
  htx : TxWF tx
  hamt : amt < 2 ^ 64
  hi : i < tx.inputs.length
  hi' : i' < tx.inputs.length
  hnz : decode (serOutPoint (inputAt tx i)) ≠ 0
  hdis : serOutPoint (inputAt tx i) ≠ serOutPoint (inputAt tx i')
  hres : Residual P tx i amt f a
  hres' : Residual P tx i' amt' f' a'
  hstack : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust
    (some (lockScript f))) scriptSig [] 0).2).stack = a.stack ++ S
  hvalid : Eval.verifyScript params (txContext tx i amt) scriptSig (lockScript f) = .valid
  hstack' : ((evalScript Eval.opExec (mkEnv params (txContext tx i' amt') params.flags.forkAdjust
    (some (lockScript f'))) scriptSig' [] 0).2).stack = a'.stack ++ S'
  hvalid' : Eval.verifyScript params (txContext tx i' amt') scriptSig' (lockScript f') = .valid

/-- **The bytes accept only what the model accepts** (third stage, the merge commit). -/
theorem accepts_of_real_merge_commit {P : Prims Bytes} {tx : Tx} {i amt : Nat} {f : Fields} {a : Args}
    {S : List Bytes} {scriptSig : Bytes} {i' amt' : Nat} {f' : Fields} {a' : Args} {S' : List Bytes}
    {scriptSig' : Bytes} (h : RealMergeCommit P tx i amt f a S scriptSig i' amt' f' a' S' scriptSig') :
    Accepts P .fungible (spendOf tx i f a
      (some (f', ⟨(inputAt tx i').prevHash, (inputAt tx i').prevIndex⟩)) none none) :=
  simpleMulti_refines_merge_commit P tx i amt f a S scriptSig i' amt' f' a' S' scriptSig' h.hwf h.hA h.hwf'
    h.hA' h.hty h.hnty h.hty' h.hnty' h.hpre h.hpre' h.hset h.hmrg h.hidx0 h.hgen h.htx h.hamt h.hi h.hi'
    h.hnz h.hdis h.hres h.hres' h.hstack h.hvalid h.hstack' h.hvalid'

/-- A real merge settle, as `simpleMulti_refines_merge_settle` takes it, with `G` and `GB` the two rebuilt
ancestors and `GpRealB` the second lineage's link. -/
structure RealMergeSettle (P : Prims Bytes) (tx : Tx) (i amt : Nat) (f : Fields) (a : Args) (S : List Bytes)
    (scriptSig : Bytes) (G GB : Tx) : Prop where
  hwf : WF f
  hA : ArgsWF a
  hty : SmbType f.ty
  hnty : SmbType a.nty
  hpre : castToBool a.pre = true
  hmrg : f.ty = [0x25]
  hgp : decode f.gp ≠ 0
  hgen : decode f.parent = 0 → settledTy f.ty
  htx : TxWF tx
  hamt : amt < 2 ^ 64
  hi : i < tx.inputs.length
  hnz : decode (serOutPoint (inputAt tx i)) ≠ 0
  hres : Residual P tx i amt f a
  hgr : ResidualGp P f a G
  hgb : GpRealB P f a GB
  hstack : ((evalScript Eval.opExec (mkEnv params (txContext tx i amt) params.flags.forkAdjust
    (some (lockScript f))) scriptSig [] 0).2).stack = a.stack ++ S
  hvalid : Eval.verifyScript params (txContext tx i amt) scriptSig (lockScript f) = .valid

/-- **The bytes accept only what the model accepts** (fourth stage, the merge settle). -/
theorem accepts_of_real_merge_settle {P : Prims Bytes} {tx : Tx} {i amt : Nat} {f : Fields} {a : Args}
    {S : List Bytes} {scriptSig : Bytes} {G GB : Tx} (h : RealMergeSettle P tx i amt f a S scriptSig G GB) :
    Accepts P .fungible (spendOf tx i f a none (some G) (some GB)) :=
  simpleMulti_refines_merge_settle P tx i amt f a S scriptSig G GB h.hwf h.hA h.hty h.hnty h.hpre h.hmrg
    h.hgp h.hgen h.htx h.hamt h.hi h.hnz h.hres h.hgr h.hgb h.hstack h.hvalid

/-! ## The consequences, of any spend read from the bytes

Each theorem takes `Accepts` of the spend as the four `accepts_of_*` theorems give it, so it applies to
every stage. -/

/-- **Lemma 1 of the shipped bytes.** The key presented hashes to the owner, the signature verifies over
this transaction's digest, and the flag byte is `0x41`. -/
theorem real_presented {P : Prims Bytes} {tx : Tx} {i : Nat} {f : Fields} {a : Args}
    {other : Option (Fields × Outpoint Bytes)} {ancA ancB : Option Tx}
    (h : Accepts P .fungible (spendOf tx i f a other ancA ancB)) :
    P.h160 a.pk = f.pkh ∧ P.verify a.pk (P.sighash (absTx tx) i) a.sig = true ∧ a.sig.getLast?.getD 0 = 0x41 :=
  t2_presented h

/-- **Theorem 2 of the shipped bytes (ownership).** Under A2 for the owner's key, a valid spend means the
owner signed this very transaction. -/
theorem real_ownership {P : Prims Bytes} {tx : Tx} {i : Nat} {f : Fields} {a : Args}
    {other : Option (Fields × Outpoint Bytes)} {ancA ancB : Option Tx} {pkO : PubKey} {signed : Msg → Prop}
    (hO : P.h160 pkO = f.pkh) (hS : OwnerSecrecy P pkO signed)
    (h : Accepts P .fungible (spendOf tx i f a other ancA ancB)) :
    signed (P.sighash (absTx tx) i) :=
  t2_ownership hO hS h

/-- **Theorem 4's step of the shipped bytes.** Every token output of a valid spend is typed by an edge of
the fungible state machine from the spent token's type. -/
theorem real_state_machine {P : Prims Bytes} {tx : Tx} {i : Nat} {f : Fields} {a : Args}
    {other : Option (Fields × Outpoint Bytes)} {ancA ancB : Option Tx}
    (h : Accepts P .fungible (spendOf tx i f a other ancA ancB)) :
    ∀ t ∈ (absTx tx).tokens, Fam.edge .fungible (tokenOf f).txoType t.txoType :=
  t4_step h

/-- **Theorem 3's step of the shipped bytes.** The value the token outputs carry, plus what a melt
destroys, is the value consumed (a spend with one token input). -/
theorem real_value_conserved {P : Prims Bytes} {tx : Tx} {i : Nat} {f : Fields} {a : Args}
    {ancA ancB : Option Tx} (h : Accepts P .fungible (spendOf tx i f a none ancA ancB)) :
    ((absTx tx).tokens.map Token.value).sum + (if kindOf f a = .melt then (tokenOf f).value else 0) =
      (tokenOf f).value + 0 :=
  Spend.value_conserved h

/-- **Theorem 3's step of the shipped bytes, the merge commit.** The value the token outputs carry is the
value of both tokens consumed. -/
theorem real_value_conserved_merge {P : Prims Bytes} {tx : Tx} {i : Nat} {f : Fields} {a : Args}
    {f' : Fields} {op : Outpoint Bytes} {ancA ancB : Option Tx}
    (h : Accepts P .fungible (spendOf tx i f a (some (f', op)) ancA ancB)) :
    ((absTx tx).tokens.map Token.value).sum + (if kindOf f a = .melt then (tokenOf f).value else 0) =
      (tokenOf f).value + (tokenOf f').value :=
  Spend.value_conserved h

/-- **Theorem 1's step of the shipped bytes.** Every token output of a valid spend carries the spent
token's issuer and names the spent outpoint as its parent: one hop of a lineage is what the covenant wrote
from the token it spent. -/
theorem real_issuer_carried {P : Prims Bytes} {tx : Tx} {i : Nat} {f : Fields} {a : Args}
    {other : Option (Fields × Outpoint Bytes)} {ancA ancB : Option Tx}
    (h : Accepts P .fungible (spendOf tx i f a other ancA ancB)) :
    ∀ t ∈ (absTx tx).tokens, t.issuer = (tokenOf f).issuer ∧
      t.parent = some ⟨(inputAt tx i).prevHash, (inputAt tx i).prevIndex⟩ :=
  t1_step h

/-- **Lemma 5 of the shipped bytes.** A parentless token, the genesis, moves only under the issuer's key:
the key presented is the issuer's. -/
theorem real_genesis_needs_issuer {P : Prims Bytes} {tx : Tx} {i : Nat} {f : Fields} {a : Args}
    {other : Option (Fields × Outpoint Bytes)} {ancA ancB : Option Tx}
    (h : Accepts P .fungible (spendOf tx i f a other ancA ancB)) (hg : (tokenOf f).isGenesis) :
    a.pk = (tokenOf f).issuer :=
  t1_genesis_signer h hg

end BoltProof.Glue.SimpleMulti
