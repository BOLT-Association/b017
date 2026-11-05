import BoltProof.Bridge.Glue.MinSimple.Spec

/-!
# The `SimpleMultiBOLT` lock as the stack carries it

The fungible family's vocabulary (`lean/GLUE-PLAN.md`, M5): the eleven lock fields
(`src/tokens/MultiBOLT.ts`, `templates/SimpleMulti.sx.template.ts`), the unlocking arguments above
the 150 ancestor pieces (the pieces themselves stay abstract until the rebuild is run), the lock's
own `OP_PUSH_TX` block, and `Reaches`, the statement that the run of the suffix passes an offset in
an active arm with a stack satisfying a predicate. The preimage accessors are shared with the NFT
family (`MinSimple/Spec.lean`): the BIP143 layout is the same for every lock.
-/

set_option autoImplicit false

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

/-- The eleven lock pushes (`templates/SimpleMulti.sx.template.ts`, `lock`), in push order; the last push,
`issuer`, is on top of the stack. -/
structure Fields where
  /-- `balance`, 16 bytes. -/
  bal : Bytes
  /-- `balanceCommit`, 16 bytes: the split piece or the merged-in balance a commit carries. -/
  balCommit : Bytes
  /-- `pubKeyHash`: the owner. -/
  pkh : Bytes
  /-- `pubKeyHashCommit`: the recipient a commit names. -/
  com : Bytes
  /-- `pubKeyHashCommit2`: the second recipient of a split. -/
  com2 : Bytes
  /-- `otherGrandparentOutpoint`, 36 bytes: the second lineage of a merge. -/
  ogp : Bytes
  /-- `txoType`, one byte. -/
  ty : Bytes
  /-- `outputIndexN`, one byte. -/
  outIdx : Bytes
  /-- `parentOutpoint`, 36 bytes. -/
  parent : Bytes
  /-- `grandparentOutpoint`, 36 bytes. -/
  gp : Bytes
  /-- `issuerPubKey`, 33 bytes. -/
  issuer : Bytes

/-- The unlocking arguments above the ancestor pieces, named as the stack has them: the preimage on
top (empty for a melt), the owner's key and signature, then `inputIndexN`, `nextTxoType`,
`nextBalanceCommit`, the two recipient hashes, the change blob, the funding outpoint and the five
interop slots of a merge. -/
structure Args where
  pre : Bytes
  pk : Bytes
  sig : Bytes
  inIdx : Bytes
  nty : Bytes
  nbc : Bytes
  pkh2 : Bytes
  pkh1 : Bytes
  chg : Bytes
  fund : Bytes
  i1 : Bytes
  i2 : Bytes
  i3 : Bytes
  i4 : Bytes
  i5 : Bytes

/-- The unlocking arguments as the stack holds them, top first. -/
def Args.stack (a : Args) : List Bytes :=
  [a.pre, a.pk, a.sig, a.inIdx, a.nty, a.nbc, a.pkh2, a.pkh1, a.chg, a.fund, a.i1, a.i2, a.i3, a.i4, a.i5]

/-- The lock fields as the stack holds them when the suffix starts, top first. -/
def Fields.stack (f : Fields) : List Bytes :=
  [f.issuer, f.gp, f.parent, f.outIdx, f.ty, f.ogp, f.com2, f.com, f.pkh, f.balCommit, f.bal]

/-- The lock's own `OP_PUSH_TX` block: suffix bytes 38–422, from `OP_DUP` to `OP_CHECKSIGVERIFY`. -/
def pushTxBlock : Bytes := SimpleMulti.c38 ++ (SimpleMulti.c159 ++ SimpleMulti.c280)

/-- The `OP_PUSH_TX` block ran without failing, in an active arm, with the preimage on top. -/
def PushTxReached (env : Env) (pre cs : Bytes) : Prop :=
  ∃ (tail : Bytes) (X A : List Bytes) (m : Nat) (C : Cond) (kk : Nat) (r : GOut),
    C.isActive = true ∧ run Eval.opExec env pushTxBlock tail (St (pre :: X) A m C kk cs) = r ∧ r.IsOk

/-- The run of `suffix ++ k` passes suffix offset `off` in an active arm with a stack satisfying `P`. -/
def Reaches (env : Env) (off : Nat) (k t : Bytes) (r : GOut) (cs : Bytes) (P : List Bytes → Prop) : Prop :=
  ∃ (S A : List Bytes) (m : Nat) (C : Cond) (kk : Nat),
    run Eval.opExec env (SimpleMulti.suffix.drop off ++ k) t (St S A m C kk cs) = r ∧ C.isActive = true ∧ P S

end BoltProof.Glue.SimpleMulti
