import BoltProof.Bridge.Glue.MinSimple.Spec

/-!
# The `SimpleMultiBOLT` lock as the stack carries it

The fungible family's vocabulary (`lean/README.md`, "The glue"): the eleven lock fields
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

/-- Seventy-five ancestor pieces, `p0` nearest the top of the stack: the two rebuilds
(`src/lib/multi/multiSpend.ts`, `parseAncestorTx`) each read one such record, the first rebuild
the deeper one. -/
structure Pieces75 where
  p0 : Bytes
  p1 : Bytes
  p2 : Bytes
  p3 : Bytes
  p4 : Bytes
  p5 : Bytes
  p6 : Bytes
  p7 : Bytes
  p8 : Bytes
  p9 : Bytes
  p10 : Bytes
  p11 : Bytes
  p12 : Bytes
  p13 : Bytes
  p14 : Bytes
  p15 : Bytes
  p16 : Bytes
  p17 : Bytes
  p18 : Bytes
  p19 : Bytes
  p20 : Bytes
  p21 : Bytes
  p22 : Bytes
  p23 : Bytes
  p24 : Bytes
  p25 : Bytes
  p26 : Bytes
  p27 : Bytes
  p28 : Bytes
  p29 : Bytes
  p30 : Bytes
  p31 : Bytes
  p32 : Bytes
  p33 : Bytes
  p34 : Bytes
  p35 : Bytes
  p36 : Bytes
  p37 : Bytes
  p38 : Bytes
  p39 : Bytes
  p40 : Bytes
  p41 : Bytes
  p42 : Bytes
  p43 : Bytes
  p44 : Bytes
  p45 : Bytes
  p46 : Bytes
  p47 : Bytes
  p48 : Bytes
  p49 : Bytes
  p50 : Bytes
  p51 : Bytes
  p52 : Bytes
  p53 : Bytes
  p54 : Bytes
  p55 : Bytes
  p56 : Bytes
  p57 : Bytes
  p58 : Bytes
  p59 : Bytes
  p60 : Bytes
  p61 : Bytes
  p62 : Bytes
  p63 : Bytes
  p64 : Bytes
  p65 : Bytes
  p66 : Bytes
  p67 : Bytes
  p68 : Bytes
  p69 : Bytes
  p70 : Bytes
  p71 : Bytes
  p72 : Bytes
  p73 : Bytes
  p74 : Bytes

/-- The pieces as the stack holds them, top first. -/
def Pieces75.stack (ps : Pieces75) : List Bytes :=
  [ps.p0, ps.p1, ps.p2, ps.p3, ps.p4, ps.p5, ps.p6, ps.p7, ps.p8, ps.p9, ps.p10, ps.p11, ps.p12, ps.p13, ps.p14, ps.p15, ps.p16, ps.p17, ps.p18, ps.p19, ps.p20, ps.p21, ps.p22, ps.p23, ps.p24, ps.p25, ps.p26, ps.p27, ps.p28, ps.p29, ps.p30, ps.p31, ps.p32, ps.p33, ps.p34, ps.p35, ps.p36, ps.p37, ps.p38, ps.p39, ps.p40, ps.p41, ps.p42, ps.p43, ps.p44, ps.p45, ps.p46, ps.p47, ps.p48, ps.p49, ps.p50, ps.p51, ps.p52, ps.p53, ps.p54, ps.p55, ps.p56, ps.p57, ps.p58, ps.p59, ps.p60, ps.p61, ps.p62, ps.p63, ps.p64, ps.p65, ps.p66, ps.p67, ps.p68, ps.p69, ps.p70, ps.p71, ps.p72, ps.p73, ps.p74]

/-- The unlocking arguments, named as the stack has them: the preimage on top (empty for a melt),
the owner's key and signature, then `inputIndexN`, `nextTxoType`, `nextBalanceCommit`, the two
recipient hashes, the change blob, the funding outpoint, the five interop slots of a merge, and
the 150 ancestor pieces, `psA` above `psB`. -/
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
  psA : Pieces75
  psB : Pieces75

/-- The unlocking arguments as the stack holds them, top first. -/
def Args.stack (a : Args) : List Bytes :=
  [a.pre, a.pk, a.sig, a.inIdx, a.nty, a.nbc, a.pkh2, a.pkh1, a.chg, a.fund, a.i1, a.i2, a.i3, a.i4, a.i5] ++
    (a.psA.stack ++ a.psB.stack)

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
