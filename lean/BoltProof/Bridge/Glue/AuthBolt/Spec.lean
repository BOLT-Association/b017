import BoltProof.Bridge.Glue.MinSimple.Spec

/-!
# What the `AuthBOLT` suffix enforces

The vocabulary of the glue theorem for the identity NFT lock (`lean/GLUE-PLAN.md`, M6), `MinSimpleBOLT`'s with
the differences the bytes make: the unlocking script carries an `authOrMiscData` push below everything else (a
direct push, at most 75 bytes: the guard at suffix 25) and a 27th ancestor piece (the grandparent commit's own
`authOrMiscData`, which leads its rebuilt unlocking script), and the suffix is 1145 bytes. As for `MinSimpleBOLT`: the six
lock fields and the unlocking arguments as the stack carries them, the fields of the sighash
preimage the covenant parses, the outputs it rebuilds, the grandparent transaction it rebuilds,
and the two predicates the soundness theorem concludes:

* `Enforced env f a cs`: every fact the suffix checks on a spend that presents a preimage, as the
  symbolic run of the suffix (`MinSimple/Paths.lean`) derives it, with the lock's own `OP_PUSH_TX`
  block abstracted to "it ran to its end on this preimage" (`PushTxReached`; M4 reads the signature
  check off that run).
* `EnforcedMelt env f a`: the four facts the melt arm checks when no preimage is presented.

`Reached` records that the run passes the two proved fragments (`Gadgets/NftType.lean`,
`Gadgets/NullAncestor.lean`) at their offsets with the stack the fragment lemmas assume. `Ends`
is the shape of the run after the suffix: the owner's `OP_CHECKSIG` result on top.

Every definition here mirrors the byte layout the run produces, and the accessors are
`abbrev`s, so the path theorems close by matching the facts the run leaves (`fact`); the layout facts the reader may want (`scLen` is the `fd` varint at preimage byte 104,
the lock script is six pushes of 21, 21, 2, 37, 37 and 34 bytes followed by the suffix, …) are
in the docstrings.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BoltProof.Glue.AuthBolt

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

/-! ## The stack -/

/-- The six lock pushes (`src/lib/single/singleLock.ts`), named as the stack has them: the last
push, `issuer`, on top. -/
structure Fields where
  pkh : Bytes
  com : Bytes
  ty : Bytes
  parent : Bytes
  gp : Bytes
  issuer : Bytes

/-- The 27 pieces of the grandparent transaction the unlocking script supplies, `p0` nearest the
top of the stack. They are all empty unless the spend rebuilds the grandparent. -/
structure Pieces where
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

/-- The unlocking arguments, named as the stack has them: the sighash preimage `pre` on top (empty
for a melt), then the owner's key and signature, the beneficiary hash, the change output blob, the
funding outpoint and the 26 pieces. -/
structure Args where
  pre : Bytes
  pk : Bytes
  sig : Bytes
  ben : Bytes
  chg : Bytes
  fund : Bytes
  ps : Pieces
  /-- the owner-supplied `authOrMiscData`, the first push of the unlocking script and so the deepest -/
  auth : Bytes

/-- The pieces as the stack holds them. -/
def Pieces.stack (ps : Pieces) : List Bytes :=
  [ps.p0, ps.p1, ps.p2, ps.p3, ps.p4, ps.p5, ps.p6, ps.p7, ps.p8, ps.p9, ps.p10, ps.p11, ps.p12,
    ps.p13, ps.p14, ps.p15, ps.p16, ps.p17, ps.p18, ps.p19, ps.p20, ps.p21, ps.p22, ps.p23, ps.p24,
    ps.p25, ps.p26]

/-- The pieces concatenated, as the null-ancestor check sees them (`OP_CAT` from `p0` upwards). -/
abbrev Pieces.cat (ps : Pieces) : Bytes :=
  ps.p26 ++ (ps.p25 ++ (ps.p24 ++ (ps.p23 ++ (ps.p22 ++ (ps.p21 ++ (ps.p20 ++ (ps.p19 ++ (ps.p18 ++ (ps.p17 ++
    (ps.p16 ++ (ps.p15 ++ (ps.p14 ++ (ps.p13 ++ (ps.p12 ++ (ps.p11 ++ (ps.p10 ++ (ps.p9 ++ (ps.p8 ++
    (ps.p7 ++ (ps.p6 ++ (ps.p5 ++ (ps.p4 ++ (ps.p3 ++ (ps.p2 ++ (ps.p1 ++ ps.p0)))))))))))))))))))))))))

/-- The unlocking arguments as the stack holds them, top first. -/
def Args.stack (a : Args) : List Bytes :=
  [a.pre, a.pk, a.sig, a.ben, a.chg, a.fund] ++ a.ps.stack ++ [a.auth]

/-- The lock fields as the stack holds them when the suffix starts, top first. -/
def Fields.stack (f : Fields) : List Bytes :=
  [f.issuer, f.gp, f.parent, f.ty, f.com, f.pkh]

/-! ## The preimage

The covenant parses the BIP143-style sighash preimage (`nVersion ‖ hashPrevouts ‖ hashSequence ‖
outpoint ‖ scriptCode ‖ value ‖ nSequence ‖ hashOutputs ‖ nLocktime ‖ sighashType`) with the
scriptCode length read as a three-byte `fd` varint at bytes 104–106 (suffix 414–482; the `fd`
byte itself is dropped, not checked). -/

/-- The scriptCode length: the two bytes after the `fd` at byte 104. -/
abbrev scLen (pre : Bytes) : Nat := (decode (List.take 2 (List.drop 105 pre))).toNat
/-- The scriptCode, i.e. the lock script being spent. -/
abbrev sc (pre : Bytes) : Bytes := List.take (scLen pre) (List.drop 107 pre)
abbrev preVersion (pre : Bytes) : Bytes := List.take 4 pre
abbrev preHashPrevouts (pre : Bytes) : Bytes := List.take 32 (List.drop 4 pre)
/-- The outpoint being spent. -/
abbrev preOutpoint (pre : Bytes) : Bytes := List.take 36 (List.drop 68 pre)
/-- The value of the output being spent, 8 bytes after the scriptCode. -/
abbrev preValue (pre : Bytes) : Bytes := List.take 8 (List.drop (107 + scLen pre) pre)
abbrev preHashOutputs (pre : Bytes) : Bytes := List.take 32 (List.drop (107 + scLen pre + 8 + 4) pre)
abbrev preSighashType (pre : Bytes) : Bytes := List.take 1 (List.drop (107 + scLen pre + 8 + 4 + 32 + 4) pre)

/-- The lock script's `parent` push (bytes 44–80 of the scriptCode: `0x24` and 36 bytes). -/
abbrev scParentPush (pre : Bytes) : Bytes := List.take 37 (List.drop 44 (sc pre))
/-- The lock script's `issuer` push (bytes 118–151: `0x21` and 33 bytes). -/
abbrev scIssuerPush (pre : Bytes) : Bytes := List.take 34 (List.drop 118 (sc pre))
/-- The lock script after its six pushes: the covenant suffix, as the preimage carries it. -/
abbrev scSuffix (pre : Bytes) : Bytes := List.drop 152 (sc pre)

/-! ## The outputs the covenant rebuilds -/

/-- The issuer push of the new token (suffix 559–569): the signing key at genesis (`parent = 0`),
the old issuer push otherwise. -/
abbrev issuerPush (f : Fields) (a : Args) : Bytes :=
  if decode f.parent = 0 then 33 :: a.pk else scIssuerPush a.pre

/-- A commit spend's outputs: the settle-typed token (`pkh`, the beneficiary hash as the
commitment, type `0x21`, this outpoint as parent, the old parent as grandparent, the issuer, the
suffix) with the spent value, then the pay-to-proof output `02 b017 88 76 a9 14 <ben> 88 ac`. -/
abbrev commitOuts (f : Fields) (a : Args) : Bytes :=
  preValue a.pre ++ [253, 17, 5] ++ 20 :: (f.pkh ++ 20 :: a.ben ++ [1, 33] ++ 36 :: preOutpoint a.pre ++
    scParentPush a.pre ++ issuerPush f a ++ scSuffix a.pre) ++
  (preValue a.pre ++ [29, 2, 176, 23, 136, 118, 169, 20] ++ a.ben ++ [136, 172])

/-- A settle spend's output: the commit-typed token owned by the committed hash (`com` as the
owner, twenty zero bytes as the commitment, type `0x00`, this outpoint as parent, the old parent
as grandparent, the issuer, the suffix) with the spent value. -/
abbrev settleOuts (f : Fields) (a : Args) : Bytes :=
  preValue a.pre ++ [253, 17, 5] ++ 20 :: (f.com ++ 20 :: List.replicate 20 0 ++ [1, 0] ++
    36 :: preOutpoint a.pre ++ scParentPush a.pre ++ issuerPush f a ++ scSuffix a.pre)

/-- The outputs the covenant requires before the change blob, by the spent token's type. -/
def expectedOuts (f : Fields) (a : Args) : Bytes :=
  if f.ty = [0] then commitOuts f a else settleOuts f a

/-! ## The rebuilt grandparent (suffix 614–965)

When a settle spends a token with a grandparent, the covenant rebuilds the grandparent transaction
from the 26 pieces, with the lock script of its token output and the unlocking script of its
token input filled in from the scriptCode, and checks its hash against `gp`. The widths `w2`,
`w3`, `w4` are the `OP_NUM2BIN` results the covenant computes for the varints inside. -/

/-- The two-byte script length `0x017d` the rebuilt unlocking script reads from the scriptCode. -/
@[simp] theorem decode_7d01 : decode [125, 1] = 381 := by decide

/-- The grandparent's token input's unlocking script, rebuilt: the grandparent commit's own `authOrMiscData` push
(piece 24, its push opcode `w6` the `OP_NUM2BIN` of its length) and 27 empty piece pushes, then as for
`MinSimpleBOLT` with `AuthBOLT`'s preimage and lock lengths (`0x0513`, `0x0511`) and its `OP_PUSH_TX` code from
scriptCode byte 193. -/
abbrev rebuiltScriptSig (a : Args) (w3 w4 w6 : Bytes) : Bytes :=
  w6 ++ a.ps.p24 ++ List.replicate 27 0 ++ (w4 ++ a.ps.p23) ++ (w3 ++ a.ps.p22) ++ 20 :: a.ps.p21 ++
    (encode ↑(List.length a.ps.p20) ++ a.ps.p20) ++ 33 :: a.ps.p19 ++
    76 :: 104 :: (a.ps.p18 ++ 3 :: 253 :: 19 :: 5 :: 2 :: 173 :: 104 :: 77 :: 17 :: 5 :: 20 ::
      (a.ps.p17 ++ 20 :: a.ps.p16 ++ 1 :: a.ps.p15 ++ 36 :: a.ps.p14 ++ 36 :: a.ps.p13 ++
        scIssuerPush a.pre ++ scSuffix a.pre)) ++
    52 :: a.ps.p12 ++ [3, 253, 17, 5] ++
    [85, 121, 85, 122, 85, 122, 85, 121, 85, 121, 126, 126, 126, 126, 84, 122, 82, 122, 84, 122, 84,
      122, 126, 126, 126, 124, 115, 99, 1, 65] ++
    List.take 381 (List.drop 193 (sc a.pre)) ++ [171, 173, 104]

/-- The grandparent transaction, rebuilt: its version (piece 26), the input count, its token input's outpoint
(piece 25) and rebuilt unlocking script, the rest as for `MinSimpleBOLT`. -/
abbrev rebuilt (f : Fields) (a : Args) (w2 w3 w4 w6 : Bytes) : Bytes :=
  a.ps.p26 ++ encode ((if ((List.length a.ps.p23 : Nat) : Int) = 0 then 0 else 1) + 1) ++ a.ps.p25 ++
    253 :: (w2 ++ rebuiltScriptSig a w3 w4 w6) ++ a.ps.p11 ++ a.ps.p10 ++
    (encode ↑(List.length a.ps.p9) ++ a.ps.p9) ++ a.ps.p8 ++
    encode ((if ((List.length a.ps.p1 : Nat) : Int) = 0 then 0 else 1) + 2) ++
    preValue a.pre ++ [253, 17, 5] ++ 20 :: a.ps.p7 ++ 20 :: a.ps.p6 ++ 1 :: a.ps.p5 ++
    36 :: a.ps.p4 ++ 36 :: a.ps.p3 ++ scIssuerPush a.pre ++ scSuffix a.pre ++
    preValue a.pre ++ [29, 2, 176, 23, 136, 118, 169, 20] ++ f.pkh ++ [136, 172] ++
    a.ps.p2 ++ (encode ↑(List.length a.ps.p1) ++ a.ps.p1) ++ a.ps.p0

/-! ## The predicates -/

/-- The lock's own `OP_PUSH_TX` block: suffix bytes 38–422, from `OP_DUP` to `OP_CHECKSIGVERIFY`. -/
def pushTxBlock : Bytes := AuthBolt.c38 ++ (AuthBolt.c159 ++ AuthBolt.c280)

/-- The `OP_PUSH_TX` block ran without failing, in an active arm, with the preimage on top of the
stack (`IsOk`: to its end, or to a top-level `OP_RETURN`, which the block does not contain). -/
def PushTxReached (env : Env) (pre cs : Bytes) : Prop :=
  ∃ (tail : Bytes) (X A : List Bytes) (m : Nat) (C : Cond) (kk : Nat) (r : GOut),
    C.isActive = true ∧ run Eval.opExec env pushTxBlock tail (St (pre :: X) A m C kk cs) = r ∧ r.IsOk

/-- The issuer guard (suffix 9–24): the spend is a genesis (`parent = 0`), or a settle without a
grandparent. -/
def Guard (f : Fields) : Prop := (decode f.gp = 0 ∧ f.ty = [0x21]) ∨ decode f.parent = 0

/-- What the suffix enforces on a spend that presents a preimage. -/
structure Enforced (env : Env) (f : Fields) (a : Args) (cs : Bytes) : Prop where
  /-- the lock's `OP_PUSH_TX` block accepted the preimage -/
  pushTx : PushTxReached env a.pre cs
  /-- `nVersion ≥ 2` (suffix 448–452) -/
  version : 2 ≤ decode (preVersion a.pre)
  /-- the preimage's sighash type is `0x41`, `SIGHASH_ALL | SIGHASH_FORKID` (suffix 444–447) -/
  sighashType : preSighashType a.pre = [0x41]
  /-- the spent output carries exactly one satoshi (suffix 475–481) -/
  value : decode (preValue a.pre) = 1
  /-- the outputs: the token the type selects, the pay-to-proof output of a commit, then the
  change blob, hash to the preimage's `hashOutputs` (suffix 532–612 and 1077–1102) -/
  outputs : Hash.hash256 (expectedOuts f a ++ a.chg) = preHashOutputs a.pre
  /-- a settle of a token with a grandparent rebuilds the grandparent from the pieces and checks
  its hash against `gp`, then `hashPrevouts` against this outpoint, the grandparent's first
  output and the funding outpoint (suffix 614–967) -/
  rebuild : f.ty = [0x21] → decode f.gp ≠ 0 →
    ∃ w2 w3 w4 w6 : Bytes,
      num2bin (encode ↑(List.length a.ps.p24)) 1 = some w6 ∧
      num2bin (encode ↑(List.length a.ps.p23)) 1 = some w4 ∧
      num2bin (encode ↑(List.length a.ps.p22)) 1 = some w3 ∧
      num2bin (encode ↑(List.length (rebuiltScriptSig a w3 w4 w6))) 2 = some w2 ∧
      Hash.hash256 (rebuilt f a w2 w3 w4 w6) = List.take 32 f.gp ∧
      Hash.hash256 (preOutpoint a.pre ++ (Hash.hash256 (rebuilt f a w2 w3 w4 w6) ++ [1, 0, 0, 0]) ++ a.fund) =
        preHashPrevouts a.pre
  /-- otherwise every piece is empty (the null-ancestor check, suffix 969–1075) and `hashPrevouts`
  is this outpoint and the funding outpoint -/
  null : f.ty = [0] ∨ decode f.gp = 0 →
    a.ps.cat = [] ∧ Hash.hash256 (preOutpoint a.pre ++ a.fund) = preHashPrevouts a.pre
  /-- under the guard, the signing key is the issuer (suffix 18–24) -/
  issuer : Guard f → f.issuer = a.pk
  /-- the signing key hashes to the owner (suffix 1120–1124) -/
  owner : Hash.hash160 a.pk = f.pkh
  /-- the owner's signature ends in the sighash byte `0x41` (suffix 1125–1130) -/
  sigType : List.drop (List.length a.sig - 1) a.sig = [0x41]
  sigEnc : Ops.Crypto.checkSignatureEncoding env a.sig = .ok ()
  pkEnc : Ops.Crypto.checkPubKeyEncoding env a.pk = .ok ()
  /-- `authOrMiscData` is a direct push, under 76 bytes (suffix 25–33) -/
  auth : ((a.auth.length : Nat) : Int) < 76

/-- What the melt arm (suffix 1104–1118) enforces when no preimage is presented: the issuer guard,
the owner's key and the signature's sighash byte. Nothing constrains the outputs. -/
structure EnforcedMelt (env : Env) (f : Fields) (a : Args) : Prop where
  issuer : Guard f → f.issuer = a.pk
  owner : Hash.hash160 a.pk = f.pkh
  sigType : List.drop (List.length a.sig - 1) a.sig = [0x41]
  sigEnc : Ops.Crypto.checkSignatureEncoding env a.sig = .ok ()
  pkEnc : Ops.Crypto.checkPubKeyEncoding env a.pk = .ok ()
  auth : ((a.auth.length : Nat) : Int) < 76

/-- The run of `suffix ++ k` passes suffix offset `off` in an active arm with a stack satisfying `P`:
from there, the rest of the suffix and `k` run to the same outcome. -/
def Reaches (env : Env) (off : Nat) (k t : Bytes) (r : GOut) (cs : Bytes) (P : List Bytes → Prop) : Prop :=
  ∃ (S A : List Bytes) (m : Nat) (C : Cond) (kk : Nat),
    run Eval.opExec env (AuthBolt.suffix.drop off ++ k) t (St S A m C kk cs) = r ∧ C.isActive = true ∧ P S

/-- The run passes the two proved fragments where `Gadgets/` places them, with the stack their
lemmas assume: the NFT type selector at 543 (`Gadgets/NftType.lean`) with the type byte at depth
`0x17 = 23`, and the null-ancestor tail at 1094 (`Gadgets/NullAncestor.lean`) with the
concatenated pieces on top. -/
structure Reached (env : Env) (f : Fields) (a : Args) (k t : Bytes) (r : GOut) (cs : Bytes) : Prop where
  typeSel : Reaches env 543 k t r cs (fun S => S.getD 23 [] = f.ty)
  nullTail : f.ty = [0] ∨ decode f.gp = 0 →
    Reaches env 1094 k t r cs (fun S => S.head? = some a.ps.cat)

/-- The owner's `OP_CHECKSIG` result, the top of the stack when the suffix ends. -/
abbrev ownerCheck (env : Env) (a : Args) (cs : Bytes) : Bytes :=
  if env.ctx.checkSig a.sig a.pk (Sighash.cleanupScriptCode cs a.sig true) true = true then [1] else []

/-- The run after the suffix: `k` from the owner's check on top of some stack, the tracker back
to the suffix's entry tracker. -/
def Ends (env : Env) (a : Args) (k t : Bytes) (r : GOut) (C : Cond) (cs : Bytes) : Prop :=
  ∃ (m kk : Nat) (rest alt : List Bytes),
    run Eval.opExec env k t (St (ownerCheck env a cs :: rest) alt m C kk cs) = r

/-! ## Small facts about the guard and the path conditions -/

theorem guard_of_genesis {f : Fields} (hpar : decode f.parent = 0) : Guard f := Or.inr hpar
theorem guard_of_settle_noGp {f : Fields} (hty : f.ty = [0x21]) (hgp : decode f.gp = 0) : Guard f :=
  Or.inl ⟨hgp, hty⟩
theorem not_guard_commit {f : Fields} (hty : f.ty = [0]) (hpar : ¬ decode f.parent = 0) : ¬ Guard f := by
  rintro (⟨_, h⟩ | h)
  · rw [hty] at h; cases h
  · exact hpar h
theorem not_guard_settle {f : Fields} (hpar : ¬ decode f.parent = 0) (hgp : ¬ decode f.gp = 0) : ¬ Guard f := by
  rintro (⟨h, _⟩ | h)
  · exact hgp h
  · exact hpar h
theorem commit_ne_settle {f : Fields} (hty : f.ty = [0]) : f.ty ≠ [0x21] := by rw [hty]; decide
theorem settle_ne_commit {f : Fields} (hty : f.ty = [0x21]) : f.ty ≠ [0] := by rw [hty]; decide
theorem not_null_cond {f : Fields} (hty : f.ty = [0x21]) (hgp : ¬ decode f.gp = 0) :
    ¬ (f.ty = [0] ∨ decode f.gp = 0) := by
  rintro (h | h)
  · rw [hty] at h; cases h
  · exact hgp h

/-! ## Normalising the facts a run leaves

The inversion lemmas state their facts in the opcode's own terms (`castToBool (encode (if _ then 1
else 0))`, `encode (decode _) = [1]`, `(↑n - 1).toNat`, `num2bin _ (decode [26]).toNat`); these
rewrite them into the terms of `Enforced`. -/

theorem encode_eq_one_iff (x : Int) : encode x = [1] ↔ x = 1 := by
  constructor
  · intro h; have := congrArg decode h; rwa [decode_encode, decode_lit 1 (by decide)] at this
  · rintro rfl; rfl

theorem encode_length_eq_nil_iff {α : Type} (L : List α) : encode ↑(List.length L) = [] ↔ L = [] := by
  constructor
  · intro h; have := congrArg decode h; rw [decode_encode, decode_nil] at this
    exact List.length_eq_zero_iff.mp (by exact_mod_cast this)
  · rintro rfl; rfl

theorem num2bin_nil_20 : num2bin [] 20 = some (List.replicate 20 0) := by decide
theorem num2bin_nil_27 : num2bin [] 27 = some (List.replicate 27 0) := by decide

/-- `MinSimple`'s `enforced_norm` for `AuthBOLT` (27 empty pushes): rewrite the facts of a finished run into the terms of `Enforced` (every hypothesis and the goal),
and substitute the widths `OP_NUM2BIN` fixed (`h`, the run itself, is kept out of the substitution). -/
syntax "auth_norm" ident : tactic
macro_rules
  | `(tactic| auth_norm $h:ident) =>
    `(tactic| (revert $h:ident; simp only [decode_lit, Nat.reduceLT, Int.reduceToNat, Int.toNat_natCast, Int.pred_toNat,
          decode_encode, castToBool_encode_ite, decide_eq_true_eq, ge_iff_le, encode_eq_one_iff,
          encode_length_eq_nil_iff, decode_7d01, num2bin_nil_20, num2bin_nil_27, Option.some.injEq] at *; subst_vars; intro $h:ident))

end BoltProof.Glue.AuthBolt
