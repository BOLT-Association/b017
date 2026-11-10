import BoltProof.Bridge.Glue.SerialBolt.Arms

/-!
# What the `SerialBOLT` suffix enforces

The vocabulary of the glue theorem for the serial-number NFT lock (`lean/README.md`, "The glue"), `MinSimpleBOLT`'s with
the differences the bytes make: the lock carries two more pushes below `MinSimpleBOLT`'s six, `genesisOutpoint`
(the mint's outpoint from the first spend on, null before) and `mintData` (the issuer's bytes at genesis, empty
after), so every scriptCode offset past them moves by the `mintData` push's width (`mintW`); every new token is
written with this spend's outpoint as `genesisOutpoint` at genesis and the old one after, and an empty `mintData`;
the unlocking script carries 27 ancestor pieces; and the rebuilt grandparent's token input spent a lock whose
`genesisOutpoint` and `mintData` pushes the rebuild writes from the pieces (`Arms.lean`). As for `MinSimpleBOLT`:
the lock fields and the unlocking arguments as the stack carries them, the fields of the sighash preimage the
covenant parses, the outputs it rebuilds, the grandparent transaction it rebuilds, and the two predicates the
soundness theorem concludes:

* `Enforced env f a cs`: every fact the suffix checks on a spend that presents a preimage, as the symbolic run of
  the suffix (`SerialBolt/Paths/*.lean`) derives it, with the lock's own `OP_PUSH_TX` block abstracted to "it ran to
  its end on this preimage" (`PushTxReached`).
* `EnforcedMelt env f a`: the facts the prologue and the melt arm check when no preimage is presented.

`Reached` records that the run passes the two proved fragments (`Gadgets/NftType.lean`,
`Gadgets/NullAncestor.lean`) at their offsets with the stack the fragment lemmas assume. `Ends` is the shape of the
run after the suffix: the owner's `OP_CHECKSIG` result on top.

Every definition here mirrors the byte layout the run produces, and the accessors are `abbrev`s, so the path
theorems close by matching the facts the run leaves (`fact`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BoltProof.Glue.SerialBolt

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

/-! ## The stack -/

/-- The eight lock pushes, named as the stack has them: the last push, `issuer`, on top. The suffix drops
`genesis` at once (suffix 0–2); the covenant reads it off the scriptCode instead. -/
structure Fields where
  /-- `genesisOutpoint`, the first push: the mint's outpoint from the first spend on (36 bytes) -/
  genesis : Bytes
  /-- `mintData`, the second push: the issuer's bytes on the mint, empty after -/
  mint : Bytes
  pkh : Bytes
  com : Bytes
  ty : Bytes
  parent : Bytes
  gp : Bytes
  issuer : Bytes

/-- The 27 pieces of the grandparent transaction the unlocking script supplies, `p0` nearest the top of the stack.
They are all empty unless the spend rebuilds the grandparent. -/
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
funding outpoint and the 27 pieces. -/
structure Args where
  pre : Bytes
  pk : Bytes
  sig : Bytes
  ben : Bytes
  chg : Bytes
  fund : Bytes
  ps : Pieces

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
  [a.pre, a.pk, a.sig, a.ben, a.chg, a.fund] ++ a.ps.stack

/-- The lock fields as the stack holds them when the suffix starts, top first. -/
def Fields.stack (f : Fields) : List Bytes :=
  [f.issuer, f.gp, f.parent, f.ty, f.com, f.pkh, f.mint, f.genesis]

/-! ## The preimage

The covenant parses the BIP143-style sighash preimage (`nVersion ‖ hashPrevouts ‖ hashSequence ‖
outpoint ‖ scriptCode ‖ value ‖ nSequence ‖ hashOutputs ‖ nLocktime ‖ sighashType`) with the
scriptCode length read as a three-byte `fd` varint at bytes 104–106 (suffix 447–470; the `fd`
byte itself is dropped, not checked). -/

/- The preimage's fields sit where `MinSimpleBOLT`'s do, so the accessors are `MinSimple`'s, and the preimage
lemmas of `Refine/Serial.lean` apply as they are; the scriptCode's pushes do not (`scParentPushS`, …, below). -/
export BoltProof.Glue.MinSimple (scLen sc preVersion preHashPrevouts preOutpoint preValue preHashOutputs
  preSighashType)

/-! ## The lock's own pushes, read off the scriptCode

`SerialBOLT`'s lock is eight pushes, `genesisOutpoint` (37 bytes), `mintData` (`mintW` bytes), `pkh` and `com` (21
each), `txoType` (2), `parent` and `gp` (37 each) and `issuer` (34), then the suffix. The covenant splits the
scriptCode at these widths (suffix 470–515) with the `mintData` width the prologue computes from the length of the
pushed `mintData` (suffix 16–31). -/

/-- The width of the `mintData` push: a direct push (one byte and the data) up to 75 bytes, `OP_PUSHDATA1` (two
bytes and the data) beyond. -/
abbrev mintW (f : Fields) : Nat :=
  (((List.length f.mint : Nat) : Int) + if ((List.length f.mint : Nat) : Int) ≤ 75 then 1 else 2).toNat

/-- The scriptCode's `genesisOutpoint` push. -/
abbrev scGenesisPush (a : Args) : Bytes := List.take 37 (sc a.pre)
/-- The scriptCode's `parent` push. -/
abbrev scParentPushS (f : Fields) (a : Args) : Bytes :=
  List.take 37 (List.drop (37 + mintW f + 21 + 21 + 2) (sc a.pre))
/-- The scriptCode's `issuer` push. -/
abbrev scIssuerPushS (f : Fields) (a : Args) : Bytes :=
  List.take 34 (List.drop (37 + mintW f + 21 + 21 + 2 + 37 + 37) (sc a.pre))
/-- The scriptCode after the eight pushes: the suffix. -/
abbrev scSuffixS (f : Fields) (a : Args) : Bytes :=
  List.drop (37 + mintW f + 21 + 21 + 2 + 37 + 37 + 34) (sc a.pre)

/-! ## The outputs the covenant rebuilds

Every new token carries an empty `mintData` (`OP_0`), so its lock is 1473 bytes (`fd c1 05`). At genesis
(`parent = 0`) the new token's `genesisOutpoint` is this outpoint and its issuer the signing key; after genesis both
are copied from the scriptCode. -/

/-- The pay-to-proof output of a commit: `02 b017 88 76 a9 14 <ben> 88 ac` with the spent value. -/
abbrev proofOut (a : Args) : Bytes := preValue a.pre ++ [29, 2, 176, 23, 136, 118, 169, 20] ++ a.ben ++ [136, 172]

/-- A commit spend's outputs: the commit-typed token (`pkh`, the beneficiary hash as the commitment, type `0x21`,
this outpoint as parent, the old parent as grandparent) with the spent value, then the pay-to-proof output. -/
abbrev commitOuts (f : Fields) (a : Args) : Bytes :=
  if decode f.parent = 0 then
    preValue a.pre ++ [253, 193, 5] ++ 36 :: (preOutpoint a.pre ++ [0] ++ 20 :: (f.pkh ++ 20 :: a.ben ++ [1, 33] ++
      36 :: preOutpoint a.pre ++ scParentPushS f a ++ 33 :: a.pk ++ scSuffixS f a)) ++ proofOut a
  else
    preValue a.pre ++ [253, 193, 5] ++ (scGenesisPush a ++ [0] ++ 20 :: (f.pkh ++ 20 :: a.ben ++ [1, 33] ++
      36 :: preOutpoint a.pre ++ scParentPushS f a ++ scIssuerPushS f a ++ scSuffixS f a)) ++ proofOut a

/-- A settle spend's output: the settle-typed token owned by the committed hash (`com` as the owner, twenty zero
bytes as the commitment, type `0x00`, this outpoint as parent, the old parent as grandparent) with the spent value. -/
abbrev settleOuts (f : Fields) (a : Args) : Bytes :=
  if decode f.parent = 0 then
    preValue a.pre ++ [253, 193, 5] ++ 36 :: (preOutpoint a.pre ++ [0] ++ 20 :: (f.com ++ 20 :: List.replicate 20 0 ++
      [1, 0] ++ 36 :: preOutpoint a.pre ++ scParentPushS f a ++ 33 :: a.pk ++ scSuffixS f a))
  else
    preValue a.pre ++ [253, 193, 5] ++ (scGenesisPush a ++ [0] ++ 20 :: (f.com ++ 20 :: List.replicate 20 0 ++
      [1, 0] ++ 36 :: preOutpoint a.pre ++ scParentPushS f a ++ scIssuerPushS f a ++ scSuffixS f a))

/-- The outputs the covenant requires before the change blob, by the spent token's type. -/
def expectedOuts (f : Fields) (a : Args) : Bytes :=
  if f.ty = [0] then commitOuts f a else settleOuts f a

/-! ## The rebuilt grandparent (suffix 614–1123)

When a settle spends a token with a grandparent, the covenant rebuilds the grandparent transaction (the commit
that created the spent token's parent) from the 27 pieces and checks its hash against `gp`. Its token input's
unlocking script is rebuilt with the preimage that input signed, whose scriptCode is the lock that input spent
(`gpScriptCode`, with the two pushes `Arms.lean` reads); its first output is the token this lock's lineage carries.
The `w`s are the `OP_NUM2BIN` words the covenant computes for the push lengths and varints inside. -/

/-- The lock the grandparent's token input spent: its `genesisOutpoint` push (null when that lock's own parent,
piece 14, is null), its `mintData` push (piece 18), the five pushes of pieces 17–13, and this lock's issuer push
and suffix. -/
abbrev gpScriptCode (f : Fields) (a : Args) (w6 : Bytes) : Bytes :=
  genesisPushOf (encode (decode a.ps.p14)) (scGenesisPush a) ++ mintPushOf a.ps.p18 w6 ++
    20 :: (a.ps.p17 ++ 20 :: a.ps.p16 ++ 1 :: a.ps.p15 ++ 36 :: a.ps.p14 ++ 36 :: a.ps.p13 ++ scIssuerPushS f a ++
      scSuffixS f a)

/-- The grandparent's token input's unlocking script, rebuilt: 27 empty piece pushes, the funding outpoint, the
change blob, the beneficiary hash, the signature and the key (pieces 24–20), the preimage in its three pushes around
the scriptCode (pieces 19 and 12), and the unlocking script's own `OP_PUSH_TX` code from the scriptCode. -/
abbrev rebuiltScriptSig (f : Fields) (a : Args) (w3 w4 w5 w6 w11 w12 : Bytes) : Bytes :=
  List.replicate 27 0 ++ (w12 ++ a.ps.p24) ++ (w11 ++ a.ps.p23) ++ 20 :: a.ps.p22 ++
    (encode ((List.length a.ps.p21 : Nat) : Int) ++ a.ps.p21) ++ 33 :: a.ps.p20 ++
    76 :: 104 :: (a.ps.p19 ++ 3 :: 253 :: (w5 ++ [2, 173, 104] ++ 77 :: (w3 ++ gpScriptCode f a w6))) ++
    52 :: a.ps.p12 ++ 3 :: 253 :: w4 ++
    [85, 121, 85, 122, 85, 122, 85, 121, 85, 121, 126, 126, 126, 126, 84, 122, 82, 122, 84, 122, 84, 122, 126, 126,
      126, 124, 115, 99, 1, 65] ++
    List.take 381 (List.drop (37 + mintW f + 21 + 21 + 2 + 37 + 37 + 34 + 65) (sc a.pre)) ++ [171, 173, 104]

/-- The grandparent transaction, rebuilt: its version (piece 26), the input count, its token input (outpoint piece
25, the rebuilt unlocking script, the sequence and the second input, pieces 11–8), the output count, its token output
(the commit-typed token of pieces 7–3 with this lock's genesis push, issuer and suffix) and its pay-to-proof output
(the spent token's owner), the rest (pieces 2–0). -/
abbrev rebuilt (f : Fields) (a : Args) (w2 w3 w4 w5 w6 w11 w12 : Bytes) : Bytes :=
  a.ps.p26 ++ encode ((if ((List.length a.ps.p24 : Nat) : Int) = 0 then 0 else 1) + 1) ++ a.ps.p25 ++
    253 :: (w2 ++ rebuiltScriptSig f a w3 w4 w5 w6 w11 w12) ++ a.ps.p11 ++ a.ps.p10 ++
    (encode ((List.length a.ps.p9 : Nat) : Int) ++ a.ps.p9) ++ a.ps.p8 ++
    encode ((if ((List.length a.ps.p1 : Nat) : Int) = 0 then 0 else 1) + 2) ++ preValue a.pre ++ [253, 193, 5] ++
    (scGenesisPush a ++ [0]) ++ 20 :: a.ps.p7 ++ 20 :: a.ps.p6 ++ 1 :: a.ps.p5 ++ 36 :: a.ps.p4 ++ 36 :: a.ps.p3 ++
    scIssuerPushS f a ++ scSuffixS f a ++ preValue a.pre ++ [29, 2, 176, 23, 136, 118, 169, 20] ++ f.pkh ++
    [136, 172] ++ a.ps.p2 ++ (encode ((List.length a.ps.p1 : Nat) : Int) ++ a.ps.p1) ++ a.ps.p0

/-! ## The predicates -/

/-- The lock's own `OP_PUSH_TX` block: suffix bytes 62–446, from `OP_DUP` to `OP_CHECKSIGVERIFY`. -/
def pushTxBlock : Bytes := SerialBolt.c62 ++ (SerialBolt.c183 ++ SerialBolt.c304)

/-- The `OP_PUSH_TX` block ran without failing, in an active arm, with the preimage on top of the
stack (`IsOk`: to its end, or to a top-level `OP_RETURN`, which the block does not contain). -/
def PushTxReached (env : Env) (pre cs : Bytes) : Prop :=
  ∃ (tail : Bytes) (X A : List Bytes) (m : Nat) (C : Cond) (kk : Nat) (r : GOut),
    C.isActive = true ∧ run Eval.opExec env pushTxBlock tail (St (pre :: X) A m C kk cs) = r ∧ r.IsOk

/-- The issuer guard (suffix 39–57): the spend is a genesis (`parent = 0`), or a settle without a
grandparent. -/
def Guard (f : Fields) : Prop := (decode f.gp = 0 ∧ f.ty = [0x21]) ∨ decode f.parent = 0

/-- What the suffix enforces on a spend that presents a preimage. -/
structure Enforced (env : Env) (f : Fields) (a : Args) (cs : Bytes) : Prop where
  /-- the lock's `OP_PUSH_TX` block accepted the preimage -/
  pushTx : PushTxReached env a.pre cs
  /-- `nVersion ≥ 2` -/
  version : 2 ≤ decode (preVersion a.pre)
  /-- the preimage's sighash type is `0x41`, `SIGHASH_ALL | SIGHASH_FORKID` -/
  sighashType : preSighashType a.pre = [0x41]
  /-- the spent output carries exactly one satoshi -/
  value : decode (preValue a.pre) = 1
  /-- a `mintData` beyond a direct push is at most 255 bytes (suffix 23–27) -/
  mintLen : ¬ ((List.length f.mint : Nat) : Int) ≤ 75 → ((List.length f.mint : Nat) : Int) ≤ 255
  /-- after genesis the `mintData` is empty (suffix 11–15) -/
  mintEmpty : ¬ decode f.parent = 0 → f.mint = []
  /-- at genesis the scriptCode's `genesisOutpoint` is null (suffix 516–528) -/
  genesisNull : decode f.parent = 0 → scGenesisPush a = 36 :: List.replicate 36 0
  /-- the outputs: the token the type selects, the pay-to-proof output of a commit, then the change blob, hash to
  the preimage's `hashOutputs` -/
  outputs : Hash.hash256 (expectedOuts f a ++ a.chg) = preHashOutputs a.pre
  /-- a settle of a token with a grandparent rebuilds the grandparent from the pieces and checks its hash against
  `gp`, then `hashPrevouts` against this outpoint, the grandparent's first output and the funding outpoint -/
  rebuild : f.ty = [0x21] → decode f.gp ≠ 0 →
    ∃ w2 w3 w4 w5 w6 w11 w12 : Bytes,
      num2bin (encode ((List.length a.ps.p24 : Nat) : Int)) 1 = some w12 ∧
      num2bin (encode ((List.length a.ps.p23 : Nat) : Int)) 1 = some w11 ∧
      (¬ ((List.length a.ps.p18 : Nat) : Int) ≤ 75 →
        num2bin (encode ((List.length a.ps.p18 : Nat) : Int)) (mintLenWidth ((List.length a.ps.p18 : Nat) : Int)) =
          some w6) ∧
      num2bin (encode (((List.length (gpScriptCode f a w6) : Nat) : Int) + 2)) 2 = some w5 ∧
      num2bin (encode ((List.length (gpScriptCode f a w6) : Nat) : Int)) 2 = some w4 ∧
      num2bin (encode ((List.length (gpScriptCode f a w6) : Nat) : Int)) 2 = some w3 ∧
      num2bin (encode ((List.length (rebuiltScriptSig f a w3 w4 w5 w6 w11 w12) : Nat) : Int)) 2 = some w2 ∧
      Hash.hash256 (rebuilt f a w2 w3 w4 w5 w6 w11 w12) = List.take 32 f.gp ∧
      Hash.hash256 (preOutpoint a.pre ++ (Hash.hash256 (rebuilt f a w2 w3 w4 w5 w6 w11 w12) ++ [1, 0, 0, 0]) ++
        a.fund) = preHashPrevouts a.pre
  /-- otherwise every piece is empty (the null-ancestor check) and `hashPrevouts` is this outpoint and the funding
  outpoint -/
  null : f.ty = [0] ∨ decode f.gp = 0 →
    a.ps.cat = [] ∧ Hash.hash256 (preOutpoint a.pre ++ a.fund) = preHashPrevouts a.pre
  /-- under the guard, the signing key is the issuer -/
  issuer : Guard f → f.issuer = a.pk
  /-- the signing key hashes to the owner -/
  owner : Hash.hash160 a.pk = f.pkh
  /-- the owner's signature ends in the sighash byte `0x41` -/
  sigType : List.drop (List.length a.sig - 1) a.sig = [0x41]
  sigEnc : Ops.Crypto.checkSignatureEncoding env a.sig = .ok ()
  pkEnc : Ops.Crypto.checkPubKeyEncoding env a.pk = .ok ()

/-- What the melt arm enforces when no preimage is presented: the prologue's `mintData` checks, the issuer guard,
the owner's key and the signature's sighash byte. Nothing constrains the outputs. -/
structure EnforcedMelt (env : Env) (f : Fields) (a : Args) : Prop where
  mintLen : ¬ ((List.length f.mint : Nat) : Int) ≤ 75 → ((List.length f.mint : Nat) : Int) ≤ 255
  mintEmpty : ¬ decode f.parent = 0 → f.mint = []
  issuer : Guard f → f.issuer = a.pk
  owner : Hash.hash160 a.pk = f.pkh
  sigType : List.drop (List.length a.sig - 1) a.sig = [0x41]
  sigEnc : Ops.Crypto.checkSignatureEncoding env a.sig = .ok ()
  pkEnc : Ops.Crypto.checkPubKeyEncoding env a.pk = .ok ()

/-- The run of `suffix ++ k` passes suffix offset `off` in an active arm with a stack satisfying `P`:
from there, the rest of the suffix and `k` run to the same outcome. -/
def Reaches (env : Env) (off : Nat) (k t : Bytes) (r : GOut) (cs : Bytes) (P : List Bytes → Prop) : Prop :=
  ∃ (S A : List Bytes) (m : Nat) (C : Cond) (kk : Nat),
    run Eval.opExec env (SerialBolt.suffix.drop off ++ k) t (St S A m C kk cs) = r ∧ C.isActive = true ∧ P S

/-- The run passes the two proved fragments where `Gadgets/` places them, with the stack their
lemmas assume: the NFT type selector at 589 (`Gadgets/NftType.lean`) with the type byte at depth
`0x18 = 24`, and the null-ancestor tail at 1232 (`Gadgets/NullAncestor.lean`) with the
concatenated pieces on top. -/
structure Reached (env : Env) (f : Fields) (a : Args) (k t : Bytes) (r : GOut) (cs : Bytes) : Prop where
  typeSel : Reaches env 589 k t r cs (fun S => S.getD 24 [] = f.ty)
  nullTail : f.ty = [0] ∨ decode f.gp = 0 →
    Reaches env 1232 k t r cs (fun S => S.head? = some a.ps.cat)

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

/-- `MinSimple`'s `enforced_norm` for `SerialBOLT`: rewrite the facts of a finished run into the terms of `Enforced`
(every hypothesis and the goal), read the stack items the arms name, and substitute the widths `OP_NUM2BIN` fixed
(`h`, the run itself, is kept out of the substitution). -/
syntax "serial_norm" ident : tactic
macro_rules
  | `(tactic| serial_norm $h:ident) =>
    `(tactic| (revert $h:ident; simp only [decode_lit, Nat.reduceLT, Int.reduceToNat, Int.toNat_natCast, Int.pred_toNat,
          decode_encode, castToBool_encode_ite, decide_eq_true_eq, ge_iff_le, encode_eq_one_iff,
          encode_length_eq_nil_iff, num2bin_nil_20, num2bin_nil_27, num2bin_nil_36, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.getD_some, Option.some.injEq] at *; subst_vars; intro $h:ident))

/-- Two `OP_NUM2BIN` results of the same number at the same width are the same word. -/
theorem num2bin_some_inj {x : Bytes} {n : Nat} {w₁ w₂ : Bytes} (h₁ : num2bin x n = some w₁)
    (h₂ : num2bin x n = some w₂) : w₁ = w₂ :=
  Option.some.inj (h₁.symm.trans h₂)

open Lean Meta Elab Tactic in
/-- One step of `num2bin_dedup`: two hypotheses `num2bin x n = some w₁` and `num2bin x n = some w₂` with distinct
variables `w₁`, `w₂` give `w₁ = w₂`, substituted. -/
private def num2binDedupStep (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let hyps := (← getLCtx).decls.toList.filterMap id |>.filter (fun d => !d.isImplementationDetail)
  for d₁ in hyps do
    let t₁ ← instantiateMVars d₁.type
    let some (_, l₁, r₁) := t₁.eq? | continue
    unless l₁.isAppOfArity ``num2bin 2 && r₁.isAppOfArity ``Option.some 2 && r₁.appArg!.isFVar do continue
    for d₂ in hyps do
      if d₂.fvarId == d₁.fvarId then continue
      let t₂ ← instantiateMVars d₂.type
      let some (_, l₂, r₂) := t₂.eq? | continue
      unless r₂.isAppOfArity ``Option.some 2 && r₂.appArg!.isFVar && r₂.appArg! != r₁.appArg! do continue
      unless l₁ == l₂ do continue
      let pf ← mkAppM ``num2bin_some_inj #[mkFVar d₁.fvarId, mkFVar d₂.fvarId]
      let g₁ ← g.assert `hw (← inferType pf) pf
      let (fv, g₂) ← g₁.intro1
      return some (← subst g₂ fv)
  return none

open Lean Meta Elab Tactic in
/-- Identify the words of every two `OP_NUM2BIN` facts on the same number and width (the rebuild computes the
grandparent's input-lock length word twice), so the facts name one witness. -/
elab "num2bin_dedup" : tactic => do
  let mut g ← getMainGoal
  for _ in [0:20] do
    match ← num2binDedupStep g with
    | some g' => g := g'
    | none => break
  replaceMainGoal [g]

end BoltProof.Glue.SerialBolt
