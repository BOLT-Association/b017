import BoltProof.Bridge.Glue.SimpleMulti.Regions
import BoltProof.Bridge.Glue.SimpleMulti.Reaches

/-!
# What the fungible suffix enforces

The vocabulary of the `SimpleMultiBOLT` path theorems, as `MinSimple/Spec.lean` is for the NFT
family: the pushes of the spent lock read off the scriptCode in the preimage, the new token's lock
and the outputs a spend must hash to (`expectedOuts`, by the spent type and the next type), and
the structure `Enforced` listing what a run that presents a preimage establishes. The terms are
`abbrev`s so the path theorems close by matching the facts their runs leave (`fact`), after
`enforced_norm` has put both sides in the same shape.

The types: even `txoType`s (`0x20`, `0x22`, `0x24`) are the settled transfer, split and merge
states, odd ones (`0x21`, `0x23`, `0x25`) the commits. A commit spend (even type, next type odd)
builds the commit token (`com = pkh1`, and for a split `com2 = pkh2` with `balanceCommit = nbc`)
and a tagged pay-to-proof output per recipient; a settle spend (odd type, next type the mode's
settled type) builds the settled token owned by the committed recipient and, when the token has
a grandparent, rebuilds the ancestors from the pieces.
-/

set_option autoImplicit false

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated
open BoltProof.Glue.MinSimple (scLen sc preVersion preHashPrevouts preOutpoint preValue preHashOutputs
  preSighashType Guard encode_eq_one_iff encode_length_eq_nil_iff)

/-! ## The spent lock, as the preimage carries it

The scriptCode is the lock: eleven pushes, `0x10` and the 16-byte balance, `0x10` and the
16-byte `balanceCommit`, three `0x14` and 20-byte hashes (`pkh`, `com`, `com2`), `0x24` and the
36-byte `ogp`, two one-byte pushes (`txoType`, `outputIndexN`), two `0x24` and 36-byte outpoints
(`parent`, `gp`), `0x21` and the 33-byte issuer, then the suffix from byte 246. -/

abbrev scBalPush (pre : Bytes) : Bytes := List.take 17 (sc pre)
abbrev scPkhPush (pre : Bytes) : Bytes := List.take 21 (List.drop 34 (sc pre))
abbrev scComPush (pre : Bytes) : Bytes := List.take 21 (List.drop 55 (sc pre))
abbrev scParentPush (pre : Bytes) : Bytes := List.take 37 (List.drop 138 (sc pre))
abbrev scIssuerPush (pre : Bytes) : Bytes := List.take 34 (List.drop 212 (sc pre))
abbrev scSuffix (pre : Bytes) : Bytes := List.drop 246 (sc pre)

/-- `n` zero bytes: the empty `balanceCommit`, hashes and outpoint of a fresh token, `OP_NUM2BIN`
of `OP_0` in the covenant. -/
abbrev zeros (n : Nat) : Bytes := List.replicate n 0

/-- The new token's index byte: 0 when the input-index argument `inputIndexN` is zero, else 1. The argument is
not tied to the input's position: `hashPrevouts` beginning with this outpoint is what places the token at input 0
(a merge commit's second token input excepted, whose prevouts begin with the other token's outpoint). -/
abbrev inIdxByte (a : Args) : Nat := if decode a.inIdx = 0 then 0 else 1

/-- A fungible lock from its eleven pushes and the suffix. -/
abbrev lockOf (bal balCommit pkh com com2 ogp ty outIdx parent gp issuer suf : Bytes) : Bytes :=
  bal ++ balCommit ++ pkh ++ com ++ com2 ++ ogp ++ ty ++ outIdx ++ parent ++ gp ++ issuer ++ suf

/-- The tagged pay-to-proof output to a hash: the spent value and the 29-byte script
`02 b017 88 76 a9 14 <hash> 88 ac`. -/
abbrev proofOut (pre pkh : Bytes) : Bytes := preValue pre ++ [29, 2, 176, 23, 136, 118, 169, 20] ++ pkh ++ [136, 172]

/-- A token output: the spent value, the lock's length as a `fd` varint, the lock. -/
abbrev tokenOut (pre lock : Bytes) : Bytes := preValue pre ++ [253] ++ encode (lock.length : Int) ++ lock

/-- The commit token a commit spend builds: the old balance, `balanceCommit` zero for a transfer
and `nbc` for a split or a merge, the old owner, `com = pkh1`, `com2` zero or `pkh2` for a split,
`ogp` zero or the other lineage's outpoint `i1` for a merge, the next type, the index byte
(`inIdxByte`), this outpoint as parent, the old parent as grandparent, the issuer, the suffix. -/
abbrev commitLock (a : Args) (balCommit com2 ogp : Bytes) : Bytes :=
  lockOf (scBalPush a.pre) ([16] ++ balCommit) (scPkhPush a.pre) ([20] ++ a.pkh1) ([20] ++ com2) ([36] ++ ogp)
    ([1] ++ a.nty) [1, inIdxByte a] ([36] ++ preOutpoint a.pre) (scParentPush a.pre) (scIssuerPush a.pre)
    (scSuffix a.pre)

/-- The merged token as a merge commit's second token input (`inputIndexN` non-zero) builds it: the other token's
balance (`nbc`) and its own as `balanceCommit`, the other token's owner (`i3`), `com = pkh1`, `com2` zero, its own
parent push as `ogp`, the next type, index 0, the other token's outpoint (`i2`) as parent and its parent (`i1`) as
grandparent, the issuer, the suffix. With honest interop arguments it is the token the first input builds. -/
abbrev mergeLock1 (a : Args) : Bytes :=
  lockOf ([16] ++ a.nbc) (scBalPush a.pre) ([20] ++ a.i3) ([20] ++ a.pkh1) ([20] ++ zeros 20) (scParentPush a.pre)
    ([1] ++ a.nty) [1, 0] ([36] ++ a.i2) ([36] ++ a.i1) (scIssuerPush a.pre) (scSuffix a.pre)

/-- The settled token a settle spend builds: the old balance, `balanceCommit` zero, the committed
recipient as owner, `com`, `com2` and `ogp` zero, the next type, the index byte, this outpoint, the old
parent, the issuer, the suffix. -/
abbrev settleLock (a : Args) : Bytes :=
  lockOf (scBalPush a.pre) ([16] ++ zeros 16) (scComPush a.pre) ([20] ++ zeros 20) ([20] ++ zeros 20) ([36] ++ zeros 36)
    ([1] ++ a.nty) [1, inIdxByte a] ([36] ++ preOutpoint a.pre) (scParentPush a.pre) (scIssuerPush a.pre)
    (scSuffix a.pre)

/-- The outputs a spend must hash to, before the change blob, by the next type: a transfer commit
(`0x21`), a split commit (`0x23`) and a merge commit (`0x25`) are the commit token and a proof
output per recipient (a merge commit's second token input builds the merged token from the interop arguments,
`mergeLock1`); a transfer settle (`0x20`) is the settled token. (The settles' outputs are `Settle.lean`'s.) -/
def expectedOuts (a : Args) : Bytes :=
  if a.nty = [0x21] then tokenOut a.pre (commitLock a (zeros 16) (zeros 20) (zeros 36)) ++ proofOut a.pre a.pkh1
  else if a.nty = [0x23] then
    tokenOut a.pre (commitLock a a.nbc a.pkh2 (zeros 36)) ++ proofOut a.pre a.pkh1 ++ proofOut a.pre a.pkh2
  else if a.nty = [0x25] then
    (if decode a.inIdx = 0 then tokenOut a.pre (commitLock a a.nbc (zeros 20) a.i1) else tokenOut a.pre (mergeLock1 a))
      ++ proofOut a.pre a.pkh1
  else tokenOut a.pre (settleLock a)

/-- The 150 pieces concatenated, as the null-ancestor check sees them (`OP_CAT` from the deepest
piece, `psB.p74`, upwards). -/
abbrev nullCat (a : Args) : Bytes :=
  a.psB.p74 ++ (a.psB.p73 ++ (a.psB.p72 ++ (a.psB.p71 ++ (a.psB.p70 ++ (a.psB.p69 ++ (a.psB.p68 ++ (a.psB.p67 ++ (a.psB.p66 ++ (a.psB.p65 ++ (a.psB.p64 ++ (a.psB.p63 ++ (a.psB.p62 ++ (a.psB.p61 ++ (a.psB.p60 ++ (a.psB.p59 ++ (a.psB.p58 ++ (a.psB.p57 ++ (a.psB.p56 ++ (a.psB.p55 ++ (a.psB.p54 ++ (a.psB.p53 ++ (a.psB.p52 ++ (a.psB.p51 ++ (a.psB.p50 ++ (a.psB.p49 ++ (a.psB.p48 ++ (a.psB.p47 ++ (a.psB.p46 ++ (a.psB.p45 ++ (a.psB.p44 ++ (a.psB.p43 ++ (a.psB.p42 ++ (a.psB.p41 ++ (a.psB.p40 ++ (a.psB.p39 ++ (a.psB.p38 ++ (a.psB.p37 ++ (a.psB.p36 ++ (a.psB.p35 ++ (a.psB.p34 ++ (a.psB.p33 ++ (a.psB.p32 ++ (a.psB.p31 ++ (a.psB.p30 ++ (a.psB.p29 ++ (a.psB.p28 ++ (a.psB.p27 ++ (a.psB.p26 ++ (a.psB.p25 ++ (a.psB.p24 ++ (a.psB.p23 ++ (a.psB.p22 ++ (a.psB.p21 ++ (a.psB.p20 ++ (a.psB.p19 ++ (a.psB.p18 ++ (a.psB.p17 ++ (a.psB.p16 ++ (a.psB.p15 ++ (a.psB.p14 ++ (a.psB.p13 ++ (a.psB.p12 ++ (a.psB.p11 ++ (a.psB.p10 ++ (a.psB.p9 ++ (a.psB.p8 ++ (a.psB.p7 ++ (a.psB.p6 ++ (a.psB.p5 ++ (a.psB.p4 ++ (a.psB.p3 ++ (a.psB.p2 ++ (a.psB.p1 ++ (a.psB.p0 ++ (a.psA.p74 ++ (a.psA.p73 ++ (a.psA.p72 ++ (a.psA.p71 ++ (a.psA.p70 ++ (a.psA.p69 ++ (a.psA.p68 ++ (a.psA.p67 ++ (a.psA.p66 ++ (a.psA.p65 ++ (a.psA.p64 ++ (a.psA.p63 ++ (a.psA.p62 ++ (a.psA.p61 ++ (a.psA.p60 ++ (a.psA.p59 ++ (a.psA.p58 ++ (a.psA.p57 ++ (a.psA.p56 ++ (a.psA.p55 ++ (a.psA.p54 ++ (a.psA.p53 ++ (a.psA.p52 ++ (a.psA.p51 ++ (a.psA.p50 ++ (a.psA.p49 ++ (a.psA.p48 ++ (a.psA.p47 ++ (a.psA.p46 ++ (a.psA.p45 ++ (a.psA.p44 ++ (a.psA.p43 ++ (a.psA.p42 ++ (a.psA.p41 ++ (a.psA.p40 ++ (a.psA.p39 ++ (a.psA.p38 ++ (a.psA.p37 ++ (a.psA.p36 ++ (a.psA.p35 ++ (a.psA.p34 ++ (a.psA.p33 ++ (a.psA.p32 ++ (a.psA.p31 ++ (a.psA.p30 ++ (a.psA.p29 ++ (a.psA.p28 ++ (a.psA.p27 ++ (a.psA.p26 ++ (a.psA.p25 ++ (a.psA.p24 ++ (a.psA.p23 ++ (a.psA.p22 ++ (a.psA.p21 ++ (a.psA.p20 ++ (a.psA.p19 ++ (a.psA.p18 ++ (a.psA.p17 ++ (a.psA.p16 ++ (a.psA.p15 ++ (a.psA.p14 ++ (a.psA.p13 ++ (a.psA.p12 ++ (a.psA.p11 ++ (a.psA.p10 ++ (a.psA.p9 ++ (a.psA.p8 ++ (a.psA.p7 ++ (a.psA.p6 ++ (a.psA.p5 ++ (a.psA.p4 ++ (a.psA.p3 ++ (a.psA.p2 ++ (a.psA.p1 ++ a.psA.p0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The owner's `OP_CHECKSIG` result, the top of the stack when the suffix ends. -/
abbrev ownerCheck (env : Env) (a : Args) (cs : Bytes) : Bytes :=
  if env.ctx.checkSig a.sig a.pk (Sighash.cleanupScriptCode cs a.sig true) true = true then [1] else []

/-- The run after the suffix: `k` from the owner's check on top of some stack, the tracker back
where the suffix found it. -/
def Ends (env : Env) (a : Args) (k t : Bytes) (r : GOut) (C : Cond) (cs : Bytes) : Prop :=
  ∃ (S A : List Bytes) (m kk : Nat), run Eval.opExec env k t (St (ownerCheck env a cs :: S) A m C kk cs) = r

/-- The issuer guard's condition (suffix 0–9): a genesis (`parent = 0`) or no grandparent. -/
def GuardF (f : Fields) : Prop := decode f.parent = 0 ∨ decode f.gp = 0

/-- The outpoints `hashPrevouts` covers before the funding outpoint: this outpoint, and for a merge commit the
other token's outpoint `i2` after it, or before it when this is the second token input (`inputIndexN` non-zero). -/
def prevoutsOf (a : Args) : Bytes :=
  if a.nty = [0x25] then (if decode a.inIdx = 0 then preOutpoint a.pre ++ a.i2 else a.i2 ++ preOutpoint a.pre)
  else preOutpoint a.pre

/-- The bound the balance checks compare against, `2^127 - 1`. -/
abbrev maxBalance : Int := decode maxBalanceBytes

theorem num2bin_nil_16 : num2bin [] 16 = some (zeros 16) := by decide
theorem num2bin_nil_20 : num2bin [] 20 = some (zeros 20) := by decide
theorem num2bin_nil_33 : num2bin [] 33 = some (zeros 33) := by decide
theorem num2bin_nil_36 : num2bin [] 36 = some (zeros 36) := by decide
theorem num2bin_nil_150 : num2bin [] 150 = some (zeros 150) := by decide

/-- What the suffix enforces on a spend that presents a preimage, with the token at input 0 and
no rebuilt ancestor (a commit spend, or a settle of a token without a grandparent). -/
structure Enforced (env : Env) (f : Fields) (a : Args) (cs : Bytes) : Prop where
  /-- the lock's `OP_PUSH_TX` block accepted the preimage -/
  pushTx : PushTxReached env a.pre cs
  /-- `nVersion ≥ 2` (suffix 485–489) -/
  version : 2 ≤ decode (preVersion a.pre)
  /-- the preimage's sighash type is `0x41` (suffix 481–484) -/
  sighashType : preSighashType a.pre = [0x41]
  /-- the spent output carries exactly one satoshi (suffix 665–670) -/
  value : decode (preValue a.pre) = 1
  /-- the balance and `nextBalanceCommit` are between 0 and `2^127 - 1` (suffix 610–631) -/
  balLo : 0 ≤ decode f.bal
  balHi : decode f.bal ≤ maxBalance
  nbcLo : 0 ≤ decode a.nbc
  nbcHi : decode a.nbc ≤ maxBalance
  /-- a split commit keeps a non-negative remainder (suffix 687–696) -/
  splitGuard : a.nty = [0x23] → 0 ≤ decode f.bal - decode a.nbc
  /-- a merge commit keeps the sum within the bound (suffix 672–682) -/
  mergeGuard : a.nty = [0x25] → decode f.bal + decode a.nbc ≤ maxBalance
  /-- the outputs the next type selects, then the change blob, hash to `hashOutputs` -/
  outputs : Hash.hash256 (expectedOuts a ++ a.chg) = preHashOutputs a.pre
  /-- without a rebuilt ancestor every piece is empty (the null-ancestor check, suffix 3899–4651) -/
  null : nullCat a = []
  /-- `hashPrevouts` is this outpoint, for a merge commit the other token's outpoint, and the
  funding outpoint (suffix 4653–4660) -/
  prevouts : Hash.hash256 (prevoutsOf a ++ a.fund) = preHashPrevouts a.pre
  /-- under the guard, the signing key is the issuer and the next type is neither `0x25` nor `0x27`
  (suffix 10–26) -/
  issuer : GuardF f → f.issuer = a.pk ∧ a.nty ≠ [0x25] ∧ a.nty ≠ [0x27]
  /-- the signing key hashes to the owner (suffix 4672–4697) -/
  owner : Hash.hash160 a.pk = f.pkh
  /-- the owner's signature ends in the sighash byte `0x41` (suffix 4661–4671) -/
  sigType : List.drop (List.length a.sig - 1) a.sig = [0x41]
  sigEnc : Ops.Crypto.checkSignatureEncoding env a.sig = .ok ()
  pkEnc : Ops.Crypto.checkPubKeyEncoding env a.pk = .ok ()

/-- Close a goal by a hypothesis that matches it up to the `abbrev`s (reducible transparency only). -/
syntax "factF" : tactic
macro_rules
  | `(tactic| factF) => `(tactic| with_reducible assumption)

/-- Rewrite the facts of a finished run into the terms of `Enforced` (every hypothesis and the goal):
the flags as propositions, the zero widths substituted, the appends right-nested. -/
syntax "enforced_normF" ident : tactic
macro_rules
  | `(tactic| enforced_normF $h:ident) =>
    `(tactic| (revert $h:ident; simp only [decode_lit, Nat.reduceLT, Int.reduceToNat, Int.toNat_natCast, Int.pred_toNat,
          decode_encode, castToBool_encode_ite, decide_eq_true_eq, ge_iff_le, encode_eq_one_iff,
          encode_length_eq_nil_iff, num2bin_nil_16, num2bin_nil_20, num2bin_nil_33, num2bin_nil_36, num2bin_nil_150,
          Option.some.injEq, encode_two, encode_three, encode_four, List.append_assoc, List.cons_append,
          List.nil_append, List.singleton_append,
          -- the rebuild phase's regions, read on the explicit stack: their results and facts, the depth
          -- accessor and the pieces
          rebuildA_stack, rebuildA_fact0, rebuildA_fact1, rebuildA_fact2, rebuildA_fact3, rebuildA_fact4, rebuildA_fact5, rebuildA_fact6, rebuildA_fact7, rebuildA_fact8, rebuildA_fact9, rebuildA_fact10, rebuildA_fact11, rebuildA_fact12, nullArm_stack, nullArm_fact0, rebuildB_0_stack, rebuildB_1_stack, rebuildB_1_fact0, rebuildB_1_fact1, rebuildB_1_fact2, rebuildB_1_fact3, rebuildB_1_fact4, rebuildB_1_fact5, rebuildB_1_fact6, rebuildB_1_fact7, rebuildB_1_fact8, rebuildB_1_fact9, rebuildB_1_fact10, rebuildB_1_fact11, rebuildB_2_stack, rebuildB_2_fact0, rebuildB_2_fact1, rebuildB_2_fact2, rebuildB_2_fact3, rebuildB_2_fact4, rebuildB_2_fact5, rebuildB_2_fact6, rebuildB_2_fact7, rebuildB_2_fact8, rebuildB_2_fact9, rebuildB_2_fact10, rebuildB_2_fact11,
          item, Pieces75.stack, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
          Option.getD_none] at *; subst_vars; intro $h:ident))

end BoltProof.Glue.SimpleMulti
