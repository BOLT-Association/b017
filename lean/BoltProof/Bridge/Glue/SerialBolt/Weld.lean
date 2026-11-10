import BoltProof.Bridge.Glue.SerialBolt.Abs
import BoltProof.Bridge.Glue.Refine.Serial

/-!
# The welds: byte facts as transaction facts

Small lemmas between the facts `Enforced` states (`SerialBolt/Spec.lean`), the preimage fields
(`Refine/Serial.lean`) and the model's objects (`SerialBolt/Abs.lean`), as for `AuthBOLT`: the version
word, the signature's sighash byte, the scriptCode cleanup, the lock's own pushes inside the preimage (past
the variable-width `mintData` push), and the two output templates the covenant builds, read as serialised
outputs of the locks the model expects (every new token's `mintData` empty, its lock 1473 bytes).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace BoltProof.Glue.SerialBolt

open BsvScript BsvScript.Numbers BsvScript.Tx BsvScript.Sighash BoltProof.Glue.Serial
open BoltProof.Bridge.Generated

theorem suffix_length : SerialBolt.suffix.length = 1283 := by decide +kernel

/-- The `mintData` push is at most 257 bytes. -/
theorem mintW_le {f : Fields} (hwf : WF f) : mintW f ≤ 257 := by
  rw [← mintPush_length hwf.mint]
  have := hwf.mint
  unfold mintPush
  split_ifs <;> simp <;> omega

/-- The `mintData` push is at least one byte. -/
theorem mintW_pos {f : Fields} (hwf : WF f) : 1 ≤ mintW f := by
  rw [← mintPush_length hwf.mint]
  unfold mintPush
  split_ifs <;> simp

theorem lockOf_length_eq {f : Fields} (hwf : WF f) : (lockOf f).length = 1472 + mintW f := by
  rw [lockOf_length hwf, suffix_length]; omega

/-- A lock with an empty `mintData` is 1473 bytes. -/
theorem lockOf_length_nil {f : Fields} (hwf : WF f) (hm : f.mint = []) : (lockOf f).length = 1473 := by
  rw [lockOf_length_eq hwf]
  simp [mintW, hm]

theorem hash256_length (x : Bytes) : (Hash.hash256 x).length = 32 := Hash.sha256d_length _

/-! ## Numbers -/

/-- Four bytes as a script number: the top byte's bit 7 is the sign, its low seven bits top the
magnitude. -/
theorem decode_four (b0 b1 b2 b3 : Nat) :
    decode [b0, b1, b2, b3] =
      if 128 ≤ b3 then -(((((b3 % 128) * 256 + b2) * 256 + b1) * 256 + b0 : Nat) : Int)
      else ((((b3 % 128) * 256 + b2) * 256 + b1) * 256 + b0 : Nat) := by
  simp [decode, decodeRev, beNat]

/-- A 32-bit little-endian word as a script number: its value below `2^31`, negative above. -/
theorem decode_le32 (u : Nat) (hu : u < 2 ^ 32) :
    decode (le32 u) = if u < 2 ^ 31 then (u : Int) else -((u - 2 ^ 31 : Nat) : Int) := by
  rw [le32, decode_four]
  have hb : u / 16777216 % 256 = u / 16777216 := Nat.mod_eq_of_lt (by omega)
  rw [hb]
  by_cases h : u < 2 ^ 31
  · rw [ite_eq_right (by omega : ¬ 128 ≤ u / 16777216), ite_eq_left h]
    omega
  · rw [ite_eq_left (by omega : 128 ≤ u / 16777216), ite_eq_right h]
    omega

/-- The version test on the serialised word is the test on the version. -/
theorem two_le_of_decode_serVersion (v : Int) (hv : -2 ^ 31 ≤ v ∧ v < 2 ^ 31)
    (h : 2 ≤ decode (serVersion v)) : 2 ≤ v := by
  unfold serVersion at h
  have hnn : 0 ≤ v % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have hlt : v % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  rw [decode_le32 _ (by omega)] at h
  split_ifs at h with hc
  · omega
  · omega

/-- The sighash byte the covenant checks is the signature's last byte. -/
theorem getLast_eq_of_drop {sig : Bytes} (h : List.drop (sig.length - 1) sig = [0x41]) : sig.getLast? = some 0x41 := by
  rw [List.getLast?_eq_some_iff]
  exact ⟨sig.take (sig.length - 1), by rw [← h, List.take_append_drop]⟩

/-- With the FORKID bit set, the scriptCode is left as it is. -/
theorem cleanupScriptCode_forkid (lock sig : Bytes) (h : sig.getLast? = some 0x41) :
    cleanupScriptCode lock sig true = lock := by
  have h6 : Nat.testBit 65 6 = true := by decide
  have : SigHashType.hasForkId (SigHashType.ofSig sig) = true := by
    simp [SigHashType.ofSig, h, SigHashType.hasForkId, h6]
  simp [cleanupScriptCode, this]

/-! ## The lock inside the preimage -/

theorem scGenesisPush_of_sc {f : Fields} (hwf : WF f) {a : Args} (hsc : sc a.pre = lockOf f) :
    scGenesisPush a = 36 :: f.genesis := by
  simp only [scGenesisPush, hsc]
  rw [show lockOf f = (36 :: f.genesis) ++ (mintPush f.mint ++ pushesOf f) from rfl,
    List.take_left' (by simp [hwf.genesis])]

theorem drop_sc {f : Fields} (hwf : WF f) {a : Args} (hsc : sc a.pre = lockOf f) (n : Nat) :
    List.drop (37 + mintW f + n) (sc a.pre) = (pushesOf f).drop n := by
  rw [hsc, ← List.drop_drop, lockOf_drop hwf]

theorem scParentPushS_of_sc {f : Fields} (hwf : WF f) {a : Args} (hsc : sc a.pre = lockOf f) :
    scParentPushS f a = 36 :: f.parent := by
  simp only [scParentPushS]
  rw [show 37 + mintW f + 21 + 21 + 2 = 37 + mintW f + 44 by omega, drop_sc hwf hsc, pushesOf_drop_44 hwf,
    List.take_succ_cons, List.take_left' hwf.parent]

theorem scIssuerPushS_of_sc {f : Fields} (hwf : WF f) {a : Args} (hsc : sc a.pre = lockOf f) :
    scIssuerPushS f a = 33 :: f.issuer := by
  simp only [scIssuerPushS]
  rw [show 37 + mintW f + 21 + 21 + 2 + 37 + 37 = 37 + mintW f + 118 by omega, drop_sc hwf hsc,
    pushesOf_drop_118 hwf, List.take_succ_cons, List.take_left' hwf.issuer]

theorem scSuffixS_of_sc {f : Fields} (hwf : WF f) {a : Args} (hsc : sc a.pre = lockOf f) :
    scSuffixS f a = SerialBolt.suffix := by
  simp only [scSuffixS]
  rw [show 37 + mintW f + 21 + 21 + 2 + 37 + 37 + 34 = 37 + mintW f + 152 by omega, drop_sc hwf hsc,
    pushesOf_drop_152 hwf]

/-! ## The outputs as the model's locks -/

/-- The fields of the token a commit creates (`commitOuts`): the owner stays, the recipient is committed, the
type is `0x21`, the spent outpoint becomes the parent, the parent the grandparent; at genesis the spent outpoint
becomes the `genesisOutpoint` and the signer the issuer; the `mintData` is empty. -/
def commitFields (f : Fields) (a : Args) (inp : TxIn) : Fields :=
  { genesis := if decode f.parent = 0 then serOutPoint inp else f.genesis, mint := [], pkh := f.pkh,
    com := a.ben, ty := [0x21], parent := serOutPoint inp, gp := f.parent,
    issuer := if decode f.parent = 0 then a.pk else f.issuer }

/-- The fields of the token a settle creates (`settleOuts`): the committed hash owns it, the commitment is
cleared, the type is `0x00`. -/
def settleFields (f : Fields) (a : Args) (inp : TxIn) : Fields :=
  { genesis := if decode f.parent = 0 then serOutPoint inp else f.genesis, mint := [], pkh := f.com,
    com := List.replicate 20 0, ty := [0], parent := serOutPoint inp, gp := f.parent,
    issuer := if decode f.parent = 0 then a.pk else f.issuer }

/-- The widths the unlocking arguments must carry for the covenant's output templates to be well-formed locks:
the covenant copies the recipient hash and (at genesis) the signing key into the new token's pushes without
checking their widths. -/
structure ArgsWF (a : Args) : Prop where
  ben : a.ben.length = 20
  pk : a.pk.length = 33

theorem commitFields_wf {f : Fields} {a : Args} {inp : TxIn} (hwf : WF f) (ha : ArgsWF a)
    (h32 : inp.prevHash.length = 32) : WF (commitFields f a inp) := by
  refine ⟨?_, by simp [commitFields], hwf.pkh, ha.ben, rfl, ?_, hwf.parent, ?_⟩
  · simp only [commitFields]; split_ifs <;> simp [serOutPoint_length, h32, hwf.genesis]
  · simp [commitFields, serOutPoint_length, h32]
  · simp only [commitFields]; split_ifs <;> simp [ha.pk, hwf.issuer]

theorem settleFields_wf {f : Fields} {a : Args} {inp : TxIn} (hwf : WF f) (ha : ArgsWF a)
    (h32 : inp.prevHash.length = 32) : WF (settleFields f a inp) := by
  refine ⟨?_, by simp [settleFields], hwf.com, by simp [settleFields], rfl, ?_, hwf.parent, ?_⟩
  · simp only [settleFields]; split_ifs <;> simp [serOutPoint_length, h32, hwf.genesis]
  · simp [settleFields, serOutPoint_length, h32]
  · simp only [settleFields]; split_ifs <;> simp [ha.pk, hwf.issuer]

theorem compactSize_1473 : compactSize 1473 = [253, 193, 5] := by decide
theorem compactSize_29 : compactSize 29 = [29] := by decide

/-- A commit's outputs are the serialised token output and the serialised pay-to-proof output. -/
theorem commitOuts_eq {f : Fields} {a : Args} (hwf : WF f) (ha : ArgsWF a) {inp : TxIn}
    (h32 : inp.prevHash.length = 32) {amt : Nat}
    (hval : preValue a.pre = le64 amt) (hout : preOutpoint a.pre = serOutPoint inp) (hsc : sc a.pre = lockOf f) :
    commitOuts f a =
      serTxOut ⟨amt, lockOf (commitFields f a inp)⟩ ++ serTxOut ⟨amt, proofScript a.ben⟩ := by
  have hl : (lockOf (commitFields f a inp)).length = 1473 :=
    lockOf_length_nil (commitFields_wf hwf ha h32) rfl
  have hp : (proofScript a.ben).length = 29 := by simp [proofScript, ha.ben]
  simp only [serTxOut, serScript, hl, hp, compactSize_1473, compactSize_29]
  simp only [commitOuts, proofOut, hval, hout, scGenesisPush_of_sc hwf hsc, scParentPushS_of_sc hwf hsc,
    scIssuerPushS_of_sc hwf hsc, scSuffixS_of_sc hwf hsc, lockOf, pushesOf, mintPush, commitFields, proofScript,
    List.append_assoc, List.cons_append, List.nil_append]
  split_ifs <;> simp

/-- A settle's output is the serialised token output. -/
theorem settleOuts_eq {f : Fields} {a : Args} (hwf : WF f) (ha : ArgsWF a) {inp : TxIn}
    (h32 : inp.prevHash.length = 32) {amt : Nat}
    (hval : preValue a.pre = le64 amt) (hout : preOutpoint a.pre = serOutPoint inp) (hsc : sc a.pre = lockOf f) :
    settleOuts f a = serTxOut ⟨amt, lockOf (settleFields f a inp)⟩ := by
  have hl : (lockOf (settleFields f a inp)).length = 1473 :=
    lockOf_length_nil (settleFields_wf hwf ha h32) rfl
  simp only [serTxOut, serScript, hl, compactSize_1473]
  simp only [settleOuts, hval, hout, scGenesisPush_of_sc hwf hsc, scParentPushS_of_sc hwf hsc,
    scIssuerPushS_of_sc hwf hsc, scSuffixS_of_sc hwf hsc, lockOf, pushesOf, mintPush, settleFields,
    List.append_assoc, List.cons_append, List.nil_append]
  split_ifs <;> simp

/-- A well-formed lock output is a token output of the model. -/
theorem outOf_lock {g : Fields} (hwf : WF g) (v : Nat) : outOf ⟨v, lockOf g⟩ = .token (tokenOf g) := by
  simp [outOf, decodeLock_lockOf hwf]

/-- A script that decodes is at least 1473 bytes. -/
theorem decodeLock_none_of_short {s : Bytes} (hs : s.length < 1473) : decodeLock s = none := by
  cases hdl : decodeLock s with
  | none => rfl
  | some g =>
    obtain ⟨hwf, heq⟩ := eq_lockOf_of_decodeLock hdl
    have := congrArg List.length heq
    rw [lockOf_length_eq hwf] at this
    have := mintW_pos hwf
    omega

/-- A pay-to-proof output is a proof output of the model. -/
theorem outOf_proof {pkh : Bytes} (h : pkh.length = 20) (v : Nat) : outOf ⟨v, proofScript pkh⟩ = .proof pkh := by
  have hd : decodeLock (proofScript pkh) = none := decodeLock_none_of_short (by simp [proofScript, h])
  simp only [outOf, hd]
  simp [proofScript, h]

/-! ## The new tokens are the model's -/

/-- The token a commit creates is the model's `commitToken` of the abstracted spend. -/
theorem tokenOf_commitFields (tx : Tx) (i : Nat) {f : Fields} {a : Args}
    (hiss : decode f.parent = 0 → f.issuer = a.pk)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0) (h32 : (inputAt tx i).prevHash.length = 32)
    (hidx : (inputAt tx i).prevIndex < 2 ^ 32) :
    tokenOf (commitFields f a (inputAt tx i)) = (spendOf tx i f a).commitToken := by
  simp only [tokenOf, commitFields, spendOf, Spend.commitToken, outpointOf, hnz, ↓reduceIte,
    (serOutPoint_inj h32 hidx).1, (serOutPoint_inj h32 hidx).2, Mode.commitType]
  split_ifs with hg <;> simp [hiss, hg]

/-- The token a settle creates is the model's `settleToken` of the abstracted spend. -/
theorem tokenOf_settleFields (tx : Tx) (i : Nat) {f : Fields} {a : Args} (hty : f.ty = [0x21])
    (hiss : decode f.parent = 0 → f.issuer = a.pk)
    (hnz : decode (serOutPoint (inputAt tx i)) ≠ 0) (h32 : (inputAt tx i).prevHash.length = 32)
    (hidx : (inputAt tx i).prevIndex < 2 ^ 32) :
    tokenOf (settleFields f a (inputAt tx i)) = (spendOf tx i f a).settleToken .nft 0 := by
  simp only [tokenOf, settleFields, spendOf, Spend.settleToken, outpointOf, hnz, ↓reduceIte,
    (serOutPoint_inj h32 hidx).1, (serOutPoint_inj h32 hidx).2, Fam.settleOf, Token.settledBalance, hty,
    zeroPKH, Fam.modeOfCommitType]
  split_ifs with hg <;> simp [hiss, hg]

end BoltProof.Glue.SerialBolt
