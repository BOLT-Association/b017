import BoltProof.Bridge.Glue.AuthBolt.Abs
import BoltProof.Bridge.Glue.Refine.Serial

/-!
# The welds: byte facts as transaction facts

Small lemmas between the facts `Enforced` states (`AuthBolt/Spec.lean`), the preimage fields
(`Refine/Serial.lean`) and the model's objects (`AuthBolt/Abs.lean`): the version byte, the
signature's sighash byte, the scriptCode cleanup, the lock's own layout inside the preimage, and
the two output templates the covenant builds, read as serialised outputs of the locks the model
expects.
-/

set_option autoImplicit false

namespace BoltProof.Glue.AuthBolt

open BsvScript BsvScript.Numbers BsvScript.Tx BsvScript.Sighash BoltProof.Glue.Serial
open BoltProof.Bridge.Generated

theorem suffix_length : AuthBolt.suffix.length = 1145 := by decide +kernel

theorem lockOf_length_eq {f : Fields} (hwf : WF f) : (lockOf f).length = 1297 := by
  rw [lockOf_length hwf, suffix_length]

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

theorem scParentPush_of_sc {f : Fields} (hwf : WF f) {pre : Bytes} (hsc : sc pre = lockOf f) :
    scParentPush pre = 36 :: f.parent := by
  simp only [scParentPush, hsc, lockOf_drop_44 hwf, List.take_succ_cons, List.take_left' hwf.parent]

theorem scIssuerPush_of_sc {f : Fields} (hwf : WF f) {pre : Bytes} (hsc : sc pre = lockOf f) :
    scIssuerPush pre = 33 :: f.issuer := by
  simp only [scIssuerPush, hsc, lockOf_drop_118 hwf, List.take_succ_cons, List.take_left' hwf.issuer]

theorem scSuffix_of_sc {f : Fields} (hwf : WF f) {pre : Bytes} (hsc : sc pre = lockOf f) :
    scSuffix pre = AuthBolt.suffix := by
  simp only [scSuffix, hsc, lockOf_drop_152 hwf]

/-! ## The outputs as the model's locks -/

/-- The fields of the token a commit creates (`commitOuts`): the owner stays, the recipient is
committed, the type is `0x21`, the spent outpoint becomes the parent, the parent the grandparent,
and the issuer is the signer at genesis. -/
def commitFields (f : Fields) (a : Args) (inp : TxIn) : Fields :=
  { pkh := f.pkh, com := a.ben, ty := [0x21], parent := serOutPoint inp, gp := f.parent,
    issuer := if decode f.parent = 0 then a.pk else f.issuer }

/-- The fields of the token a settle creates (`settleOuts`): the committed hash owns it, the
commitment is cleared, the type is `0x00`. -/
def settleFields (f : Fields) (a : Args) (inp : TxIn) : Fields :=
  { pkh := f.com, com := List.replicate 20 0, ty := [0], parent := serOutPoint inp, gp := f.parent,
    issuer := if decode f.parent = 0 then a.pk else f.issuer }

/-- The widths the unlocking arguments must carry for the covenant's output templates to be
well-formed locks: the covenant copies the recipient hash and (at genesis) the signing key into
the new token's pushes without checking their widths. -/
structure ArgsWF (a : Args) : Prop where
  ben : a.ben.length = 20
  pk : a.pk.length = 33

theorem commitFields_wf {f : Fields} {a : Args} {inp : TxIn} (hwf : WF f) (ha : ArgsWF a)
    (h32 : inp.prevHash.length = 32) : WF (commitFields f a inp) := by
  refine ⟨hwf.pkh, ha.ben, rfl, ?_, hwf.parent, ?_⟩
  · simp [commitFields, serOutPoint_length, h32]
  · simp only [commitFields]; split_ifs <;> simp [ha.pk, hwf.issuer]

theorem settleFields_wf {f : Fields} {a : Args} {inp : TxIn} (hwf : WF f) (ha : ArgsWF a)
    (h32 : inp.prevHash.length = 32) : WF (settleFields f a inp) := by
  refine ⟨hwf.com, by simp [settleFields], rfl, ?_, hwf.parent, ?_⟩
  · simp [settleFields, serOutPoint_length, h32]
  · simp only [settleFields]; split_ifs <;> simp [ha.pk, hwf.issuer]

theorem compactSize_1297 : compactSize 1297 = [253, 17, 5] := by decide
theorem compactSize_29 : compactSize 29 = [29] := by decide

/-- A commit's outputs are the serialised token output and the serialised pay-to-proof output. -/
theorem commitOuts_eq {f : Fields} {a : Args} (hwf : WF f) (ha : ArgsWF a) {inp : TxIn}
    (h32 : inp.prevHash.length = 32) {amt : Nat}
    (hval : preValue a.pre = le64 amt) (hout : preOutpoint a.pre = serOutPoint inp) (hsc : sc a.pre = lockOf f) :
    commitOuts f a =
      serTxOut ⟨amt, lockOf (commitFields f a inp)⟩ ++ serTxOut ⟨amt, proofScript a.ben⟩ := by
  have hl : (lockOf (commitFields f a inp)).length = 1297 := lockOf_length_eq (commitFields_wf hwf ha h32)
  have hp : (proofScript a.ben).length = 29 := by simp [proofScript, ha.ben]
  simp only [serTxOut, serScript, hl, hp, compactSize_1297, compactSize_29]
  simp only [commitOuts, hval, hout, scParentPush_of_sc hwf hsc, scIssuerPush_of_sc hwf hsc,
    scSuffix_of_sc hwf hsc, issuerPush, lockOf, commitFields, proofScript, List.append_assoc, List.cons_append,
    List.nil_append]
  split_ifs <;> simp

/-- A settle's output is the serialised token output. -/
theorem settleOuts_eq {f : Fields} {a : Args} (hwf : WF f) (ha : ArgsWF a) {inp : TxIn}
    (h32 : inp.prevHash.length = 32) {amt : Nat}
    (hval : preValue a.pre = le64 amt) (hout : preOutpoint a.pre = serOutPoint inp) (hsc : sc a.pre = lockOf f) :
    settleOuts f a = serTxOut ⟨amt, lockOf (settleFields f a inp)⟩ := by
  have hl : (lockOf (settleFields f a inp)).length = 1297 := lockOf_length_eq (settleFields_wf hwf ha h32)
  simp only [serTxOut, serScript, hl, compactSize_1297]
  simp only [settleOuts, hval, hout, scParentPush_of_sc hwf hsc, scIssuerPush_of_sc hwf hsc,
    scSuffix_of_sc hwf hsc, issuerPush, lockOf, settleFields, List.append_assoc, List.cons_append, List.nil_append]
  split_ifs <;> simp

/-- A well-formed lock output is a token output of the model. -/
theorem outOf_lock {g : Fields} (hwf : WF g) (v : Nat) : outOf ⟨v, lockOf g⟩ = .token (tokenOf g) := by
  simp [outOf, decodeLock_lockOf hwf]

/-- A pay-to-proof output is a proof output of the model. -/
theorem outOf_proof {pkh : Bytes} (h : pkh.length = 20) (v : Nat) : outOf ⟨v, proofScript pkh⟩ = .proof pkh := by
  have hd : decodeLock (proofScript pkh) = none := by
    unfold decodeLock
    rw [ite_eq_right_iff.mpr]
    intro hc
    have := hc.1
    simp [proofScript, h, suffix_length] at this
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

end BoltProof.Glue.AuthBolt
