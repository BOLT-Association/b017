import BsvScript.Tx
import BsvScript.Sighash
import BoltProof.Bridge.Glue.MinSimple.Spec

/-!
# Serialisation: what the covenant hashes is what the node parses

The covenant welds its claims to the transaction through hashes of serialised data: the sighash
preimage, the outputs, the outpoints, the rebuilt grandparent. Under second-preimage freedom
(`Refine/MinSimple.lean`) a hash equality is a byte equality, and these lemmas turn the byte
equality into facts about the transaction's fields: the little-endian words and varints round
trip (`leNat_le32`, `readVarInt_compactSize`), an output or an input read back is the output or
input written (`readTxOut_serTxOut`, `readTxIn_serTxIn`), a well-formed transaction decodes to
itself (`decodeTx_serTx`), a serialised output list that starts with an output starts with that
output (`flatten_serTxOut_cons`), and the preimage fields the covenant cuts out of a BIP143
preimage are the transaction's (`preimage_fields`).
-/

set_option autoImplicit false
-- `simp only [Option.bind]` unfolds the monadic binds of the readers by their equation lemmas; the
-- unused-argument linter does not see that use and reports it, so it is off for this file.
set_option linter.unusedSimpArgs false

namespace BoltProof.Glue.Serial

open BsvScript BsvScript.Numbers BsvScript.Tx BsvScript.Sighash

/-! ## Little-endian words -/

theorem leNat_le32 (u : Nat) (hu : u < 2 ^ 32) : leNat (le32 u) = u := by
  simp only [le32, leNat]; omega

theorem leNat_le64 (u : Nat) (hu : u < 2 ^ 64) : leNat (le64 u) = u := by
  simp only [le64, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, leNat, Nat.pow_zero, Nat.div_one]
  omega

theorem readLE_append {n : Nat} {a r : Bytes} (ha : a.length = n) : readLE n (a ++ r) = some (leNat a, r) := by
  simp [readLE, List.take_left' ha, List.drop_left' ha, ha]

theorem readBytes_append {n : Nat} {a r : Bytes} (ha : a.length = n) : readBytes n (a ++ r) = some (a, r) := by
  simp [readBytes, List.take_left' ha, List.drop_left' ha, ha]

theorem readLE_exact {n : Nat} {a : Bytes} (ha : a.length = n) : readLE n a = some (leNat a, []) := by
  simp [readLE, ha, List.take_of_length_le (Nat.le_of_eq ha), List.drop_of_length_le (Nat.le_of_eq ha)]

/-- A signed 32-bit version round trips through its serialised word. -/
theorem toInt32_serVersion (v : Int) (hv : -2 ^ 31 ≤ v ∧ v < 2 ^ 31) : toInt32 (leNat (serVersion v)) = v := by
  unfold serVersion toInt32
  have hnn : 0 ≤ v % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have hlt : v % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  rw [leNat_le32 _ (by omega)]
  by_cases h0 : 0 ≤ v
  · have : v % 2 ^ 32 = v := Int.emod_eq_of_lt h0 (by omega)
    rw [this]
    have : v.toNat < 2 ^ 31 := by omega
    simp only [this, ↓reduceIte, Int.toNat_of_nonneg h0]
  · have h0' : v < 0 := by omega
    have : v % 2 ^ 32 = v + 2 ^ 32 := by omega
    rw [this]
    have h1 : ¬ (v + 2 ^ 32).toNat < 2 ^ 31 := by omega
    simp only [h1, ↓reduceIte]
    rw [Int.toNat_of_nonneg (by omega)]
    omega

/-! ## Varints -/

theorem readVarInt_compactSize (n : Nat) (hn : n < 2 ^ 64) (r : Bytes) :
    readVarInt (compactSize n ++ r) = some (n, r) := by
  unfold compactSize
  by_cases h1 : n < 253
  · simp [readVarInt, h1]
  by_cases h2 : n ≤ 0xffff
  · simp only [h1, ↓reduceIte, h2, List.cons_append, List.nil_append]
    simp [readVarInt, readLE, leNat]
    omega
  by_cases h3 : n ≤ 0xffffffff
  · simp only [h1, ↓reduceIte, h2, h3, List.cons_append, readVarInt]
    rw [readLE_append (le32_length n), leNat_le32 _ (by omega)]
    simp [show ¬ (254 < 253) from by decide, show ¬ (254 = 253) from by decide, show 0x10000 ≤ n from by omega]
  · simp only [h1, ↓reduceIte, h2, h3, List.cons_append, readVarInt]
    rw [readLE_append (le64_length n), leNat_le64 _ hn]
    simp [show ¬ (255 < 253) from by decide, show ¬ (255 = 253) from by decide, show ¬ (255 = 254) from by decide,
      show 0x100000000 ≤ n from by omega]

/-! ## Outputs, inputs, transactions -/

/-- A serialised output read back is the output written. -/
theorem readTxOut_serTxOut (o : TxOut) (hv : o.value < 2 ^ 64) (hs : o.scriptPubKey.length < 2 ^ 64) (r : Bytes) :
    readTxOut (serTxOut o ++ r) = some (o, r) := by
  simp only [serTxOut, serScript, readTxOut, List.append_assoc]
  rw [readLE_append (le64_length _), leNat_le64 _ hv]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [readVarInt_compactSize _ hs]
  simp only [Option.bind]
  rw [readBytes_append rfl]
  rfl

/-- A serialised input read back is the input written. -/
theorem readTxIn_serTxIn (i : TxIn) (h32 : i.prevHash.length = 32) (hidx : i.prevIndex < 2 ^ 32)
    (hseq : i.sequence < 2 ^ 32) (hs : i.scriptSig.length < 2 ^ 64) (r : Bytes) :
    readTxIn (serTxIn i ++ r) = some (i, r) := by
  simp only [serTxIn, serOutPoint, serScript, readTxIn, List.append_assoc]
  rw [readBytes_append h32]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [readLE_append (le32_length _), leNat_le32 _ hidx]
  simp only [Option.bind]
  rw [readVarInt_compactSize _ hs]
  simp only [Option.bind]
  rw [readBytes_append rfl]
  simp only [Option.bind]
  rw [readLE_append (le32_length _), leNat_le32 _ hseq]
  rfl

/-- A serialised list read back, item by item, is the list written. -/
theorem readMany_flatten {α : Type} (ser : α → Bytes) (reader : Bytes → Option (α × Bytes)) :
    ∀ (l : List α) (r : Bytes), (∀ x ∈ l, ∀ r', reader (ser x ++ r') = some (x, r')) →
      readMany reader l.length ((l.map ser).flatten ++ r) = some (l, r)
  | [], r, _ => by simp [readMany]
  | x :: xs, r, h => by
    simp only [List.map_cons, List.flatten_cons, List.length_cons, readMany, List.append_assoc]
    rw [h x (by simp) _]
    simp only [Option.bind_eq_bind, Option.bind]
    rw [readMany_flatten ser reader xs r (fun y hy => h y (by simp [hy]))]
    rfl

/-- A transaction the serialisation round trip holds of: the widths and ranges `decodeTx` reads. -/
structure TxWF (tx : Tx) : Prop where
  version : -2 ^ 31 ≤ tx.version ∧ tx.version < 2 ^ 31
  inputs : ∀ i ∈ tx.inputs,
    i.prevHash.length = 32 ∧ i.prevIndex < 2 ^ 32 ∧ i.sequence < 2 ^ 32 ∧ i.scriptSig.length < 2 ^ 64
  outputs : ∀ o ∈ tx.outputs, o.value < 2 ^ 64 ∧ o.scriptPubKey.length < 2 ^ 64
  nIn : tx.inputs.length < 2 ^ 64
  nOut : tx.outputs.length < 2 ^ 64
  lockTime : tx.lockTime < 2 ^ 32

/-- A well-formed transaction decodes to itself. -/
theorem decodeTx_serTx (tx : Tx) (h : TxWF tx) : decodeTx (serTx tx) = some tx := by
  have hin : ∀ r, readMany readTxIn tx.inputs.length ((tx.inputs.map serTxIn).flatten ++ r) = some (tx.inputs, r) :=
    fun r => readMany_flatten serTxIn readTxIn tx.inputs r
      (fun i hi r' => readTxIn_serTxIn i (h.inputs i hi).1 (h.inputs i hi).2.1 (h.inputs i hi).2.2.1 (h.inputs i hi).2.2.2 r')
  have hout : ∀ r, readMany readTxOut tx.outputs.length ((tx.outputs.map serTxOut).flatten ++ r) = some (tx.outputs, r) :=
    fun r => readMany_flatten serTxOut readTxOut tx.outputs r
      (fun o ho r' => readTxOut_serTxOut o (h.outputs o ho).1 (h.outputs o ho).2 r')
  simp [decodeTx, decodeTxPrefix, serTx, readLE_append (serVersion_length tx.version), toInt32_serVersion _ h.version,
    readVarInt_compactSize _ h.nIn, readVarInt_compactSize _ h.nOut, hin, hout, readLE_exact (le32_length tx.lockTime),
    leNat_le32 _ h.lockTime]

/-! ## Prefix cancellation -/

/-- A serialised output list that starts with a serialised output starts with that output. -/
theorem flatten_serTxOut_cons {os : List TxOut}
    (hwf : ∀ o ∈ os, o.value < 2 ^ 64 ∧ o.scriptPubKey.length < 2 ^ 64) {o : TxOut}
    (ho : o.value < 2 ^ 64 ∧ o.scriptPubKey.length < 2 ^ 64) {rest : Bytes}
    (h : (os.map serTxOut).flatten = serTxOut o ++ rest) :
    ∃ os', os = o :: os' ∧ (os'.map serTxOut).flatten = rest := by
  cases os with
  | nil =>
    simp only [List.map_nil, List.flatten_nil] at h
    have := congrArg List.length h
    simp [serTxOut, le64] at this
    omega
  | cons o1 os' =>
    simp only [List.map_cons, List.flatten_cons] at h
    have h1 := readTxOut_serTxOut o1 (hwf o1 (by simp)).1 (hwf o1 (by simp)).2 ((os'.map serTxOut).flatten)
    rw [h, readTxOut_serTxOut o ho.1 ho.2] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    exact ⟨os', by rw [h1.1], h1.2.symm⟩

/-- A serialised outpoint list that starts with 36 bytes starts with an input serialising to them. -/
theorem flatten_serOutPoint_cons {is : List TxIn} (h32 : ∀ i ∈ is, i.prevHash.length = 32) {p rest : Bytes}
    (hp : p.length = 36) (h : (is.map serOutPoint).flatten = p ++ rest) :
    ∃ i is', is = i :: is' ∧ serOutPoint i = p ∧ (is'.map serOutPoint).flatten = rest := by
  cases is with
  | nil =>
    simp only [List.map_nil, List.flatten_nil] at h
    have := congrArg List.length h
    simp [hp] at this
    omega
  | cons i is' =>
    simp only [List.map_cons, List.flatten_cons] at h
    have := List.append_inj h (by rw [serOutPoint_length, h32 i (by simp), hp])
    exact ⟨i, is', rfl, this.1, this.2⟩

/-- An outpoint's bytes name the input. -/
theorem serOutPoint_inj {i : TxIn} (h32 : i.prevHash.length = 32) (hidx : i.prevIndex < 2 ^ 32) :
    (serOutPoint i).take 32 = i.prevHash ∧ leNat ((serOutPoint i).drop 32) = i.prevIndex := by
  simp only [serOutPoint, List.take_left' h32, List.drop_left' h32, leNat_le32 _ hidx, and_self]

/-! ## The preimage's fields -/

/-- Two bytes below the sign bit are the script number they denote. -/
theorem decode_two (a b : Nat) (hb : b < 128) : decode [a, b] = ((a + 256 * b : Nat) : Int) := by
  simp [decode, decodeRev, beNat, Nat.mod_eq_of_lt hb, Nat.not_le.mpr hb]
  omega

theorem hash256_eq (x : Bytes) : Hash.hash256 x = Hash.sha256d x := rfl
theorem hashPrevouts_length (tx : Tx) : (hashPrevouts tx).length = 32 := Hash.sha256d_length _
theorem hashOutputs_length (tx : Tx) : (hashOutputs tx).length = 32 := Hash.sha256d_length _

/-- `SIGHASH_ALL | SIGHASH_FORKID` hashes every outpoint. -/
theorem bip143Prevouts_all (tx : Tx) : bip143Prevouts tx ⟨0x41⟩ = hashPrevouts tx := by
  have : SigHashType.hasAnyoneCanPay ⟨0x41⟩ = false := by decide
  simp [bip143Prevouts, this]

/-- `SIGHASH_ALL | SIGHASH_FORKID` hashes every output. -/
theorem bip143Outputs_all (tx : Tx) (i : Nat) : bip143Outputs tx i ⟨0x41⟩ = hashOutputs tx := by
  have h1 : SigHashType.baseType ⟨0x41⟩ ≠ SIGHASH_SINGLE := by decide
  have h2 : SigHashType.baseType ⟨0x41⟩ ≠ SIGHASH_NONE := by decide
  simp [bip143Outputs, h1, h2]

theorem serialize_all : SigHashType.serialize ⟨0x41⟩ = [0x41, 0, 0, 0] := by decide

/-- The fields the covenant cuts out of the preimage (`MinSimple/Spec.lean`) are the transaction's,
when the preimage is this spend's BIP143 preimage for `SIGHASH_ALL | SIGHASH_FORKID`, the lock's
length takes a three-byte varint, and the spent outpoint has a 32-byte txid. -/
theorem preimage_fields (lock : Bytes) (hl : 253 ≤ lock.length ∧ lock.length < 32768) (tx : Tx) (i : Nat)
    (amt : Nat) (h32 : (inputAt tx i).prevHash.length = 32) :
    MinSimple.scLen (preimageBIP143 lock tx i ⟨0x41⟩ amt) = lock.length ∧
    MinSimple.sc (preimageBIP143 lock tx i ⟨0x41⟩ amt) = lock ∧
    MinSimple.preVersion (preimageBIP143 lock tx i ⟨0x41⟩ amt) = serVersion tx.version ∧
    MinSimple.preHashPrevouts (preimageBIP143 lock tx i ⟨0x41⟩ amt) = hashPrevouts tx ∧
    MinSimple.preOutpoint (preimageBIP143 lock tx i ⟨0x41⟩ amt) = serOutPoint (inputAt tx i) ∧
    MinSimple.preValue (preimageBIP143 lock tx i ⟨0x41⟩ amt) = le64 amt ∧
    MinSimple.preHashOutputs (preimageBIP143 lock tx i ⟨0x41⟩ amt) = hashOutputs tx ∧
    MinSimple.preSighashType (preimageBIP143 lock tx i ⟨0x41⟩ amt) = [0x41] := by
  have hcs : compactSize lock.length = [253] ++ [lock.length % 256, lock.length / 256 % 256] := by
    simp only [compactSize, Nat.not_lt.mpr hl.1, ↓reduceIte, show lock.length ≤ 0xffff from by omega]; rfl
  have hpre : preimageBIP143 lock tx i ⟨0x41⟩ amt = serVersion tx.version ++ (hashPrevouts tx ++ (bip143Sequence tx ⟨0x41⟩ ++ (serOutPoint (inputAt tx i) ++ ([253] ++ ([lock.length % 256, lock.length / 256 % 256] ++ (lock ++ (le64 amt ++ (le32 (inputAt tx i).sequence ++ (hashOutputs tx ++ (le32 tx.lockTime ++ ([0x41, 0, 0, 0]))))))))))) := by
    simp only [preimageBIP143, serScript, hcs, bip143Prevouts_all, bip143Outputs_all, serialize_all,
      List.append_assoc]
  have e : ∀ (l r : Bytes) (n : Nat), l.length = n → (l ++ r).drop n = r := fun l r n hl => List.drop_left' hl
  have t : ∀ (l r : Bytes) (n : Nat), l.length = n → (l ++ r).take n = l := fun l r n hl => List.take_left' hl
  have h36 : (serOutPoint (inputAt tx i)).length = 36 := by rw [serOutPoint_length, h32]
  have d4 : (preimageBIP143 lock tx i ⟨0x41⟩ amt).drop 4 = hashPrevouts tx ++ (bip143Sequence tx ⟨0x41⟩ ++ (serOutPoint (inputAt tx i) ++ ([253] ++ ([lock.length % 256, lock.length / 256 % 256] ++ (lock ++ (le64 amt ++ (le32 (inputAt tx i).sequence ++ (hashOutputs tx ++ (le32 tx.lockTime ++ ([0x41, 0, 0, 0])))))))))) := by
    rw [hpre, e _ _ _ (serVersion_length _)]
  have d36 : (preimageBIP143 lock tx i ⟨0x41⟩ amt).drop 36 = bip143Sequence tx ⟨0x41⟩ ++ (serOutPoint (inputAt tx i) ++ ([253] ++ ([lock.length % 256, lock.length / 256 % 256] ++ (lock ++ (le64 amt ++ (le32 (inputAt tx i).sequence ++ (hashOutputs tx ++ (le32 tx.lockTime ++ ([0x41, 0, 0, 0]))))))))) := by
    rw [show (36 : Nat) = 4 + 32 from rfl, ← List.drop_drop, d4, e _ _ _ (hashPrevouts_length _)]
  have d68 : (preimageBIP143 lock tx i ⟨0x41⟩ amt).drop 68 = serOutPoint (inputAt tx i) ++ ([253] ++ ([lock.length % 256, lock.length / 256 % 256] ++ (lock ++ (le64 amt ++ (le32 (inputAt tx i).sequence ++ (hashOutputs tx ++ (le32 tx.lockTime ++ ([0x41, 0, 0, 0])))))))) := by
    rw [show (68 : Nat) = 36 + 32 from rfl, ← List.drop_drop, d36, e _ _ _ (bip143Sequence_length _ _)]
  have d104 : (preimageBIP143 lock tx i ⟨0x41⟩ amt).drop 104 = [253] ++ ([lock.length % 256, lock.length / 256 % 256] ++ (lock ++ (le64 amt ++ (le32 (inputAt tx i).sequence ++ (hashOutputs tx ++ (le32 tx.lockTime ++ ([0x41, 0, 0, 0]))))))) := by
    rw [show (104 : Nat) = 68 + 36 from rfl, ← List.drop_drop, d68, e _ _ _ h36]
  have d105 : (preimageBIP143 lock tx i ⟨0x41⟩ amt).drop 105 = [lock.length % 256, lock.length / 256 % 256] ++ (lock ++ (le64 amt ++ (le32 (inputAt tx i).sequence ++ (hashOutputs tx ++ (le32 tx.lockTime ++ ([0x41, 0, 0, 0])))))) := by
    rw [show (105 : Nat) = 104 + 1 from rfl, ← List.drop_drop, d104, e [253] _ 1 rfl]
  have d107 : (preimageBIP143 lock tx i ⟨0x41⟩ amt).drop 107 = lock ++ (le64 amt ++ (le32 (inputAt tx i).sequence ++ (hashOutputs tx ++ (le32 tx.lockTime ++ ([0x41, 0, 0, 0]))))) := by
    rw [show (107 : Nat) = 105 + 2 from rfl, ← List.drop_drop, d105, e [lock.length % 256, lock.length / 256 % 256] _ 2 rfl]
  have hlen : MinSimple.scLen (preimageBIP143 lock tx i ⟨0x41⟩ amt) = lock.length := by
    simp only [MinSimple.scLen, d105, t [lock.length % 256, lock.length / 256 % 256] _ 2 rfl]
    rw [decode_two _ _ (by omega)]
    simp only [Int.toNat_natCast]
    omega
  have dL : (preimageBIP143 lock tx i ⟨0x41⟩ amt).drop (107 + lock.length) = le64 amt ++ (le32 (inputAt tx i).sequence ++ (hashOutputs tx ++ (le32 tx.lockTime ++ ([0x41, 0, 0, 0])))) := by
    rw [← List.drop_drop, d107, e lock _ lock.length rfl]
  have dL12 : (preimageBIP143 lock tx i ⟨0x41⟩ amt).drop (107 + lock.length + 8 + 4) = hashOutputs tx ++ (le32 tx.lockTime ++ ([0x41, 0, 0, 0])) := by
    rw [← List.drop_drop, ← List.drop_drop, dL, e _ _ _ (le64_length _), e _ _ _ (le32_length _)]
  have dL48 : (preimageBIP143 lock tx i ⟨0x41⟩ amt).drop (107 + lock.length + 8 + 4 + 32 + 4) = [0x41, 0, 0, 0] := by
    rw [← List.drop_drop, ← List.drop_drop, dL12, e _ _ _ (hashOutputs_length _), e _ _ _ (le32_length _)]
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [MinSimple.sc, hlen, d107, t lock _ lock.length rfl]
  · simp only [MinSimple.preVersion, hpre, t _ _ _ (serVersion_length _)]
  · simp only [MinSimple.preHashPrevouts, d4, t _ _ _ (hashPrevouts_length _)]
  · simp only [MinSimple.preOutpoint, d68, t _ _ _ h36]
  · simp only [MinSimple.preValue, hlen, dL, t _ _ _ (le64_length _)]
  · simp only [MinSimple.preHashOutputs, hlen, dL12, t _ _ _ (hashOutputs_length _)]
  · simp only [MinSimple.preSighashType, hlen, dL48]; rfl

end BoltProof.Glue.Serial
