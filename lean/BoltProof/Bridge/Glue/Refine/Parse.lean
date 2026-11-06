import BoltProof.Bridge.Glue.Refine.Serial

/-!
# Parsing laid-out bytes

The covenant rebuilds an ancestor transaction from pieces and hashes the result. Under
second-preimage freedom the rebuilt bytes are the ancestor's serialisation, so the ancestor is what
`decodeTx` reads from them. These lemmas read a byte string laid out field by field (an outpoint, a
varint, a script, a sequence; a value, a varint, a script; the version, the counts, the lock time)
with only the widths each reader consumes, and return the fields as the pieces themselves
(`inOfBytes`, `outOfBytes`), so no byte-range condition on the pieces is needed. A varint is any
prefix that reads as the length that follows (`VarIntOf`), which covers the covenant's own encodings
(`OP_NUM2BIN` words after `0xfd`) as well as `compactSize`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace BoltProof.Glue.Serial

open BsvScript BsvScript.Numbers BsvScript.Tx BsvScript.Sighash

/-- An input read off its bytes: the 36-byte outpoint, the unlocking script, the 4-byte sequence. -/
def inOfBytes (op sc sq : Bytes) : TxIn :=
  { prevHash := op.take 32, prevIndex := leNat (op.drop 32), scriptSig := sc, sequence := leNat sq }

/-- An output read off its bytes: the 8-byte value and the locking script. -/
def outOfBytes (v sc : Bytes) : TxOut := { value := leNat v, scriptPubKey := sc }

/-- A prefix that `readVarInt` reads as `n`, whatever follows. -/
def VarIntOf (vi : Bytes) (n : Nat) : Prop := ∀ r, readVarInt (vi ++ r) = some (n, r)

theorem varIntOf_small {n : Nat} (h : n < 253) : VarIntOf [n] n := by
  intro r; simp [readVarInt, h]

theorem varIntOf_fd {a b : Nat} (h : 253 ≤ a + 256 * b) : VarIntOf [253, a, b] (a + 256 * b) := by
  intro r
  simp only [List.cons_append, List.nil_append, readVarInt, show ¬ (253 < 253) from by decide, ↓reduceIte]
  rw [show a :: b :: r = [a, b] ++ r from rfl, readLE_append (n := 2) rfl]
  simp [leNat, h]

theorem varIntOf_compactSize (n : Nat) (hn : n < 2 ^ 64) : VarIntOf (compactSize n) n :=
  fun r => readVarInt_compactSize n hn r

/-- The covenant's long-script varint: `0xfd` and the low two bytes of the length's 3-byte `OP_NUM2BIN` word. -/
theorem varIntOf_num2bin3 {n : Nat} {w : Bytes} (h : num2bin (encode (n : Int)) (decode (encode 3)).toNat = some w)
    (hlo : 253 ≤ n) (hhi : n < 65536) :
    VarIntOf (253 :: List.take (((List.length w : Nat) : Int) - 1).toNat w) n := by
  rw [decode_encode] at h
  have hl := num2bin_length _ _ _ h
  have hd := num2bin_decode _ _ _ h
  rw [decode_encode] at hd
  match w, hl with
  | [b0, b1, b2], _ =>
    have hn : n = b0 + 256 * b1 := by
      simp only [decode, decodeRev, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        beNat, List.foldl] at hd
      split_ifs at hd with hs
      · omega
      · omega
    have hv := varIntOf_fd (a := b0) (b := b1) (by omega)
    simpa [← hn] using hv

/-- A short script's length pushed as a script number is its varint. -/
theorem varIntOf_encode_small {n : Nat} (h1 : 1 ≤ n) (h2 : n < 128) : VarIntOf (encode (n : Int)) n := by
  have he : encode (n : Int) = [n] := by
    rw [encode_ofNat n (by omega)]
    have hm : magBytes n = [n] := by
      unfold magBytes
      obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [hk]
      simp only [magBytesFuel]
      have h0 : (k + 1) / 256 = 0 := by omega
      have h1' : (k + 1) % 256 = k + 1 := by omega
      have hz : magBytesFuel k 0 = [] := by cases k <;> simp [magBytesFuel]
      simp [h0, h1', hz]
    rw [hm]
    simp [signTopRev, show ¬ (128 ≤ n) from by omega]
  rw [he]; exact varIntOf_small (by omega)

/-- Equal script numbers of two lengths are equal lengths. -/
theorem len_of_encode_eq {l k : Nat} (h : encode (l : Int) = encode (k : Int)) : l = k := by
  have := congrArg decode h
  rw [decode_encode, decode_encode] at this
  exact_mod_cast this

/-- An input laid out as its fields reads back as `inOfBytes`. -/
theorem readTxIn_bytes {op vi sc sq r : Bytes} (hop : op.length = 36) (hvi : VarIntOf vi sc.length)
    (hsq : sq.length = 4) :
    readTxIn (op ++ (vi ++ (sc ++ (sq ++ r)))) = some (inOfBytes op sc sq, r) := by
  have hsplit : op = op.take 32 ++ op.drop 32 := (List.take_append_drop 32 op).symm
  have h32 : (op.take 32).length = 32 := by simp [hop]
  have h4 : (op.drop 32).length = 4 := by simp [hop]
  unfold readTxIn
  rw [hsplit, List.append_assoc, readBytes_append h32]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [readLE_append h4]
  simp only [Option.bind]
  rw [hvi]
  simp only [Option.bind]
  rw [readBytes_append rfl]
  simp only [Option.bind]
  rw [readLE_append hsq]
  simp only [inOfBytes, ← hsplit]
  rfl

/-- An output laid out as its fields reads back as `outOfBytes`. -/
theorem readTxOut_bytes {v vi sc r : Bytes} (hv : v.length = 8) (hvi : VarIntOf vi sc.length) :
    readTxOut (v ++ (vi ++ (sc ++ r))) = some (outOfBytes v sc, r) := by
  unfold readTxOut
  rw [readLE_append hv]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hvi]
  simp only [Option.bind]
  rw [readBytes_append rfl]
  rfl

/-! ## Lists of items -/

/-- The bytes `b` read as the items `xs`, whatever follows. -/
def ReadsAs {α : Type} (reader : Bytes → Option (α × Bytes)) (n : Nat) (b : Bytes) (xs : List α) : Prop :=
  ∀ r, readMany reader n (b ++ r) = some (xs, r)

theorem readsAs_nil {α : Type} (reader : Bytes → Option (α × Bytes)) : ReadsAs reader 0 [] [] := by
  intro r; simp [readMany]

theorem readsAs_cons {α : Type} {reader : Bytes → Option (α × Bytes)} {n : Nat} {b bs : Bytes} {x : α}
    {xs : List α} (h1 : ∀ r, reader (b ++ r) = some (x, r)) (h : ReadsAs reader n bs xs) :
    ReadsAs reader (n + 1) (b ++ bs) (x :: xs) := by
  intro r
  simp only [readMany, List.append_assoc]
  rw [h1]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [h r]
  rfl

theorem readsAs_one {α : Type} {reader : Bytes → Option (α × Bytes)} {b : Bytes} {x : α}
    (h1 : ∀ r, reader (b ++ r) = some (x, r)) : ReadsAs reader 1 b [x] := by
  have h := readsAs_cons h1 (readsAs_nil reader)
  rwa [List.append_nil] at h

/-! ## Transactions -/

/-- A transaction laid out as its fields reads back as those fields. -/
theorem decodeTx_bytes {ver vin ib vout ob lt : Bytes} {nIn nOut : Nat} {ins : List TxIn} {outs : List TxOut}
    (hver : ver.length = 4) (hvin : VarIntOf vin nIn) (hins : ReadsAs readTxIn nIn ib ins)
    (hvout : VarIntOf vout nOut) (houts : ReadsAs readTxOut nOut ob outs) (hlt : lt.length = 4) :
    decodeTx (ver ++ (vin ++ (ib ++ (vout ++ (ob ++ lt))))) =
      some { version := toInt32 (leNat ver), inputs := ins, outputs := outs, lockTime := leNat lt } := by
  unfold decodeTx decodeTxPrefix
  rw [readLE_append hver]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hvin]
  simp only [Option.bind]
  rw [hins]
  simp only [Option.bind]
  rw [hvout]
  simp only [Option.bind]
  rw [houts]
  simp only [Option.bind]
  rw [readLE_exact hlt]
  rfl

/-- Bytes that serialise a well-formed transaction and read as another transaction name that one. -/
theorem eq_of_serTx {G G' : Tx} {X : Bytes} (hG : TxWF G) (hX : X = serTx G) (hd : decodeTx X = some G') :
    G = G' := by
  rw [hX, decodeTx_serTx G hG] at hd
  exact Option.some.inj hd

end BoltProof.Glue.Serial
