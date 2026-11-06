import BoltProof.Bridge.Glue.SimpleMulti.Rebuilt
import BoltProof.Bridge.Glue.SimpleMulti.Weld

/-!
# The rebuilt grandparent's token and the balance anchor

The first rebuild writes the grandparent's commit token as the pieces at depths 142–151 followed by the
spend's own issuer push and suffix (`lkA`). With the pieces at their push widths (`LockWidthsA`) that is
the fungible lock of `gpFieldsA` (`lkA_eq`), so the parsed grandparent's first output is that token, and
its other two outputs, being short, are not tokens (`gpTxA0_token`). The anchor the run checks
(`AnchorOK`, suffix 2660) is then the model's `settledBalance` of that token at the index the unlock
argument names, one below it (`anchorOK_settled`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Numbers BsvScript.Tx BsvScript.Sighash
open BoltProof.Glue.Serial
open BoltProof.Bridge.Generated

/-- The grandparent token's fields as the first rebuild's pieces name them, with the spend's own issuer. -/
def gpFieldsA (T : List Bytes) (issuer : Bytes) : Fields :=
  { bal := item T 151, balCommit := item T 150, pkh := item T 149, com := item T 148, com2 := item T 147,
    ogp := item T 146, ty := item T 145, outIdx := item T 144, parent := item T 143, gp := item T 142,
    issuer := issuer }

/-- The grandparent token's pieces at their push widths. -/
structure LockWidthsA (T : List Bytes) : Prop where
  bal : (item T 151).length = 16
  balCommit : (item T 150).length = 16
  pkh : (item T 149).length = 20
  com : (item T 148).length = 20
  com2 : (item T 147).length = 20
  ogp : (item T 146).length = 36
  ty : (item T 145).length = 1
  outIdx : (item T 144).length = 1
  parent : (item T 143).length = 36
  gp : (item T 142).length = 36

theorem gpFieldsA_wf {T : List Bytes} {issuer : Bytes} (hw : LockWidthsA T) (hi : issuer.length = 33) :
    WF (gpFieldsA T issuer) :=
  ⟨hw.bal, hw.balCommit, hw.pkh, hw.com, hw.com2, hw.ogp, hw.ty, hw.outIdx, hw.parent, hw.gp, hi⟩

/-- The rebuilt token output's script is the fungible lock of the pieces. -/
theorem lkA_eq {T : List Bytes} {issuer : Bytes} (hw : LockWidthsA T) (h15 : item T 15 = 33 :: issuer)
    (h14 : item T 14 = SimpleMulti.suffix) : lkA T = lockScript (gpFieldsA T issuer) := by
  have hidx : encode (((item T 144).length : Nat) : Int) = [1] := by rw [hw.outIdx]; decide
  simp only [lkA, lockScript, gpFieldsA, optPush_of_width hidx, h15, h14, List.append_assoc, List.cons_append,
    List.nil_append]

/-- A script shorter than the lock is no token. -/
theorem decodeLock_short {s : Bytes} (h : s.length < 4946) : decodeLock s = none := by
  unfold decodeLock
  rw [ite_eq_right_iff]
  intro hc
  rw [suffix_length] at hc
  omega

theorem outOf_short {o : TxOut} (h : o.scriptPubKey.length < 4946) (t : BoltProof.Token Bytes) :
    outOf o ≠ .token t := by
  unfold outOf
  rw [decodeLock_short h]
  split_ifs <;> simp

/-- The parsed grandparent's token: its first output, and no other. -/
theorem gpTxA0_token {t0 : Bytes} {T : List Bytes} {w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 : Bytes}
    {issuer : Bytes} (hw : WidthsA0 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (hl : LockWidthsA T)
    (hi : issuer.length = 33) (h15 : item T 15 = 33 :: issuer) (h14 : item T 14 = SimpleMulti.suffix)
    (j : Nat) (t : BoltProof.Token Bytes)
    (hj : ((gpTxA0 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46).outputs.map outOf)[j]? = some (.token t)) :
    j = 0 ∧ t = tokenOf (gpFieldsA T issuer) := by
  have h0 : outOf (outOfBytes (item T 30) (lkA T)) = .token (tokenOf (gpFieldsA T issuer)) := by
    simp only [outOf, outOfBytes, lkA_eq hl h15 h14, decodeLock_lockScript (gpFieldsA_wf hl hi)]
  have h1 := outOf_short (o := outOfBytes (item T 30) ((item T 12).drop 1 ++ (item T 141 ++ [136, 172])))
    (by simp [outOfBytes, hw.pt, hw.pkh])
  have h2 := outOf_short (o := outOfBytes (item T 139) (item T 138)) (by simp [outOfBytes, hw.p2])
  have houts : (gpTxA0 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46).outputs =
      [outOfBytes (item T 30) (lkA T), outOfBytes (item T 30) ((item T 12).drop 1 ++ (item T 141 ++ [136, 172])),
        outOfBytes (item T 139) (item T 138)] := rfl
  rw [houts] at hj
  rcases j with _ | _ | _ | j
  · simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hj
    rw [h0] at hj
    exact ⟨rfl, (BoltProof.Out.token.inj hj).symm⟩
  · simp only [List.map_cons, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hj
    exact absurd hj (h1 t)
  · simp only [List.map_cons, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hj
    exact absurd hj (h2 t)
  · simp at hj

/-- **The anchor is the settled balance.** The run's `AnchorOK` on a commit token of type `ty` and balances
`n2`, `n3` (the grandparent's) against the spent balance `bal` and the index argument `x` is the model's
`settledBalance` of that token at the output index one below `x`. -/
theorem anchorOK_settled {ty n3 n2 bal x : Bytes} {vout : Nat} {g : Fields}
    (hty : g.ty = ty) (hlen : ty.length = 1) (hb : g.bal = n2) (hc : g.balCommit = n3)
    (h : AnchorOK (if ty = [37] then [1] else []) ty (encode (decode n3)) (encode (decode n2)) (encode (decode bal)) x)
    (hx : decode x = (vout : Int) + 1) (hn2 : 0 ≤ decode n2) (hn3 : 0 ≤ decode n3) (hbal : 0 ≤ decode bal) :
    balOf bal = (tokenOf g).settledBalance .fungible vout := by
  obtain ⟨b, rfl⟩ : ∃ b, ty = [b] := by
    match ty, hlen with
    | [b], _ => exact ⟨b, rfl⟩
  have hdx : ∀ k : Int, encode (decode x) = encode k → decode x = k := fun k hk => by
    have := congrArg decode hk; rwa [decode_encode, decode_encode] at this
  have hde : ∀ u v : Int, encode u = encode v → u = v := fun u v huv => by
    have := congrArg decode huv; rwa [decode_encode, decode_encode] at this
  simp only [BoltProof.Token.settledBalance, tokenOf, hty, hb, hc, List.headD_cons, balOf]
  rcases h with ⟨hc1, -, hn⟩ | ⟨hc0, h23, (⟨hx1, hn⟩ | ⟨hx2, hn⟩)⟩ | ⟨hc0, h23, hx1, hn⟩
  · -- a merge commit: the sum
    have hb37 : b = 37 := by
      by_cases h37 : [b] = [37]
      · simpa using h37
      · simp [h37, castToBool_nil] at hc1
    subst hb37
    have := hde _ _ hn
    rw [decode_encode, decode_encode] at this
    show (decode bal).toNat = (decode n2).toNat + (decode n3).toNat
    omega
  · -- a split commit, the first output: the remainder
    have hb23 : b = 0x23 := by simpa using h23
    subst hb23
    have hx' := hdx 1 (by rw [hx1]; decide)
    have hv : vout = 0 := by omega
    have := hde _ _ hn
    rw [decode_encode, decode_encode] at this
    show (decode bal).toNat = if vout = 0 then (decode n2).toNat - (decode n3).toNat else (decode n3).toNat
    simp only [hv, ↓reduceIte]
    omega
  · -- a split commit, the second output: the piece
    have hb23 : b = 0x23 := by simpa using h23
    subst hb23
    have hx' := hdx 2 (by rw [hx2]; decide)
    have hv : vout ≠ 0 := by omega
    show (decode bal).toNat = if vout = 0 then (decode n2).toNat - (decode n3).toNat else (decode n3).toNat
    simp only [hv, ↓reduceIte]
    have := hde _ _ hn
    rw [this]
  · -- any other type: the balance
    have hne37 : [b] ≠ [37] := by
      intro h37; simp [h37, castToBool_one] at hc0
    have hne23 : b ≠ 0x23 := by intro h; exact h23 (by rw [h])
    have hne37' : b ≠ 37 := by intro h; exact hne37 (by rw [h])
    have := hde _ _ hn
    have hv : (decode bal).toNat = (decode n2).toNat := by rw [this]
    rcases Nat.lt_or_ge b 0x21 with hlt | hge
    · have : BoltProof.Fam.modeOfCommitType .fungible b = none := by
        unfold BoltProof.Fam.modeOfCommitType; split <;> first | rfl | omega
      simp only [this]; exact hv
    · by_cases h21 : b = 0x21
      · subst h21; exact hv
      · have : BoltProof.Fam.modeOfCommitType .fungible b = none := by
          unfold BoltProof.Fam.modeOfCommitType; split <;> first | rfl | omega
        simp only [this]; exact hv

end BoltProof.Glue.SimpleMulti
