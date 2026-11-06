import BoltProof.Bridge.Glue.SimpleMulti.Anchor
import BoltProof.Bridge.Glue.SimpleMulti.GateItems

/-!
# The first rebuild's widths, from the run and the pieces

`decode_rebuiltA` reads the rebuilt grandparent under `WidthsA`. This file derives those widths: the run
fixes the version and the first script's varint, given that script is under 65536 bytes, which follows from
the pieces being at most 520 bytes each (`scA0_length_lt`); the spend's own fields fix the token value, the
lock-length varint and the proof template; the rest are the second piece set's widths (`HonestPiecesB`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Numbers BsvScript.Tx BsvScript.Sighash
open BoltProof.Glue.Serial
open BoltProof.Bridge.Generated
open BoltProof.Glue.MinSimple (sc scLen)

theorem optPush_length_le (w p : Bytes) : (optPush w p).length ≤ w.length + p.length + 1 := by
  unfold optPush; split_ifs with h
  · rw [List.length_append, h]; omega
  · simp

theorem optPush_length_le_520 {p : Bytes} (w : Bytes) (hp : p.length ≤ 520) (hw : w.length ≤ 1) :
    (optPush w p).length ≤ 522 := by
  have := optPush_length_le w p; omega

theorem encode_len_length_le {p : Bytes} (h : p.length ≤ 520) : (encode (p.length : Int)).length ≤ 2 :=
  (encode_length_le_iff _ 2 (by decide)).mpr (by simp; omega)

/-- The first input's unlocking script is under the two-byte varint bound when the pieces are at most 520
bytes, the scriptCode's issuer push and suffix are the lock's, and the run's length words are two bytes. -/
theorem scA0_length_lt (t0 : Bytes) (T : List Bytes) (w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 : Bytes) (h5 : rebuildA_fact5 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (h6 : rebuildA_fact6 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (h7 : rebuildA_fact7 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h8 : rebuildA_fact8 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (h11 : rebuildA_fact11 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (hp : ∀ x ∈ [item T 184, item T 185, item T 186, item T 187, item T 188, item T 189, item T 190, item T 191, item T 192, item T 193, item T 194, item T 195, item T 196, item T 197, item T 198, item T 199, item T 200, item T 201, item T 202, item T 203, item T 204, item T 205, item T 206, item T 207, item T 208, item T 209], x.length ≤ 520) (h15 : (item T 15).length ≤ 34)
    (h14 : (item T 14).length ≤ 4700) :
    (scA0 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46).length < 65536 := by
  have hw46 : w46.length = 150 := by rw [num2bin_length _ _ _ h11]; decide
  have hw18 : w18.length = 2 := by rw [num2bin_length _ _ _ h5]; decide
  have hw19 : w19.length = 2 := by rw [num2bin_length _ _ _ h6]; decide
  have hw20 : w20.length = 2 := by rw [num2bin_length _ _ _ h7]; decide
  have hw23 : w23.length = 2 := by rw [num2bin_length _ _ _ h8]; decide
  have hp184 : (item T 184).length ≤ 520 := hp _ (by simp)
  have hp185 : (item T 185).length ≤ 520 := hp _ (by simp)
  have hp186 : (item T 186).length ≤ 520 := hp _ (by simp)
  have hp187 : (item T 187).length ≤ 520 := hp _ (by simp)
  have hp188 : (item T 188).length ≤ 520 := hp _ (by simp)
  have hp189 : (item T 189).length ≤ 520 := hp _ (by simp)
  have hp190 : (item T 190).length ≤ 520 := hp _ (by simp)
  have hp191 : (item T 191).length ≤ 520 := hp _ (by simp)
  have hp192 : (item T 192).length ≤ 520 := hp _ (by simp)
  have hp193 : (item T 193).length ≤ 520 := hp _ (by simp)
  have hp194 : (item T 194).length ≤ 520 := hp _ (by simp)
  have hp195 : (item T 195).length ≤ 520 := hp _ (by simp)
  have hp196 : (item T 196).length ≤ 520 := hp _ (by simp)
  have hp197 : (item T 197).length ≤ 520 := hp _ (by simp)
  have hp198 : (item T 198).length ≤ 520 := hp _ (by simp)
  have hp199 : (item T 199).length ≤ 520 := hp _ (by simp)
  have hp200 : (item T 200).length ≤ 520 := hp _ (by simp)
  have hp201 : (item T 201).length ≤ 520 := hp _ (by simp)
  have hp202 : (item T 202).length ≤ 520 := hp _ (by simp)
  have hp203 : (item T 203).length ≤ 520 := hp _ (by simp)
  have hp204 : (item T 204).length ≤ 520 := hp _ (by simp)
  have hp205 : (item T 205).length ≤ 520 := hp _ (by simp)
  have hp206 : (item T 206).length ≤ 520 := hp _ (by simp)
  have hp207 : (item T 207).length ≤ 520 := hp _ (by simp)
  have hp208 : (item T 208).length ≤ 520 := hp _ (by simp)
  have hp209 : (item T 209).length ≤ 520 := hp _ (by simp)
  have ho209 := optPush_length_le_520 (encode 4) hp209 (by decide)
  have ho208 := optPush_length_le_520 (encode 4) hp208 (by decide)
  have ho207 := optPush_length_le_520 [20] hp207 (by decide)
  have ho206 := optPush_length_le_520 [36] hp206 (by decide)
  have ho205 := optPush_length_le_520 [36] hp205 (by decide)
  have ho202 := optPush_length_le_520 [20] hp202 (by decide)
  have ho201 := optPush_length_le_520 [20] hp201 (by decide)
  have ho200 := optPush_length_le_520 (encode 16) hp200 (by decide)
  have ho199 := optPush_length_le_520 [1] hp199 (by decide)
  have ho198 := optPush_length_le_520 [1] hp198 (by decide)
  have ho196 := optPush_length_le_520 [33] hp196 (by decide)
  have ho187 := optPush_length_le_520 [1] hp187 (by decide)
  have he197 := encode_len_length_le hp197
  have he184 := encode_len_length_le hp184
  simp only [scA0, List.length_append, List.length_cons, List.length_take, List.length_drop, List.length_nil]
  omega

/-- The second token input's unlocking script is under the two-byte varint bound, likewise. -/
theorem scA2_length_lt (t0 : Bytes) (T : List Bytes) (w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 : Bytes) (h2 : rebuildA_fact2 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (h11 : rebuildA_fact11 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h182 : ¬ decode (item T 182) = 0) (hp : ∀ x ∈ [item T 156, item T 157, item T 158, item T 159, item T 160, item T 161, item T 162, item T 163, item T 164, item T 165, item T 166, item T 167, item T 168, item T 169, item T 170, item T 171, item T 172, item T 173, item T 174, item T 175, item T 176, item T 177, item T 178, item T 179, item T 180, item T 181], x.length ≤ 520) (h15 : (item T 15).length ≤ 34)
    (h14 : (item T 14).length ≤ 4700) :
    (scA2 t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46).length < 65536 := by
  obtain ⟨-, hw13, hw12, hw11, hw10, -⟩ := rebuildA_fact2_parts t0 T w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 h2 h182
  have hw46 : w46.length = 150 := by rw [num2bin_length _ _ _ h11]; decide
  have h16 : ((t0 :: T)[16]?.getD []).length ≤ 34 := h15
  have h15' : ((t0 :: T)[15]?.getD []).length ≤ 4700 := h14
  have hp157 : ((t0 :: T)[157]?.getD []).length ≤ 520 := hp (item T 156) (by simp)
  have hp158 : ((t0 :: T)[158]?.getD []).length ≤ 520 := hp (item T 157) (by simp)
  have hp159 : ((t0 :: T)[159]?.getD []).length ≤ 520 := hp (item T 158) (by simp)
  have hp160 : ((t0 :: T)[160]?.getD []).length ≤ 520 := hp (item T 159) (by simp)
  have hp161 : ((t0 :: T)[161]?.getD []).length ≤ 520 := hp (item T 160) (by simp)
  have hp162 : ((t0 :: T)[162]?.getD []).length ≤ 520 := hp (item T 161) (by simp)
  have hp163 : ((t0 :: T)[163]?.getD []).length ≤ 520 := hp (item T 162) (by simp)
  have hp164 : ((t0 :: T)[164]?.getD []).length ≤ 520 := hp (item T 163) (by simp)
  have hp165 : ((t0 :: T)[165]?.getD []).length ≤ 520 := hp (item T 164) (by simp)
  have hp166 : ((t0 :: T)[166]?.getD []).length ≤ 520 := hp (item T 165) (by simp)
  have hp167 : ((t0 :: T)[167]?.getD []).length ≤ 520 := hp (item T 166) (by simp)
  have hp168 : ((t0 :: T)[168]?.getD []).length ≤ 520 := hp (item T 167) (by simp)
  have hp169 : ((t0 :: T)[169]?.getD []).length ≤ 520 := hp (item T 168) (by simp)
  have hp170 : ((t0 :: T)[170]?.getD []).length ≤ 520 := hp (item T 169) (by simp)
  have hp171 : ((t0 :: T)[171]?.getD []).length ≤ 520 := hp (item T 170) (by simp)
  have hp172 : ((t0 :: T)[172]?.getD []).length ≤ 520 := hp (item T 171) (by simp)
  have hp173 : ((t0 :: T)[173]?.getD []).length ≤ 520 := hp (item T 172) (by simp)
  have hp174 : ((t0 :: T)[174]?.getD []).length ≤ 520 := hp (item T 173) (by simp)
  have hp175 : ((t0 :: T)[175]?.getD []).length ≤ 520 := hp (item T 174) (by simp)
  have hp176 : ((t0 :: T)[176]?.getD []).length ≤ 520 := hp (item T 175) (by simp)
  have hp177 : ((t0 :: T)[177]?.getD []).length ≤ 520 := hp (item T 176) (by simp)
  have hp178 : ((t0 :: T)[178]?.getD []).length ≤ 520 := hp (item T 177) (by simp)
  have hp179 : ((t0 :: T)[179]?.getD []).length ≤ 520 := hp (item T 178) (by simp)
  have hp180 : ((t0 :: T)[180]?.getD []).length ≤ 520 := hp (item T 179) (by simp)
  have hp181 : ((t0 :: T)[181]?.getD []).length ≤ 520 := hp (item T 180) (by simp)
  have hp182 : ((t0 :: T)[182]?.getD []).length ≤ 520 := hp (item T 181) (by simp)
  have ho182 := optPush_length_le_520 (encode 4) hp182 (by decide)
  have ho181 := optPush_length_le_520 (encode 4) hp181 (by decide)
  have ho180 := optPush_length_le_520 [20] hp180 (by decide)
  have ho179 := optPush_length_le_520 [36] hp179 (by decide)
  have ho178 := optPush_length_le_520 [36] hp178 (by decide)
  have ho175 := optPush_length_le_520 [20] hp175 (by decide)
  have ho174 := optPush_length_le_520 [20] hp174 (by decide)
  have ho173 := optPush_length_le_520 (encode 16) hp173 (by decide)
  have ho172 := optPush_length_le_520 [1] hp172 (by decide)
  have ho171 := optPush_length_le_520 [1] hp171 (by decide)
  have ho169 := optPush_length_le_520 [33] hp169 (by decide)
  have ho160 := optPush_length_le_520 [1] hp160 (by decide)
  have he170 := encode_len_length_le hp170
  have he157 := encode_len_length_le hp157
  simp only [scA2, List.length_append, List.length_cons, List.length_take, List.length_drop, List.length_nil]
  omega

/-- The second piece set at the widths of the fields the first rebuild reads it as, for each optional arm:
the grandparent's lock time, change output and proof hash, its commit token's ten pushed fields, its second
input, and its first input's outpoint and sequence; and every piece at most 520 bytes. -/
structure HonestPiecesB (ps : Pieces75) : Prop where
  lt : ps.p0.length = 4
  p2 : ps.p1.length = 25
  v2 : ps.p2.length = 8
  pkh : ps.p4.length = 20
  gp : ps.p5.length = 36
  parent : ps.p6.length = 36
  outIdx : ps.p7.length = 1
  ty : ps.p8.length = 1
  ogp : ps.p9.length = 36
  com2 : ps.p10.length = 20
  com : ps.p11.length = 20
  pkh0 : ps.p12.length = 20
  balCommit : ps.p13.length = 16
  bal : ps.p14.length = 16
  sq1 : ps.p15.length = 4
  sc1 : 1 ≤ ps.p16.length ∧ ps.p16.length < 128
  op1 : ps.p17.length = 36
  sq0 : ps.p46.length = 4
  op0 : ps.p73.length = 36
  /-- with a second proof output (a split-commit grandparent), its key hash -/
  pkh2 : ¬ decode ps.p3 = 0 → ps.p3.length = 20
  /-- with a second token input (a merge-commit grandparent), its outpoint and sequence -/
  op2 : ¬ decode ps.p45 = 0 → ps.p45.length = 36
  sq2 : ¬ decode ps.p45 = 0 → ps.p18.length = 4
  size : ∀ x ∈ ps.stack, x.length ≤ 520

theorem lockWidthsA_gate {f : Fields} {a : Args} (S : List Bytes) (hp : HonestPiecesB a.psB) :
    LockWidthsA (gateT f a S) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [gateT_item151, gateT_item150, gateT_item149, gateT_item148, gateT_item147, gateT_item146,
      gateT_item145, gateT_item144, gateT_item143, gateT_item142]
  exacts [hp.bal, hp.balCommit, hp.pkh0, hp.com, hp.com2, hp.ogp, hp.ty, hp.outIdx, hp.parent, hp.gp]

/-- The widths `decode_rebuiltA` reads, on a transfer or split settle: from the run's facts, the spent lock
and preimage, and the honest pieces. -/
theorem widthsA_gate {f : Fields} {a : Args} {S : List Bytes} {t0 : Bytes} {w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 : Bytes}
    (hwf : WF f) (hsc : sc a.pre = lockScript f) (hop : 104 ≤ a.pre.length)
    (hval : (List.take 8 (List.drop (107 + (decode (List.take 2 (List.drop 105 a.pre))).toNat) a.pre)).length = 8)
    (hnty : a.nty = [0x20] ∨ a.nty = [0x22])
    (hlen : a.nty = [0x22] → (padN 16 (encode (decode f.bal - decode f.balCommit))).length = 16)
    (hp : HonestPiecesB a.psB)
    (h2 : rebuildA_fact2 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h3 : rebuildA_fact3 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (h5 : rebuildA_fact5 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h6 : rebuildA_fact6 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (h7 : rebuildA_fact7 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h8 : rebuildA_fact8 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (h9 : rebuildA_fact9 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (h11 : rebuildA_fact11 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) (h12 : rebuildA_fact12 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46) :
    WidthsA t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 := by
  have hpn : ∀ x ∈ [item (gateT f a S) 184, item (gateT f a S) 185, item (gateT f a S) 186, item (gateT f a S) 187, item (gateT f a S) 188, item (gateT f a S) 189, item (gateT f a S) 190, item (gateT f a S) 191, item (gateT f a S) 192, item (gateT f a S) 193, item (gateT f a S) 194, item (gateT f a S) 195, item (gateT f a S) 196, item (gateT f a S) 197, item (gateT f a S) 198, item (gateT f a S) 199, item (gateT f a S) 200, item (gateT f a S) 201, item (gateT f a S) 202, item (gateT f a S) 203, item (gateT f a S) 204, item (gateT f a S) 205, item (gateT f a S) 206, item (gateT f a S) 207, item (gateT f a S) 208, item (gateT f a S) 209], x.length ≤ 520 := by
    intro x hx
    simp only [gateT_item184, gateT_item185, gateT_item186, gateT_item187, gateT_item188, gateT_item189, gateT_item190, gateT_item191, gateT_item192, gateT_item193, gateT_item194, gateT_item195, gateT_item196, gateT_item197, gateT_item198, gateT_item199, gateT_item200, gateT_item201, gateT_item202, gateT_item203, gateT_item204, gateT_item205, gateT_item206, gateT_item207, gateT_item208, gateT_item209] at hx
    exact hp.size x (List.IsInfix.subset (⟨[a.psB.p0, a.psB.p1, a.psB.p2, a.psB.p3, a.psB.p4, a.psB.p5, a.psB.p6, a.psB.p7, a.psB.p8, a.psB.p9, a.psB.p10, a.psB.p11, a.psB.p12, a.psB.p13, a.psB.p14, a.psB.p15, a.psB.p16, a.psB.p17, a.psB.p18, a.psB.p19, a.psB.p20, a.psB.p21, a.psB.p22, a.psB.p23, a.psB.p24, a.psB.p25, a.psB.p26, a.psB.p27, a.psB.p28, a.psB.p29, a.psB.p30, a.psB.p31, a.psB.p32, a.psB.p33, a.psB.p34, a.psB.p35, a.psB.p36, a.psB.p37, a.psB.p38, a.psB.p39, a.psB.p40, a.psB.p41, a.psB.p42, a.psB.p43, a.psB.p44, a.psB.p45, a.psB.p46], [a.psB.p73, a.psB.p74], rfl⟩ :
      [a.psB.p47, a.psB.p48, a.psB.p49, a.psB.p50, a.psB.p51, a.psB.p52, a.psB.p53, a.psB.p54, a.psB.p55, a.psB.p56, a.psB.p57, a.psB.p58, a.psB.p59, a.psB.p60, a.psB.p61, a.psB.p62, a.psB.p63, a.psB.p64, a.psB.p65, a.psB.p66, a.psB.p67, a.psB.p68, a.psB.p69, a.psB.p70, a.psB.p71, a.psB.p72] <:+: a.psB.stack) hx)
  have hpn2 : ∀ x ∈ [item (gateT f a S) 156, item (gateT f a S) 157, item (gateT f a S) 158, item (gateT f a S) 159, item (gateT f a S) 160, item (gateT f a S) 161, item (gateT f a S) 162, item (gateT f a S) 163, item (gateT f a S) 164, item (gateT f a S) 165, item (gateT f a S) 166, item (gateT f a S) 167, item (gateT f a S) 168, item (gateT f a S) 169, item (gateT f a S) 170, item (gateT f a S) 171, item (gateT f a S) 172, item (gateT f a S) 173, item (gateT f a S) 174, item (gateT f a S) 175, item (gateT f a S) 176, item (gateT f a S) 177, item (gateT f a S) 178, item (gateT f a S) 179, item (gateT f a S) 180, item (gateT f a S) 181], x.length ≤ 520 := by
    intro x hx
    simp only [gateT_item156, gateT_item157, gateT_item158, gateT_item159, gateT_item160, gateT_item161, gateT_item162, gateT_item163, gateT_item164, gateT_item165, gateT_item166, gateT_item167, gateT_item168, gateT_item169, gateT_item170, gateT_item171, gateT_item172, gateT_item173, gateT_item174, gateT_item175, gateT_item176, gateT_item177, gateT_item178, gateT_item179, gateT_item180, gateT_item181] at hx
    exact hp.size x (List.IsInfix.subset (⟨[a.psB.p0, a.psB.p1, a.psB.p2, a.psB.p3, a.psB.p4, a.psB.p5, a.psB.p6, a.psB.p7, a.psB.p8, a.psB.p9, a.psB.p10, a.psB.p11, a.psB.p12, a.psB.p13, a.psB.p14, a.psB.p15, a.psB.p16, a.psB.p17, a.psB.p18], [a.psB.p45, a.psB.p46, a.psB.p47, a.psB.p48, a.psB.p49, a.psB.p50, a.psB.p51, a.psB.p52, a.psB.p53, a.psB.p54, a.psB.p55, a.psB.p56, a.psB.p57, a.psB.p58, a.psB.p59, a.psB.p60, a.psB.p61, a.psB.p62, a.psB.p63, a.psB.p64, a.psB.p65, a.psB.p66, a.psB.p67, a.psB.p68, a.psB.p69, a.psB.p70, a.psB.p71, a.psB.p72, a.psB.p73, a.psB.p74], rfl⟩ :
      [a.psB.p19, a.psB.p20, a.psB.p21, a.psB.p22, a.psB.p23, a.psB.p24, a.psB.p25, a.psB.p26, a.psB.p27, a.psB.p28, a.psB.p29, a.psB.p30, a.psB.p31, a.psB.p32, a.psB.p33, a.psB.p34, a.psB.p35, a.psB.p36, a.psB.p37, a.psB.p38, a.psB.p39, a.psB.p40, a.psB.p41, a.psB.p42, a.psB.p43, a.psB.p44] <:+: a.psB.stack) hx)
  have h15 : (item (gateT f a S) 15).length ≤ 34 := by rw [gateT_item15]; simp
  have h14 : (item (gateT f a S) 14).length ≤ 4700 := by
    rw [gateT_item14, scSuffix_of_sc hwf hsc, suffix_length]
  have hlk : (lkA (gateT f a S)).length = 4946 := by
    rw [lkA_eq (lockWidthsA_gate S hp) (by rw [gateT_item15]; exact scPush_issuer hwf hsc)
      (by rw [gateT_item14]; exact scSuffix_of_sc hwf hsc), lockScript_length (gpFieldsA_wf (lockWidthsA_gate S hp)
      hwf.issuer), suffix_length]
  refine ⟨widthA_ver t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 h12, ?_,
    widthA_vi0 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 h3 h9 h11 (scA0_length_lt t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 h5 h6 h7 h8 h11 hpn h15 h14),
    ?_, ?_, fun h => widthA_vi2 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 h2 h11 h (scA2_length_lt t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 h2 h11 h hpn2 h15 h14),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gateT_item210]; exact hp.op0
  · rw [gateT_item183]; exact hp.sq0
  · intro h
    show (item (gateT f a S) 182).length = 36
    rw [gateT_item182] at h ⊢; exact hp.op2 h
  · intro h
    show (item (gateT f a S) 155).length = 4
    rw [gateT_item182] at h; rw [gateT_item155]; exact hp.sq2 h
  · rw [gateT_item154]; exact hp.op1
  · rw [gateT_item153]; exact varIntOf_encode_small hp.sc1.1 hp.sc1.2
  · rw [gateT_item152]; exact hp.sq1
  · rw [gateT_item30]; exact hval
  · rw [gateT_item0 S hwf hsc hop hnty hlen, hlk]; exact varIntOf_fd (a := 0x52) (b := 0x13) (by decide)
  · exact gateT_item12 f a S
  · rw [gateT_item141]; exact hp.pkh
  · intro h
    show (item (gateT f a S) 140).length = 20
    rw [gateT_item140] at h ⊢; exact hp.pkh2 h
  · rw [gateT_item139]; exact hp.v2
  · rw [gateT_item138]; exact hp.p2
  · rw [gateT_item137]; exact hp.lt

/-- **The real grandparent is the parsed one**: a well-formed transaction whose txid is the spent token's
grandparent and whose serialisation has no second preimage is `gpTxA`. -/
theorem gp_eq_gpTxA {f : Fields} {a : Args} {S : List Bytes} {t0 : Bytes} {w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 : Bytes} {G : Tx}
    (h1 : rebuildA_fact1 t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (hw : WidthsA t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46)
    (hG : TxWF G) (hnsp : ∀ y, Hash.hash256 y = Hash.hash256 (serTx G) → y = serTx G)
    (htxid : txid G = List.take 32 f.gp) :
    G = gpTxA t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 := by
  rw [rebuildA_fact1_eq, gateT_item36] at h1
  have hX : rebuiltA t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 = serTx G := hnsp _ (by rw [h1, ← htxid]; rfl)
  exact eq_of_serTx hG hX (decode_rebuiltA t0 (gateT f a S) w10 w11 w12 w13 w14 w17 w18 w19 w20 w23 w46 hw)

end BoltProof.Glue.SimpleMulti
