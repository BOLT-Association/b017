import BoltProof.Bridge.Glue.SimpleMulti.Weld
import BoltProof.Bridge.Glue.SimpleMulti.Sound

/-!
# `SimpleMultiBOLT`: `Accepts` from the facts

`accepts_of_facts` assembles `Accepts .fungible (spendOf …)` from the clause-level facts a successful run
establishes, as `Refine/Facts.lean` does for the NFT family: the type and mode clauses and the issuer clauses
follow from the lock's type, the next type and the prologue's guard; the others are hypotheses each path
discharges (`Refine.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Numbers BsvScript.Tx BsvScript.Sighash
open BoltProof.Glue.MinSimple (outpointOf)

theorem kindOf_melt_iff {f : Fields} {a : Args} : kindOf f a = .melt ↔ castToBool a.pre = false := by
  unfold kindOf; split_ifs with h1 h2 <;> simp_all

theorem kindOf_commit_iff {f : Fields} {a : Args} : kindOf f a = .commit ↔ castToBool a.pre = true ∧ settledTy f.ty := by
  unfold kindOf; split_ifs with h1 h2 <;> simp_all

theorem kindOf_settle_iff {f : Fields} {a : Args} : kindOf f a = .settle ↔ castToBool a.pre = true ∧ ¬ settledTy f.ty := by
  unfold kindOf; split_ifs with h1 h2 <;> simp_all

/-- The fungible issuer rule is the genesis: a parentless token. -/
theorem issuerMustSign_iff {f : Fields} : (tokenOf f).issuerMustSign .fungible ↔ decode f.parent = 0 := by
  simp only [Token.issuerMustSign, Token.isGenesis, tokenOf, outpointOf]
  split_ifs with h <;> simp_all

/-- Everything `Accepts` needs of `spendOf`, from the facts the bytes establish. -/
theorem accepts_of_facts (P : Prims Bytes) (tx : Tx) (i : Nat) (f : Fields) (a : Args)
    (other : Option (Fields × Outpoint Bytes)) (ancA ancB : Option Tx)
    (hty : SmbType f.ty) (hnty : SmbType a.nty)
    (hpar : castToBool a.pre = true → settledTy f.ty → ¬ settledTy a.nty)
    (hgen : decode f.parent = 0 → settledTy f.ty)
    (hin : i < tx.inputs.length)
    (hver : 2 ≤ tx.version)
    (howner : P.h160 a.pk = f.pkh)
    (hsig : P.verify a.pk (P.sighash (absTx tx) i) a.sig = true)
    (htype : a.sig.getLast?.getD 0 = 0x41)
    (hissuer : GuardF f → f.issuer = a.pk ∧ a.nty ≠ [0x25] ∧ a.nty ≠ [0x27])
    (houts : kindOf f a ≠ .melt → ∃ change : List (Out Bytes), (∀ o ∈ change, o.isToken = false) ∧
      (absTx tx).outputs = (spendOf tx i f a other ancA ancB).expectedOuts .fungible ++ change)
    (hmelt : kindOf f a = .melt → ∀ o ∈ (absTx tx).outputs, o.isP2pkh = true)
    (hbound : balOf f.bal ≤ Fam.maxBalance)
    (hsplit : kindOf f a = .commit → modeOf f a = .split → balOf a.nbc ≤ balOf f.bal)
    (hmerge : kindOf f a = .commit → modeOf f a = .merge →
      ∃ o, other.map (fun o => (tokenOf o.1, o.2)) = some o ∧ balOf f.bal + o.1.balance ≤ Fam.maxBalance)
    (hsplitS : kindOf f a = .settle → modeOf f a = .split → balOf f.balCommit ≤ balOf f.bal)
    (hmergeS : kindOf f a = .settle → modeOf f a = .merge → balOf f.bal + balOf f.balCommit ≤ Fam.maxBalance)
    (hother : other.isSome ↔ (kindOf f a = .commit ∧ modeOf f a = .merge))
    (hotherIn : ∀ o, other = some o → (⟨o.2.txid, o.2.vout⟩ : Outpoint Bytes) ∈ (absTx tx).inputs ∧
      o.2 ≠ ⟨(inputAt tx i).prevHash, (inputAt tx i).prevIndex⟩)
    (hotherIss : ∀ o, other = some o → o.1.issuer = f.issuer)
    (hotherTy : ∀ o, other = some o → (tokenOf o.1).txoType ∈ Fam.settleTypes .fungible)
    (hreb : kindOf f a = .settle → ∀ gp, outpointOf f.gp = some gp →
      ∃ (A : TxDesc Bytes) (t : Token Bytes), (spendOf tx i f a other ancA ancB).anc = some A ∧ P.txid A = gp.txid ∧
        A.outputs[gp.vout]? = some (.token t) ∧
        (∃ j pkh, A.outputs[j]? = some (.proof pkh) ∧ (⟨gp.txid, j⟩ : Outpoint Bytes) ∈ (absTx tx).inputs) ∧
        ∀ p, outpointOf f.parent = some p → balOf f.bal = t.settledBalance .fungible p.vout)
    (hrebB : kindOf f a = .settle → ∀ ogp, outpointOf f.ogp = some ogp →
      ∃ (B : TxDesc Bytes) (t : Token Bytes), (spendOf tx i f a other ancA ancB).ancB = some B ∧
        P.txid B = ogp.txid ∧ B.outputs[ogp.vout]? = some (.token t) ∧
        ∃ j pkh, B.outputs[j]? = some (.proof pkh) ∧ (⟨ogp.txid, j⟩ : Outpoint Bytes) ∈ (absTx tx).inputs)
    (hnull : (kindOf f a = .commit ∨ outpointOf f.gp = none) → ancA = none ∧ ancB = none) :
    Accepts P .fungible (spendOf tx i f a other ancA ancB) where
  input_is_spent := by
    simp [spendOf, absTx, inputAt, List.getElem?_eq_getElem hin]
  version := hver
  l1_owner := howner
  l1_sig := hsig
  l1_type := htype
  commit_type := by
    intro h
    obtain ⟨-, h0⟩ := kindOf_commit_iff.mp h
    rcases h0 with h0 | h0 | h0 <;> simp [spendOf, tokenOf, h0, Fam.settleTypes]
  commit_mode := by
    intro h
    obtain ⟨hpre, h0⟩ := kindOf_commit_iff.mp h
    have hns := hpar hpre h0
    have hk : kindOf f a = .commit := h
    simp only [spendOf, modeOf, hk, ↓reduceIte]
    rcases hnty with hn | hn | hn | hn | hn | hn
    · exact absurd (Or.inl hn) hns
    · simp [hn, modeOfNext, Mode.commitType, Fam.commitTypes]
    · exact absurd (Or.inr (Or.inl hn)) hns
    · simp [hn, modeOfNext, Mode.commitType, Fam.commitTypes]
    · exact absurd (Or.inr (Or.inr hn)) hns
    · simp [hn, modeOfNext, Mode.commitType, Fam.commitTypes]
  settle_type := by
    intro h
    obtain ⟨-, h0⟩ := kindOf_settle_iff.mp h
    rcases hty with hn | hn | hn | hn | hn | hn
    · exact absurd (Or.inl hn) h0
    · simp [spendOf, tokenOf, hn, Fam.commitTypes]
    · exact absurd (Or.inr (Or.inl hn)) h0
    · simp [spendOf, tokenOf, hn, Fam.commitTypes]
    · exact absurd (Or.inr (Or.inr hn)) h0
    · simp [spendOf, tokenOf, hn, Fam.commitTypes]
  settle_mode := by
    intro h
    have hs : kindOf f a = .settle := h
    obtain ⟨-, h0⟩ := kindOf_settle_iff.mp hs
    have hk : kindOf f a ≠ .commit := by rw [hs]; decide
    simp only [spendOf, modeOf, hk, ↓reduceIte, tokenOf]
    rcases hty with hn | hn | hn | hn | hn | hn
    · exact absurd (Or.inl hn) h0
    · simp [hn, Fam.modeOfCommitType]
    · exact absurd (Or.inr (Or.inl hn)) h0
    · simp [hn, Fam.modeOfCommitType]
    · exact absurd (Or.inr (Or.inr hn)) h0
    · simp [hn, Fam.modeOfCommitType]
  l5_issuer := fun h => (hissuer (Or.inl (issuerMustSign_iff.mp h))).1.symm
  l5_no_merge_at_genesis := by
    intro hg hm
    have hgen0 : decode f.parent = 0 := by
      have : (tokenOf f).parent = none := hg
      simp only [tokenOf, outpointOf] at this; split_ifs at this with h <;> simp_all
    have hn25 := (hissuer (Or.inl hgen0)).2.1
    have hm' : modeOf f a = .merge := hm
    unfold modeOf at hm'
    split_ifs at hm' with hk
    · simp only [modeOfNext] at hm'; split_ifs at hm' <;> simp_all
    · rcases hgen hgen0 with h0 | h0 | h0 <;> simp [h0, Fam.modeOfCommitType] at hm'
  l2_outs := houts
  l2_melt := hmelt
  l6_bound := fun _ => hbound
  l6_split := fun hk hm => hsplit hk hm
  l6_merge := fun hk hm => hmerge hk hm
  l6_settle_split := fun hk hm => hsplitS hk hm
  l6_settle_merge := fun hk hm => hmergeS hk hm
  other_iff_merge := by simpa [spendOf] using hother
  other_input := by
    rintro ⟨t, o⟩ ho
    simp only [spendOf, Option.map_eq_some_iff] at ho
    obtain ⟨⟨g, o'⟩, hgo, he⟩ := ho
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact hotherIn _ hgo
  l_merge_same_issuer := by
    rintro ⟨t, o⟩ ho
    simp only [spendOf, Option.map_eq_some_iff] at ho
    obtain ⟨⟨g, o'⟩, hgo, he⟩ := ho
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    simp only [tokenOf, spendOf]; exact hotherIss _ hgo
  other_settle_typed := by
    rintro ⟨t, o⟩ ho
    simp only [spendOf, Option.map_eq_some_iff] at ho
    obtain ⟨⟨g, o'⟩, hgo, he⟩ := ho
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact hotherTy _ hgo
  l3_rebuild := by
    intro h gp hgp
    obtain ⟨A, t, hanc, htxid, hout, hproof, hbal⟩ := hreb h gp hgp
    exact ⟨A, t, hanc, htxid, hout, hproof, fun _ p hp => hbal p hp⟩
  l3_merge := fun h ogp hogp => hrebB h ogp hogp
  l4_null := by
    rintro (h | h)
    · obtain ⟨h1, h2⟩ := hnull (Or.inl h); simp [spendOf, h1, h2]
    · obtain ⟨h1, h2⟩ := hnull (Or.inr h); simp [spendOf, h1, h2]

end BoltProof.Glue.SimpleMulti
