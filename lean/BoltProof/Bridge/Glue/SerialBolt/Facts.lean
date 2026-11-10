import BoltProof.Bridge.Glue.SerialBolt.Abs

/-!
# `Accepts` from the facts the bytes establish

`accepts_of_facts` discharges the twenty-six clauses of the covenant interface
(`Model/Covenant.lean`) for the abstracted spend `spendOf` (`SerialBolt/Abs.lean`) from the
handful of facts the symbolic run and the serialisation lemmas provide: the input exists, the
version, the owner's hash and signature, the sighash byte, the issuer guard, the output
decomposition, the melt outputs and the rebuilt grandparent. The clauses about balances, modes
and second inputs are vacuous for the NFT family, which only transfers.
-/

set_option autoImplicit false

namespace BoltProof.Glue.SerialBolt

open BsvScript BsvScript.Numbers BsvScript.Tx BsvScript.Sighash

theorem kindOf_melt {f : Fields} {a : Args} : kindOf f a = .melt ↔ castToBool a.pre = false := by
  unfold kindOf; split_ifs <;> simp_all

theorem kindOf_commit {f : Fields} {a : Args} : kindOf f a = .commit ↔ castToBool a.pre = true ∧ f.ty = [0] := by
  unfold kindOf; split_ifs <;> simp_all

theorem kindOf_settle {f : Fields} {a : Args} : kindOf f a = .settle ↔ castToBool a.pre = true ∧ f.ty ≠ [0] := by
  unfold kindOf; split_ifs <;> simp_all

/-- The NFT issuer rule on the abstracted token is the covenant's guard. -/
theorem issuerMustSign_iff {f : Fields} (hty : f.ty = [0] ∨ f.ty = [0x21]) :
    (tokenOf f).issuerMustSign .nft ↔ Guard f := by
  simp only [Token.issuerMustSign, Token.isGenesis, Token.is2ndTx, tokenOf, outpointOf, Guard, true_and]
  rcases hty with hty | hty <;> simp only [hty] <;> split_ifs <;> simp_all

/-- Everything `Accepts` needs of `spendOf`, from the facts the bytes establish. -/
theorem accepts_of_facts (P : Prims Bytes) (tx : Tx) (i : Nat) (f : Fields) (a : Args)
    (hty : f.ty = [0] ∨ f.ty = [0x21])
    (hin : i < tx.inputs.length)
    (hver : 2 ≤ tx.version)
    (howner : P.h160 a.pk = f.pkh)
    (hsig : P.verify a.pk (P.sighash (absTx tx) i) a.sig = true)
    (htype : a.sig.getLast?.getD 0 = 0x41)
    (hissuer : Guard f → f.issuer = a.pk)
    (houts : kindOf f a ≠ .melt → ∃ change : List (Out Bytes), (∀ o ∈ change, o.isToken = false) ∧
      (absTx tx).outputs = (spendOf tx i f a).expectedOuts .nft ++ change)
    (hmelt : kindOf f a = .melt → ∀ o ∈ (absTx tx).outputs, o.isP2pkh = true)
    (hreb : kindOf f a = .settle → ∀ gp, outpointOf f.gp = some gp →
      ∃ (A : TxDesc Bytes) (t : Token Bytes), (spendOf tx i f a).anc = some A ∧ P.txid A = gp.txid ∧
        A.outputs[gp.vout]? = some (.token t) ∧
        ∃ j pkh, A.outputs[j]? = some (.proof pkh) ∧ (⟨gp.txid, j⟩ : Outpoint Bytes) ∈ (absTx tx).inputs) :
    Accepts P .nft (spendOf tx i f a) where
  input_is_spent := by
    simp [spendOf, absTx, inputAt, List.getElem?_eq_getElem hin]
  version := hver
  l1_owner := howner
  l1_sig := hsig
  l1_type := htype
  commit_type := by
    intro h
    obtain ⟨-, h0⟩ := kindOf_commit.mp h
    simp [spendOf, tokenOf, h0, Fam.settleTypes]
  commit_mode := fun _ => by simp [spendOf, Mode.commitType, Fam.commitTypes]
  settle_type := by
    intro h
    obtain ⟨-, h0⟩ := kindOf_settle.mp h
    rcases hty with hty | hty
    · exact absurd hty h0
    · simp [spendOf, tokenOf, hty, Fam.commitTypes]
  settle_mode := by
    intro h
    obtain ⟨-, h0⟩ := kindOf_settle.mp h
    rcases hty with hty | hty
    · exact absurd hty h0
    · simp [spendOf, tokenOf, hty, Fam.modeOfCommitType]
  l5_issuer := fun h => (hissuer ((issuerMustSign_iff hty).mp h)).symm
  l5_no_merge_at_genesis := fun _ => by simp [spendOf]
  l2_outs := fun hk => Spend.outsOK_of_canonical (houts hk)
  l2_melt := hmelt
  l6_bound := fun h => by cases h
  l6_split := fun _ h => by cases h
  l6_merge := fun _ h => by cases h
  l6_settle_split := fun _ h => by cases h
  l6_settle_merge := fun _ h => by cases h
  other_iff_merge := by simp [spendOf]
  other_input := fun _ h => by cases h
  l_merge_same_issuer := fun _ h => by cases h
  other_settle_typed := fun _ h => by cases h
  l3_rebuild := by
    intro h gp hgp
    obtain ⟨A, t, hanc, htxid, hout, j, pkh, hproof, hmem⟩ := hreb h gp hgp
    exact ⟨A, t, j, pkh, hanc, htxid, hout, hproof, hmem, fun h => by cases h⟩
  l3_merge := fun _ _ h => by cases h
  l4_null := by
    rintro (h | h)
    · have hk : kindOf f a = .commit := h
      have : kindOf f a ≠ .settle := by rw [hk]; decide
      simp [spendOf, this]
    · have hg : outpointOf f.gp = none := h
      have : decode f.gp = 0 := by
        by_contra hne
        simp [outpointOf, hne] at hg
      simp [spendOf, this]

end BoltProof.Glue.SerialBolt
