import BoltProof.Bridge.Glue.MinSimple.Paths
import BoltProof.Bridge.Glue.Sections

/-!
# `MinSimpleBOLT`: the suffix enforces `Enforced`

The eleven path theorems of `MinSimple/Paths.lean` assembled: whatever the lock fields (of a token
of either type) and the unlocking arguments, a run of the suffix that does not fail enforces
`Enforced` (with a preimage) or `EnforcedMelt` (without), passes the two proved fragments, and
ends with the owner's `OP_CHECKSIG` result on top. The two `reaches_*` corollaries are the
reviewer's literal ask (`lean/README.md`, Finding 2): the run reaches each proved
fragment literal with the stack its lemma assumes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BoltProof.Glue.MinSimple

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

/-- **The glue theorem for `MinSimpleBOLT`.** From the stack the six lock pushes and the unlocking
script leave, in an active arm, the suffix either fails or enforces everything `Enforced` (or
`EnforcedMelt`) lists, and runs on with the owner's signature check on top. -/
theorem minSimple_sound {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x00] ∨ f.ty = [0x21])
    (h : run Eval.opExec env (MinSimple.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    (castToBool a.pre = true → Enforced env f a cs ∧ Reached env f a k t r cs) ∧
      (castToBool a.pre = false → EnforcedMelt env f a) ∧ Ends env a k t r C cs := by
  by_cases hpre : castToBool a.pre = true
  · have key : Enforced env f a cs ∧ Reached env f a k t r cs ∧ Ends env a k t r C cs := by
      rcases hty with hty | hty
      · by_cases hpar : decode f.parent = 0
        · exact commit_genesis he hact hty hpar hpre h hr
        · exact commit_later he hact hty hpar hpre h hr
      · by_cases hgp : decode f.gp = 0 <;> by_cases hpar : decode f.parent = 0
        · exact settle_noGp_genesis he hact hty hpar hgp hpre h hr
        · exact settle_noGp_later he hact hty hpar hgp hpre h hr
        · exact settle_genesis he hact hty hpar hgp hpre h hr
        · exact settle_later he hact hty hpar hgp hpre h hr
    exact ⟨fun _ => ⟨key.1, key.2.1⟩, fun h0 => (by rw [h0] at hpre; cases hpre), key.2.2⟩
  · have hpre' : castToBool a.pre = false := by simpa using hpre
    have key : EnforcedMelt env f a ∧ Ends env a k t r C cs := by
      rcases hty with hty | hty
      · by_cases hpar : decode f.parent = 0
        · exact melt_commit_genesis he hact hty hpar hpre' h hr
        · exact melt_commit_later he hact hty hpar hpre' h hr
      · by_cases hgp : decode f.gp = 0
        · exact melt_settle_noGp he hact hty hgp hpre' h hr
        · by_cases hpar : decode f.parent = 0
          · exact melt_settle_genesis he hact hty hpar hgp hpre' h hr
          · exact melt_settle_later he hact hty hpar hgp hpre' h hr
    exact ⟨fun h1 => absurd h1 hpre, fun _ => key.1, key.2⟩

/-! ## The fragments are reached

`Sections.lean` says what sits at 534 and 1072; `Reached` says the run gets there with the stack
the fragment lemma assumes. Put together, the fragment literal itself is run. -/

/-- The suffix from 534 is the NFT type selector followed by the suffix from 547. -/
theorem suffix_drop_534 : MinSimple.suffix.drop 534 = Gadgets.nftTypeSel 0x17 ++ MinSimple.suffix.drop 547 := by
  decide +kernel

/-- The suffix from 1072 is the null-ancestor tail followed by the suffix from 1076. -/
theorem suffix_drop_1072 : MinSimple.suffix.drop 1072 = Gadgets.nullTail ++ MinSimple.suffix.drop 1076 := by
  decide +kernel

/-- **The type selector is reached.** With a preimage, the run of the suffix executes the fragment
`nftTypeSel 0x17` (`Gadgets/NftType.lean`) from a stack whose element at depth `0x17 = 23` is the
raw type byte `f.ty`, in an active arm, and the rest of the suffix runs on to the same outcome. -/
theorem reaches_nftTypeSel {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x00] ∨ f.ty = [0x21]) (hpre : castToBool a.pre = true)
    (h : run Eval.opExec env (MinSimple.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    ∃ (S' A' : List Bytes) (m' : Nat) (C' : Cond) (kk' : Nat),
      run Eval.opExec env (Gadgets.nftTypeSel 0x17 ++ (MinSimple.suffix.drop 547 ++ k)) t
        (St S' A' m' C' kk' cs) = r ∧ C'.isActive = true ∧ S'.getD 23 [] = f.ty := by
  obtain ⟨S', A', m', C', kk', hrun, hC, hS⟩ := ((minSimple_sound he hact hty h hr).1 hpre).2.typeSel
  rw [suffix_drop_534, List.append_assoc] at hrun
  exact ⟨S', A', m', C', kk', hrun, hC, hS⟩

/-- **The null-ancestor tail is reached.** With a preimage, unless the spend is a settle of a
token with a grandparent, the run executes the fragment `nullTail` (`Gadgets/NullAncestor.lean`)
from a stack whose top is the concatenation of the 26 pieces, in an active arm. -/
theorem reaches_nullTail {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : f.ty = [0x00] ∨ f.ty = [0x21]) (hpre : castToBool a.pre = true)
    (hn : f.ty = [0] ∨ decode f.gp = 0)
    (h : run Eval.opExec env (MinSimple.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    ∃ (S' A' : List Bytes) (m' : Nat) (C' : Cond) (kk' : Nat),
      run Eval.opExec env (Gadgets.nullTail ++ (MinSimple.suffix.drop 1076 ++ k)) t
        (St S' A' m' C' kk' cs) = r ∧ C'.isActive = true ∧ S'.head? = some a.ps.cat := by
  obtain ⟨S', A', m', C', kk', hrun, hC, hS⟩ := ((minSimple_sound he hact hty h hr).1 hpre).2.nullTail hn
  rw [suffix_drop_1072, List.append_assoc] at hrun
  exact ⟨S', A', m', C', kk', hrun, hC, hS⟩

end BoltProof.Glue.MinSimple
