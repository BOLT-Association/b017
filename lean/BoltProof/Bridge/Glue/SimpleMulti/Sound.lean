import BoltProof.Bridge.Glue.SimpleMulti.Paths
import BoltProof.Bridge.Glue.SimpleMulti.Settle.Transfer
import BoltProof.Bridge.Glue.SimpleMulti.Settle.Split
import BoltProof.Bridge.Glue.SimpleMulti.Settle.Merge
import BoltProof.Bridge.Glue.SimpleMulti.Melt
import BoltProof.Bridge.Glue.SimpleMulti.Refute

/-!
# The glue theorem for `SimpleMultiBOLT`

`simpleMulti_sound` assembles the path theorems: for a lock whose type is one of the family's six and a
next type among them, a successful run of the suffix enforces what `SpendEnforced` lists for the spend's
shape and ends with the owner's signature check on top. With a preimage, a settle-typed (even) token is
committed (`Enforced`, the nine commit paths), a commit-typed (odd) token is settled into its own settle type
(`EnforcedSettle` with a grandparent, `EnforcedSettle0` without), and every other pair is refused by the parity
check (`Refute.lean`); without one the token is melted (`EnforcedMelt`). No hypothesis constrains an unlock
argument except the next type, and that one only to the family's six types: a next type outside them is the
plan's open question 4 (§7).
-/

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

namespace BoltProof.Glue.SimpleMulti

open BsvScript BsvScript.Params BsvScript.Numbers BsvScript.Machine BsvScript.Gadget
open BoltProof.Bridge.Generated

/-- The family's six types: transfer, split and merge, each settled (even) and committed (odd). -/
def SmbType (b : Bytes) : Prop :=
  b = [0x20] ∨ b = [0x21] ∨ b = [0x22] ∨ b = [0x23] ∨ b = [0x24] ∨ b = [0x25]

/-- What the suffix enforces on a spend, by its shape: a commit of a settle-typed token, a settle of a
commit-typed token with or without a grandparent, or a melt. -/
def SpendEnforced (env : Env) (f : Fields) (a : Args) (S : List Bytes) (cs : Bytes) : Prop :=
  if castToBool a.pre = true then
    if f.ty = [0x20] ∨ f.ty = [0x22] ∨ f.ty = [0x24] then Enforced env f a cs
    else if decode f.gp = 0 then EnforcedSettle0 env f a cs else EnforcedSettle env f a S cs
  else EnforcedMelt env f a

/-- **The glue theorem for `SimpleMultiBOLT`.** From the stack the eleven lock pushes and the unlocking script
leave, in an active arm, with the scriptCode's length a `fd` varint when there is a preimage, a successful run of the suffix enforces
`SpendEnforced` and runs on with the owner's signature check on top. -/
theorem simpleMulti_sound {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : SmbType f.ty) (hnty : castToBool a.pre = true → SmbType a.nty)
    (hvar : castToBool a.pre = true → List.take 1 (List.drop 104 a.pre) = [0xfd])
    (h : run Eval.opExec env (SimpleMulti.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) : SpendEnforced env f a S cs ∧ Ends env a k t r C cs := by
  by_cases hpre : castToBool a.pre = true
  · rcases hty with hty|hty|hty|hty|hty|hty <;> rcases hnty hpre with hnty|hnty|hnty|hnty|hnty|hnty
    · exact (refuse_20_20 he hact hpre (hvar hpre) hty hnty h hr).elim
    · have key := commit_20_21 he hact hpre (hvar hpre) hty hnty h hr
      simp (config := { decide := true }) only [SpendEnforced, hpre, hty, ↓reduceIte]
      exact key
    · exact (refuse_20_22 he hact hpre (hvar hpre) hty hnty h hr).elim
    · have key := commit_20_23 he hact hpre (hvar hpre) hty hnty h hr
      simp (config := { decide := true }) only [SpendEnforced, hpre, hty, ↓reduceIte]
      exact key
    · exact (refuse_20_24 he hact hpre (hvar hpre) hty hnty h hr).elim
    · have key := commit_20_25 he hact hpre (hvar hpre) hty hnty h hr
      simp (config := { decide := true }) only [SpendEnforced, hpre, hty, ↓reduceIte]
      exact key
    · by_cases hgp : decode f.gp = 0
      · have key := settle0_21_20 he hact hpre (hvar hpre) hty hnty hgp h hr
        simp (config := { decide := true }) only [SpendEnforced, hpre, hty, hgp, ↓reduceIte]
        exact key
      · have key := settle_21_20 he hact hpre (hvar hpre) hty hnty hgp h hr
        simp (config := { decide := true }) only [SpendEnforced, hpre, hty, hgp, ↓reduceIte]
        exact key
    · exact (refuse_21_21 he hact hpre (hvar hpre) hty hnty h hr).elim
    · exact (refuse_21_22 he hact hpre (hvar hpre) hty hnty h hr).elim
    · exact (refuse_21_23 he hact hpre (hvar hpre) hty hnty h hr).elim
    · exact (refuse_21_24 he hact hpre (hvar hpre) hty hnty h hr).elim
    · exact (refuse_21_25 he hact hpre (hvar hpre) hty hnty h hr).elim
    · exact (refuse_22_20 he hact hpre (hvar hpre) hty hnty h hr).elim
    · have key := commit_22_21 he hact hpre (hvar hpre) hty hnty h hr
      simp (config := { decide := true }) only [SpendEnforced, hpre, hty, ↓reduceIte]
      exact key
    · exact (refuse_22_22 he hact hpre (hvar hpre) hty hnty h hr).elim
    · have key := commit_22_23 he hact hpre (hvar hpre) hty hnty h hr
      simp (config := { decide := true }) only [SpendEnforced, hpre, hty, ↓reduceIte]
      exact key
    · exact (refuse_22_24 he hact hpre (hvar hpre) hty hnty h hr).elim
    · have key := commit_22_25 he hact hpre (hvar hpre) hty hnty h hr
      simp (config := { decide := true }) only [SpendEnforced, hpre, hty, ↓reduceIte]
      exact key
    · exact (refuse_23_20 he hact hpre (hvar hpre) hty hnty h hr).elim
    · exact (refuse_23_21 he hact hpre (hvar hpre) hty hnty h hr).elim
    · by_cases hgp : decode f.gp = 0
      · have key := settle0_23_22 he hact hpre (hvar hpre) hty hnty hgp h hr
        simp (config := { decide := true }) only [SpendEnforced, hpre, hty, hgp, ↓reduceIte]
        exact key
      · have key := settle_23_22 he hact hpre (hvar hpre) hty hnty hgp h hr
        simp (config := { decide := true }) only [SpendEnforced, hpre, hty, hgp, ↓reduceIte]
        exact key
    · exact (refuse_23_23 he hact hpre (hvar hpre) hty hnty h hr).elim
    · exact (refuse_23_24 he hact hpre (hvar hpre) hty hnty h hr).elim
    · exact (refuse_23_25 he hact hpre (hvar hpre) hty hnty h hr).elim
    · exact (refuse_24_20 he hact hpre (hvar hpre) hty hnty h hr).elim
    · have key := commit_24_21 he hact hpre (hvar hpre) hty hnty h hr
      simp (config := { decide := true }) only [SpendEnforced, hpre, hty, ↓reduceIte]
      exact key
    · exact (refuse_24_22 he hact hpre (hvar hpre) hty hnty h hr).elim
    · have key := commit_24_23 he hact hpre (hvar hpre) hty hnty h hr
      simp (config := { decide := true }) only [SpendEnforced, hpre, hty, ↓reduceIte]
      exact key
    · exact (refuse_24_24 he hact hpre (hvar hpre) hty hnty h hr).elim
    · have key := commit_24_25 he hact hpre (hvar hpre) hty hnty h hr
      simp (config := { decide := true }) only [SpendEnforced, hpre, hty, ↓reduceIte]
      exact key
    · exact (refuse_25_20 he hact hpre (hvar hpre) hty hnty h hr).elim
    · exact (refuse_25_21 he hact hpre (hvar hpre) hty hnty h hr).elim
    · exact (refuse_25_22 he hact hpre (hvar hpre) hty hnty h hr).elim
    · exact (refuse_25_23 he hact hpre (hvar hpre) hty hnty h hr).elim
    · by_cases hgp : decode f.gp = 0
      · have key := settle0_25_24 he hact hpre (hvar hpre) hty hnty hgp h hr
        simp (config := { decide := true }) only [SpendEnforced, hpre, hty, hgp, ↓reduceIte]
        exact key
      · have key := settle_25_24 he hact hpre (hvar hpre) hty hnty hgp h hr
        simp (config := { decide := true }) only [SpendEnforced, hpre, hty, hgp, ↓reduceIte]
        exact key
    · exact (refuse_25_25 he hact hpre (hvar hpre) hty hnty h hr).elim
  · have hpre' : castToBool a.pre = false := by simpa using hpre
    have key := melt he hact hpre' h hr
    simp only [SpendEnforced, hpre', Bool.false_eq_true, ↓reduceIte]
    exact key

/-- **The type relations a successful run leaves.** A settle-typed (even) token is followed by a commit type and a
commit-typed (odd) token by its own settle type: every other pair is refused (`Refute.lean`). -/
theorem types_of_run {env : Env} (he : EnvOK env) {k t : Bytes} {r : GOut} {f : Fields} {a : Args}
    {S A : List Bytes} {C : Cond} {cs : Bytes} {m kk : Nat} (hact : C.isActive = true)
    (hty : SmbType f.ty) (hnty : SmbType a.nty) (hpre : castToBool a.pre = true)
    (hvar : List.take 1 (List.drop 104 a.pre) = [0xfd])
    (h : run Eval.opExec env (SimpleMulti.suffix ++ k) t (St (f.stack ++ (a.stack ++ S)) A m C kk cs) = r)
    (hr : r.IsOk) :
    ((f.ty = [0x20] ∨ f.ty = [0x22] ∨ f.ty = [0x24]) → ¬ (a.nty = [0x20] ∨ a.nty = [0x22] ∨ a.nty = [0x24])) ∧
      (¬ (f.ty = [0x20] ∨ f.ty = [0x22] ∨ f.ty = [0x24]) → f.ty.headD 0 = a.nty.headD 0 + 1) := by
  rcases hty with hty|hty|hty|hty|hty|hty <;> rcases hnty with hnty|hnty|hnty|hnty|hnty|hnty
  · exact (refuse_20_20 he hact hpre hvar hty hnty h hr).elim
  · simp [hty, hnty]
  · exact (refuse_20_22 he hact hpre hvar hty hnty h hr).elim
  · simp [hty, hnty]
  · exact (refuse_20_24 he hact hpre hvar hty hnty h hr).elim
  · simp [hty, hnty]
  · simp [hty, hnty]
  · exact (refuse_21_21 he hact hpre hvar hty hnty h hr).elim
  · exact (refuse_21_22 he hact hpre hvar hty hnty h hr).elim
  · exact (refuse_21_23 he hact hpre hvar hty hnty h hr).elim
  · exact (refuse_21_24 he hact hpre hvar hty hnty h hr).elim
  · exact (refuse_21_25 he hact hpre hvar hty hnty h hr).elim
  · exact (refuse_22_20 he hact hpre hvar hty hnty h hr).elim
  · simp [hty, hnty]
  · exact (refuse_22_22 he hact hpre hvar hty hnty h hr).elim
  · simp [hty, hnty]
  · exact (refuse_22_24 he hact hpre hvar hty hnty h hr).elim
  · simp [hty, hnty]
  · exact (refuse_23_20 he hact hpre hvar hty hnty h hr).elim
  · exact (refuse_23_21 he hact hpre hvar hty hnty h hr).elim
  · simp [hty, hnty]
  · exact (refuse_23_23 he hact hpre hvar hty hnty h hr).elim
  · exact (refuse_23_24 he hact hpre hvar hty hnty h hr).elim
  · exact (refuse_23_25 he hact hpre hvar hty hnty h hr).elim
  · exact (refuse_24_20 he hact hpre hvar hty hnty h hr).elim
  · simp [hty, hnty]
  · exact (refuse_24_22 he hact hpre hvar hty hnty h hr).elim
  · simp [hty, hnty]
  · exact (refuse_24_24 he hact hpre hvar hty hnty h hr).elim
  · simp [hty, hnty]
  · exact (refuse_25_20 he hact hpre hvar hty hnty h hr).elim
  · exact (refuse_25_21 he hact hpre hvar hty hnty h hr).elim
  · exact (refuse_25_22 he hact hpre hvar hty hnty h hr).elim
  · exact (refuse_25_23 he hact hpre hvar hty hnty h hr).elim
  · simp [hty, hnty]
  · exact (refuse_25_25 he hact hpre hvar hty hnty h hr).elim

end BoltProof.Glue.SimpleMulti
