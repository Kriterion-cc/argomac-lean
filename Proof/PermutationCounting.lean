import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Set
import Mathlib.Probability.Distributions.Uniform

namespace Kriterion.ArgoMAC.Security

noncomputable section

open scoped ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The count depends only on the number of constrained inputs. -/
theorem compatiblePermutation_count (s t : Set α) [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] (e : s ≃ t) :
    Fintype.card {π : Equiv.Perm α // ∀ x : s, π x = e x} =
      (Fintype.card α - Fintype.card s).factorial := by
  classical
  calc
    _ = Fintype.card (↑sᶜ ≃ ↑tᶜ) := Fintype.card_congr (Equiv.Set.compl e)
    _ = (Fintype.card ↑sᶜ).factorial := Fintype.card_equiv e.toCompl
    _ = _ := congrArg Nat.factorial (Fintype.card_compl_set s)

/-- A uniform permutation has the factorial ratio as its assignment mass. -/
theorem compatiblePermutation_mass (s t : Set α) [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] (e : s ≃ t) :
    (PMF.uniformOfFintype (Equiv.Perm α)).toOuterMeasure
        {π | ∀ x : s, π x = e x} =
      ((Fintype.card α - Fintype.card s).factorial : ℝ≥0∞) /
        (Fintype.card α).factorial := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [Fintype.card_perm]
  congr 1
  exact congrArg (fun n : ℕ => (n : ℝ≥0∞)) (compatiblePermutation_count s t e)

/-- Every injective assignment has the same mass for a fixed input set. -/
theorem injectiveAssignment_mass (s : Set α) [DecidablePred (· ∈ s)]
    (f : s → α) (hf : Function.Injective f) :
    (PMF.uniformOfFintype (Equiv.Perm α)).toOuterMeasure {π | ∀ x : s, π x = f x} =
      ((Fintype.card α - Fintype.card s).factorial : ℝ≥0∞) /
        (Fintype.card α).factorial := by
  classical
  exact compatiblePermutation_mass s (Set.range f) (Equiv.ofInjective f hf)

end

end Kriterion.ArgoMAC.Security
