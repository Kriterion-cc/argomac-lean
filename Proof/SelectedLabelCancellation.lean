import Proof.ValidSourceKernel

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The fixed transcript label guard cancels the selected-label source density. -/
theorem selectedLabel_density_cancel [Fintype Block]
    (input : AffineInput) (mac : InputMac)
    (weight : (EncPRF.PermutationIndex → Block) → ℝ≥0∞) :
    (∑' key, (PMF.uniformOfFintype InputMacKey) key *
      if key.encodeAffine input = mac then
        (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞) *
          weight (inputMacCoordinateEquiv (key.encodeAffine input)) else 0) =
      weight (inputMacCoordinateEquiv mac) := by
  have fiber := congrArg (fun distribution : PMF (EncPRF.PermutationIndex → Block) =>
    distribution (inputMacCoordinateEquiv mac)) (map_uniform_selectedLabels input)
  dsimp only at fiber
  rw [PMF.map_apply, PMF.uniformOfFintype_apply] at fiber
  have selected (key : InputMacKey) :
      inputMacCoordinateEquiv mac = inputMacCoordinateEquiv (key.encodeAffine input) ↔
        key.encodeAffine input = mac := inputMacCoordinateEquiv.injective.eq_iff.trans eq_comm
  simp only [selected] at fiber
  have each (key : InputMacKey) :
      (PMF.uniformOfFintype InputMacKey) key *
        (if key.encodeAffine input = mac then
          (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞) *
            weight (inputMacCoordinateEquiv (key.encodeAffine input)) else 0) =
      (if key.encodeAffine input = mac then (PMF.uniformOfFintype InputMacKey) key else 0) *
        ((Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞) * weight (inputMacCoordinateEquiv mac)) := by
    by_cases same : key.encodeAffine input = mac <;> simp only [same, if_true, if_false, mul_zero, zero_mul]
  simp_rw [each]
  rw [ENNReal.tsum_mul_right, fiber, ← mul_assoc]
  have nonzero : (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := EncPRF.PermutationIndex → Block)
  rw [ENNReal.inv_mul_cancel nonzero (ENNReal.natCast_ne_top _), one_mul]

end
end Kriterion.ArgoMAC.Security
