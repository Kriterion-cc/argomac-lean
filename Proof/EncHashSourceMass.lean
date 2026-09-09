import Proof.EncPRFTranscript
import Proof.HiddenHashSource

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A compatible EncPRF reference separates the changed EncPRF constraints. -/
theorem realTranscript_update_enc_factor (randomness : Garbling.Randomness)
    (oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (reference : PermutationTranscriptMatches randomness.encPRFOracle
      (encOracleTranscriptRecords transcript)) :
    OracleTranscriptCompatible Garbling.oracleHandler {randomness with encPRFOracle := oracle} transcript ↔
      OracleTranscriptCompatible Garbling.oracleHandler randomness transcript ∧
        PermutationTranscriptMatches oracle (encOracleTranscriptRecords transcript) := by
  constructor
  · intro compatible
    have original := (realTranscript_update_enc_iff
      {randomness with encPRFOracle := oracle} randomness.encPRFOracle transcript compatible).mpr reference
    have matching := (realTranscript_update_enc_iff
      {randomness with encPRFOracle := oracle} oracle transcript compatible).mp compatible
    exact ⟨original, matching⟩
  · rintro ⟨compatible, matching⟩
    exact (realTranscript_update_enc_iff randomness oracle transcript compatible).mpr matching

/-- One EncPRF transcript factor preserves every hash-dependent source weight. -/
theorem encHashTranscript_weighted_eq [Fintype Block] [Fintype BaseField]
    (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (reference : PermutationTranscriptMatches randomness.encPRFOracle
      (encOracleTranscriptRecords transcript))
    (weight : EncPRF.HashOracle → ℝ≥0∞) :
    encTranscriptFactor (encOracleTranscriptRecords transcript) *
      (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        if OracleTranscriptCompatible Garbling.oracleHandler
          {randomness with hashOracle := hash} transcript then weight hash else 0) =
    ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
      ∑' oracle : PermutationOracle EncPRF.PermutationIndex Block,
        (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) oracle *
          if OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with encPRFOracle := oracle, hashOracle := hash} transcript
          then weight hash else 0 := by
  classical
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro hash
  have separate (oracle : PermutationOracle EncPRF.PermutationIndex Block) :=
    realTranscript_update_enc_factor {randomness with hashOracle := hash} oracle transcript reference
  conv_rhs =>
    arg 2
    arg 1
    ext oracle
    arg 2
    rw [separate oracle]
  by_cases compatible : OracleTranscriptCompatible Garbling.oracleHandler
      {randomness with hashOracle := hash} transcript
  · simp only [compatible, if_true, true_and]
    rw [← encTranscriptFactor_eq_mass randomness.encPRFOracle _ reference,
      PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro oracle
    by_cases matching : PermutationTranscriptMatches oracle (encOracleTranscriptRecords transcript)
    · simp [Set.indicator, matching, mul_assoc, mul_comm, mul_left_comm]
    · simp [Set.indicator, matching]
  · simp [compatible]

end

end Kriterion.ArgoMAC.Security
