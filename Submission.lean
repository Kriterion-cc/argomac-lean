/-
This file is the entry point of the submission.
`challenge.yaml` names `Submission.solution` as the entry.
`adaptivePrivacy` proves the universal privacy field.
`solution` supplies the verifier and metric entry.
-/

import Solution
import Construction
import Proof

namespace Submission

open Kriterion Kriterion.BN254 Kriterion.ArgoMAC

/-- This is the adaptive-privacy field of the obligation for the ArgoMAC construction. -/
def AdaptivePrivacy : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field),
    ∃ simulator : GarbledCircuit.Simulator AffineInput (Option (@Point field)) Pipeline.Table
      Garbling.Labels Garbling.Topology Security.CircuitSimulatorState,
      GarbledCircuit.ConcreteAdaptivePrivacy (Aux := Unit)
        (@Garbling.garbledCircuit field group construction) Garbling.topology simulator
        (@uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance)
          (Seed.randomness 0))
        Garbling.oracleHandler Security.circuitSimulatorOracleHandler 100

/-- The checked simulator gives the required universal privacy bound. -/
theorem adaptivePrivacy : AdaptivePrivacy := by
  intro field group
  letI := field
  letI := group
  refine ⟨Security.concreteCircuitSimulator, ?_⟩
  have instances : (@Fintype.ofFinite Garbling.Randomness inferInstance) =
      Security.garblingRandomnessFintype := Subsingleton.elim _ _
  have tapes : @uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance)
      (Seed.randomness 0) = Security.randomTape (Seed.randomness 0) := by
    unfold uniformRandomTape Security.randomTape
    rw [Cryptography.uniformTape_eq, instances]
  rw [tapes]
  exact Security.concreteAdaptivePrivacy (Seed.randomness 0)

/-- The supplied privacy proof closes every obligation field. -/
def solutionOf (privacy : AdaptivePrivacy) : Kriterion.Solution := {
  oracle := Garbling.oracleSpec
  Randomness := Garbling.Randomness
  randomnessFinite := inferInstance
  Public := Pipeline.Table
  EncodingKey := Garbling.EncodingKey
  Labels := Garbling.Labels
  EvaluationOracle := Garbling.EvaluationOracle
  Topology := Garbling.Topology
  State := Security.CircuitSimulatorState
  randomness := Seed.randomness 0
  encoding := Wire.encoding
  ciphertextBytes := 9699931
  scheme := fun field group => @Garbling.garbledCircuit field group construction
  ciphertextSize := by
    intro field group parameter scalar randomness
    dsimp only [Garbling.garbledCircuit]
    have size := Wire.garble_length construction scalar randomness
    simpa only [Garbling.PublicCircuit] using size
  lamportCompatible := fun field group => @Lamport.compatible field group
  evaluationOracle := fun randomness =>
    (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)
  topology := Garbling.topology
  topologyConstant := fun _ _ => rfl
  realOracle := Garbling.oracleHandler
  idealOracle := Security.circuitSimulatorOracleHandler
  functionCorrect := fun _ _ _ _ => rfl
  perfectCorrectness := fun field group => @RCBComplete.perfectCorrectness field group _
  adaptivePrivacy := privacy
}

/-- The verifier and metric use this computable entry. -/
def solution : Kriterion.Solution := solutionOf adaptivePrivacy

end Submission
