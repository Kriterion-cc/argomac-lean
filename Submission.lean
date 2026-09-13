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

abbrev AdaptivePrivacy := Security.AdaptivePrivacy

theorem adaptivePrivacy : AdaptivePrivacy := Security.adaptivePrivacy

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
    simpa only [Garbling.PublicCircuit] using
      (@Wire.ciphertextSize field group parameter scalar randomness)
  lamportCompatible := fun field group => @Lamport.compatible field group
  evaluationOracle := fun randomness =>
    (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)
  topology := Garbling.topology
  topologyConstant := Security.topologyConstant
  realOracle := Garbling.oracleHandler
  idealOracle := Security.circuitSimulatorOracleHandler
  functionCorrect := fun field group => @functionCorrect field group
  perfectCorrectness := fun field group => @perfectCorrectness field group
  adaptivePrivacy := privacy
}

/-- The verifier and metric use this computable entry. -/
def solution : Kriterion.Solution := solutionOf adaptivePrivacy

end Submission
