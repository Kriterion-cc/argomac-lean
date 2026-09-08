/-
This file is the entry point of the submission.
`challenge.yaml` names `Submission.solution` as the entry.
`solutionOf` closes every obligation field except adaptive privacy.
`solution` appears when `AdaptivePrivacy` is proved.
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

/-- Every field except adaptive privacy is closed. -/
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
  randomnessFromSeed := Seed.randomness
  benchmarkGarble := fun _ scalar randomness => Garbling.garble construction scalar randomness
  scheme := fun field group => @Garbling.garbledCircuit field group construction
  benchmarkGarble_eq := fun _ _ => rfl
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

end Submission
