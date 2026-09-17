import Proof.Privacy.Simulator.Arithmetic.SwapTable
import Proof.Privacy.Source.SharedAdaptiveRatio
import Proof.Privacy.Simulator.Arithmetic.WordInputBlock
import Proof.Privacy.Simulator.Arithmetic.TableBlock
import Proof.Privacy.Source.SharedBucketCounts
import Proof.Privacy.Simulator.Arithmetic.RuntimeSampler
import Proof.Privacy.Simulator.Arithmetic.WordOutput
import Proof.Privacy.Collision.SharedCrossBranchBound
import Proof.Privacy.Simulator.Arithmetic.SampleToRam
import Proof.Privacy.Simulator.SharedOracleProgram
import Proof.Privacy.Simulator.SharedSimulator
import Proof.Privacy.Programming.SharedGate
import Proof.Privacy.Collision.SharedGateAssignment
import Proof.Privacy.Collision.SharedBranchCollision
import Proof.Privacy.Simulator.SimulatorActualImplementation
import Proof.Privacy.Simulator.SimulatorChallengePrivacy
import Construction
import Solution
import Proof.Correctness
import Proof.Privacy.ConcreteSmallSourceRatio
import Proof.Privacy.PaperConstruction
import Proof.Privacy.Simulator.SimulatorTotalImplementation

namespace Kriterion.ArgoMAC.Security

open BN254

/-- This is the adaptive-privacy field of the obligation for the ArgoMAC construction. -/
def AdaptivePrivacy : Prop :=
  ∀ (field : FieldCertificate) (group : @GroupCertificate field),
    ∃ simulator : GarbledCircuit.Simulator AffineInput (Option (@Point field)) Pipeline.Table
      Garbling.Labels Garbling.Topology CircuitSimulatorState,
      GarbledCircuit.ConcreteAdaptivePrivacy (Aux := Unit)
        (@Garbling.garbledCircuit field group construction) Garbling.topology simulator
        (@uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance)
          (Seed.randomness 0))
        Garbling.oracleHandler circuitSimulatorOracleHandler 100

/-- The checked simulator gives the required universal privacy bound. -/
theorem adaptivePrivacy : AdaptivePrivacy := by
  intro field group
  letI := field
  letI := group
  refine ⟨concreteCircuitSimulator, ?_⟩
  have instances : (@Fintype.ofFinite Garbling.Randomness inferInstance) =
      garblingRandomnessFintype := Subsingleton.elim _ _
  have tapes : @uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance)
      (Seed.randomness 0) = randomTape (Seed.randomness 0) := by
    unfold uniformRandomTape randomTape
    rw [Cryptography.uniformTape_eq, instances]
  rw [tapes]
  exact concreteAdaptivePrivacy (Seed.randomness 0)

/-- The circuit topology does not depend on the scalar. -/
theorem topologyConstant (first second : NonZeroScalar) :
    Garbling.topology first = Garbling.topology second := rfl

end Kriterion.ArgoMAC.Security
