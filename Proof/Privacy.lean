import Proof.Privacy.Simulator.Arithmetic.PublicHandlerTail
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerDispatch
import Proof.Privacy.Source.SharedRealSourceLower
import Proof.Privacy.Source.SharedPipelineSourceRatio
import Proof.Privacy.Source.SharedCurveIndependentRatio
import Proof.Privacy.Source.SharedHiddenEncSource
import Proof.Privacy.Collision.SharedReconstructedFreshness
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerCode
import Proof.Privacy.Simulator.Arithmetic.OverlayScan
import Proof.Privacy.Simulator.Arithmetic.PointHornerSource
import Proof.Privacy.Simulator.Arithmetic.ClampPoint
import Proof.Privacy.Simulator.Arithmetic.OnlineInputReturn
import Proof.Privacy.Simulator.Arithmetic.PublicWireProtocol
import Proof.Privacy.Source.SharedFullSourceRestTransport
import Proof.Privacy.Source.SharedRealSourceSum
import Proof.Privacy.Source.SharedHiddenSourceTransport
import Proof.Privacy.Source.SharedRetainedProgramRatio
import Proof.Privacy.Source.SharedQueryBudget
import Proof.Privacy.Programming.SharedScheduleFreshness
import Proof.Privacy.Simulator.Arithmetic.OnlineSampling
import Proof.Privacy.Simulator.Arithmetic.StoredForward
import Proof.Privacy.Simulator.Arithmetic.StoredInverse
import Proof.Privacy.Simulator.Arithmetic.InstallFreshLayout
import Proof.Privacy.Simulator.Arithmetic.OnlineInputProtocol
import Proof.Privacy.Simulator.Arithmetic.QueryInputReturn
import Proof.Privacy.Simulator.Arithmetic.SamplerBatch
import Proof.Privacy.Simulator.Arithmetic.OracleMetadata
import Proof.Privacy.Simulator.Arithmetic.SwapMetadata
import Proof.Privacy.Simulator.Arithmetic.KnownQueryBlock
import Proof.Privacy.Source.SharedRetainedPostquery
import Proof.Privacy.Programming.SharedScheduleCounts
import Proof.Privacy.Simulator.Arithmetic.FreshQuerySource
import Proof.Privacy.Programming.SharedScheduleRecords
import Proof.Privacy.Simulator.Arithmetic.QueryInputProtocol
import Proof.Privacy.Simulator.Arithmetic.PointSamplerBlock
import Proof.Privacy.Simulator.Arithmetic.FreshQuery
import Proof.Privacy.Simulator.Arithmetic.PrivateSchedule
import Proof.Privacy.Simulator.Arithmetic.SamplerBatchMemory
import Proof.Privacy.Source.SharedRetainedMass
import Proof.Privacy.Source.SharedActiveMass
import Proof.Privacy.Distribution.SharedProgramQueryMass
import Proof.Privacy.Simulator.Arithmetic.ByteOutputWire
import Proof.Privacy.Simulator.Arithmetic.PrivateSamplers
import Proof.Privacy.Simulator.Arithmetic.OracleScratch
import Proof.Privacy.Simulator.Arithmetic.ByteOutput
import Proof.Privacy.Simulator.Arithmetic.WireCodec
import Proof.Privacy.Simulator.Arithmetic.PointSampler
import Proof.Privacy.Simulator.Arithmetic.KnownQuery
import Proof.Privacy.Simulator.Arithmetic.PairMemory
import Proof.Privacy.Simulator.Arithmetic.SwapBlock
import Proof.Privacy.Bounds.CombinedPrivacy
import Proof.Privacy.Source.SharedRetainedSource
import Proof.Privacy.Source.SharedTranscriptMass
import Proof.Privacy.Collision.SharedPrequeryBound
import Proof.Privacy.Distribution.SharedProgrammingDistribution
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
