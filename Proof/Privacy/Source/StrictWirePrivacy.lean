import Proof.Privacy.Source.StrictSourceSampling
import Proof.Privacy.Simulator.SharedChallengePrivacy
import Proof.SharedOracle
import Architect

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions GarbledCircuit
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The wire source has the same strict privacy error. -/
@[blueprint "Security.sharedStrictWireAdvantage_envelope"
  (statement := /-- For $q \leq 2^{101}$, the advantage between the real world of the wire circuit and the exact
    strict simulator is at most $\varepsilon_3(q) = (251850146 + 833\,q) / 2^{128}$, the Lean
    counterpart of the bucketed bound of Lemma~14. -/)
  (title := /-- BABE Lemma~14 -/)]
theorem sharedStrictWireAdvantage_envelope [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type}
    (adversary : AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table LamportSignature Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter ≤ 2 ^ 101) :
    advantage
      (realGame Shared.wireCircuit (uniformRandomTape Shared.Randomness witness)
        sharedRealOracleHandler adversary parameter scalar auxiliary)
      (sharedStrictSourceDecision SimulatorSampling.offline.law SimulatorSampling.online.law
        (sharedWireAdversary adversary) parameter scalar auxiliary) ≤
      adaptiveErrorEnvelope (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) := by
  /-- Rewrite the exact strict simulator. Apply \cref{Security.sharedStrictAdaptiveAdvantage_envelope}
    to the wire adversary. The wire circuit is the internal circuit with Lamport-mapped labels, so
    the two real worlds agree. -/
  rw [sharedStrictSourceDecision_exact]
  have bound := sharedStrictAdaptiveAdvantage_envelope (sharedWireAdversary adversary)
    parameter auxiliary scalar witness small
  simpa only [realGame, sharedWireAdversary, Shared.wireCircuit, sharedInternalCircuit,
    Lamport.wireCircuit, GarbledCircuit.mapLabels, PMF.bind_map, Function.comp_def,
    Garbling.topology] using bound

/-- The finite private samplers preserve the required work bound. -/
@[blueprint "Security.sharedStrictWirePrivacy"
  (statement := /-- Concrete adaptive privacy (Lemma~14). For every adversary with query budget $q$, the advantage
    $\delta$ between the real world of the wire circuit and the strict simulator with $256$ attempts
    per draw satisfies $(q + 1) / \delta \geq 2^{100}$. -/)
  (title := /-- BABE Lemma~14 -/)]
theorem sharedStrictWirePrivacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type}
    (adversary : AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table LamportSignature Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness) :
    WorkPerAdvantage 100 (adversaryWork adversary parameter)
      (advantage
        (realGame Shared.wireCircuit (uniformRandomTape Shared.Randomness witness)
          sharedRealOracleHandler adversary parameter scalar auxiliary)
        (sharedStrictSourceDecision (SimulatorSampling.offline.total 256).law
          (SimulatorSampling.online.total 256).law (sharedWireAdversary adversary)
          parameter scalar auxiliary)) := by
  /-- Let $q$ be the total query budget. Transfer the advantage through the exact strict simulator. If
    $q < 2^{101}$, apply \cref{Security.sharedErrors_has100Bits} with
    \cref{Security.sharedStrictWireAdvantage_envelope} and
    \cref{Security.sharedStrictSourceDecision_allowance}. Otherwise apply
    \cref{Security.sharedLargeBudget_has100Bits}. -/
  let queries := adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter
  change WorkPerAdvantage 100 (queries + 1) _
  apply adaptivePrivacyTransfer (ideal := sharedStrictSourceDecision SimulatorSampling.offline.law
    SimulatorSampling.online.law (sharedWireAdversary adversary) parameter scalar auxiliary)
  by_cases small : queries < 2 ^ 101
  · apply sharedErrors_has100Bits queries
    · exact sharedStrictWireAdvantage_envelope adversary parameter auxiliary scalar witness (Nat.le_of_lt small)
    · exact sharedStrictSourceDecision_allowance (sharedWireAdversary adversary) parameter scalar auxiliary
  · exact sharedLargeBudget_has100Bits _ _ _ queries (Nat.le_of_not_gt small)

/-- A closed implementation of the finite source meets the public privacy rule. -/
@[blueprint "Security.sharedStrictOraclePrivacy"
  (statement := /-- A closed implementation of the strict simulator meets the privacy rule of Definition~3. If a
    bounded machine implements the ideal world of $(\mathsf{Sim}_1, \mathsf{Sim}_2)$ with $256$
    sampling attempts per draw, then the program circuit satisfies oracle adaptive privacy with $T /
    \delta \geq 2^{100}$. -/)
  (title := /-- BABE Theorem~8 -/)]
theorem sharedStrictOraclePrivacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    [Fintype Shared.PrivateCoins] (witness : Shared.Randomness)
    (simulator : BoundedMachine.Simulator)
    (implementation : ∀ (adversary : AdaptiveAdversary sharedRealOracleSpec
        AffineInput Pipeline.Table LamportSignature Unit) parameter scalar,
      LazySimulatorProtocol.idealGame Shared.programCircuit Wire.encoding 9806076 simulator
        adversary parameter scalar () =
      sharedStrictSourceDecision (SimulatorSampling.offline.total 256).law
        (SimulatorSampling.online.total 256).law (sharedWireAdversary adversary)
        parameter scalar ()) :
    OracleAdaptivePrivacy Shared.programCircuit Wire.encoding 9806076
      (uniformRandomTape Shared.PrivateCoins (Shared.privateCoins witness))
      (fun parameter scalar random => (Shared.garbleProgram parameter scalar random).toOracleProgram) := by
  /-- Use the given machine as the simulator. Rewrite the real world with
    \cref{Security.OperationalOracle.shared_lazy_real} and the ideal world with the implementation
    premise. Apply \cref{Security.sharedStrictWirePrivacy} to the machine adversary. The machine
    step count $T$ dominates the query budget. -/
  refine ⟨simulator, fun machine parameter scalar => ?_⟩
  dsimp only
  rw [OperationalOracle.shared_lazy_real, implementation]
  apply le_trans (sharedStrictWirePrivacy (machineAdversary Wire.encoding machine)
    parameter () scalar witness)
  apply Nat.cast_le.mpr
  simp only [adversaryWork, machineAdversary, BoundedMachine.Adversary.steps]
  omega

end
end Kriterion.ArgoMAC.Security
