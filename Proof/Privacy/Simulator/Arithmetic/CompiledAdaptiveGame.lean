import Proof.Privacy.Source.StrictWirePrivacy
import Proof.Privacy.Simulator.Arithmetic.CompiledSetupJoint
import Proof.Privacy.Simulator.StrictOracleLaw
import Proof.Privacy.Simulator.Arithmetic.OnlineLazyDecision
import Architect

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security
noncomputable section

/-- The supported online law closes the complete fixed-oracle experiment. -/
@[blueprint "ArithmeticSimulator.lazyCompiledIdealGame_finiteSource"
  (statement := /-- If the online phase of the compiled machine equals, for every setup in the support of
    $\mathsf{Sim}_1$, the strict frame decision of $\mathsf{Sim}_2$ after the public completion of
    the permutation, then the ideal world of the machine equals the strict simulator. -/)
  (title := /-- BABE Construction~3 -/)]
theorem lazyCompiledIdealGame_finiteSource [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (online : ∀ memory coin, (memory, coin) ∈ (lazySetupJoint parameter).support →
      lazyChosenDecision lazyCompiledMachine adversary parameter scalar auxiliary memory
        (publicSourceTable coin.1) LazyOracle.empty =
      (OperationalOracle.publicCompletion
        (LazyOracle.empty : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind fun oracle =>
        sharedStrictFrameDecision (SimulatorSampling.online.total 256).law (sharedWireAdversary adversary)
          parameter scalar auxiliary (Shared.Simulator.initialState coin oracle)) :
    GarbledCircuit.LazySimulatorProtocol.idealGame Shared.programCircuit Wire.encoding 9806076
      lazyCompiledMachine adversary parameter scalar auxiliary =
    sharedStrictSourceDecision (SimulatorSampling.offline.total 256).law
      (SimulatorSampling.online.total 256).law (sharedWireAdversary adversary) parameter scalar auxiliary := by
  /-- Split the parsed game into the setup and online phases and rewrite the setup with
    \cref{ArithmeticSimulator.lazySetupJoint_parsed}. Replace the online decision on the support of
    the setup by the premise. The result is the strict simulator over the joint setup law. -/
  rw [lazyParsedGame_phases, lazySetupJoint_parsed, PMF.bind_map]
  dsimp only [Function.comp_def]
  have law : (lazySetupJoint parameter).bind (fun setup =>
      lazyChosenDecision lazyCompiledMachine adversary parameter scalar auxiliary setup.1
        (publicSourceTable setup.2.1) LazyOracle.empty) =
    (lazySetupJoint parameter).bind (fun setup =>
      (OperationalOracle.publicCompletion
        (LazyOracle.empty : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind fun oracle =>
        sharedStrictFrameDecision (SimulatorSampling.online.total 256).law (sharedWireAdversary adversary)
          parameter scalar auxiliary (Shared.Simulator.initialState setup.2 oracle)) := by
    apply ThreePhase.bind_eq_on_support
    intro setup member
    exact online setup.1 setup.2 member
  rw [law]
  unfold sharedStrictSourceDecision
  rw [← lazySetupJoint_source parameter, PMF.bind_map]
  rfl

end
end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security Security.OperationalOracle
noncomputable section

/-- The choose phase preserves the fixed-oracle completion law for every continuation. -/
theorem lazyChoose_completion {Result : Type} {budget : Nat}
    (program : OracleProgram sharedRealOracleSpec Result budget)
    (state : Shared.Simulator.OracleState)
    (lazy : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (next : Result → LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex → PMF Bool)
    (observe : Result → PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex →
      List (PermutationRecord Shared.FixedKeyIndex Block) → PMF Bool)
    (matching : HistoryMatches lazy state.fixedTranscript)
    (continuation : ∀ value updated history, HistoryMatches updated history →
      next value updated = (publicCompletion updated).bind (fun oracle => observe value oracle history)) :
    (LazyOracle.run program lazy).bind (fun result => next result.1 result.2) =
      (publicCompletion lazy).bind (fun oracle =>
        (program.run idealOracleHandler
          {state with fixedOracle := oracle.1, encOracle := oracle.2.1, hashOracle := oracle.2.2}).bind
          (fun result => observe result.1
            (result.2.fixedOracle, result.2.encOracle, result.2.hashOracle) result.2.fixedTranscript)) := by
  have completed := congrArg (fun distribution => distribution.bind
    (fun result => observe result.1 result.2.1 result.2.2))
    (shared_public_completion program state lazy)
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at completed
  rw [completed]
  rw [← tracked_run_erase program (lazy, state.fixedTranscript), PMF.bind_map]
  apply ThreePhase.bind_eq_on_support
  intro result member
  exact continuation result.1 result.2.1 result.2.2
    (history_run program (lazy, state.fixedTranscript) matching result member)

end
end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security

/-- Public queries preserve the source's abort flag. -/
theorem sharedPublicRun_bad {Result : Type} {budget : Nat}
    (program : OracleProgram sharedRealOracleSpec Result budget) (state : Shared.Simulator.OracleState)
    (result : Result × Shared.Simulator.OracleState)
    (member : result ∈ (program.run idealOracleHandler state).support) : result.2.bad = state.bad :=
  ThreePhase.run_preserves idealOracleHandler (fun current : Shared.Simulator.OracleState => current.bad)
    (by intro query current; cases query <;> rfl) program state result member

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.OperationalOracle
noncomputable section
set_option maxRecDepth 4096

set_option backward.isDefEq.respectTransparency false in
/-- The choose phase keeps only the oracle fields that affect the strict decision. -/
@[blueprint "ArithmeticSimulator.lazyChosenDecision_completion"
  (statement := /-- The choose phase keeps only the permutation fields that affect the strict decision. If the
    parsed online phase has the completed strict law for every chosen input, then the chosen
    decision of the machine equals the strict frame decision of $\mathsf{Sim}_2$ after the public
    completion. -/)
  (title := /-- BABE Construction~3 -/)]
theorem lazyChosenDecision_completion [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (memory : Memory) (coin : SimulatorSampling.OfflineCoin)
    (online : ∀ (selected : AffineInput × adversary.State) updated history, HistoryMatches updated history →
      ((lazyParsedOnline lazyCompiledMachine memory selected.1
        (Shared.programCircuit.function scalar selected.1) updated).bind fun encoded => match encoded with
        | none => PMF.pure false
        | some encoded => (LazyOracle.run
            (adversary.decide parameter (publicSourceTable coin.1) encoded.1 auxiliary selected.2) encoded.2).map Prod.fst) =
      (publicCompletion updated).bind fun complete =>
        (SimulatorSampling.online.total 256).law.bind fun random =>
          let next := sharedProgramSelectedGateView
            {(sharedOfflineFrame coin).oracle with
              fixedOracle := complete.1
              encOracle := complete.2.1
              hashOracle := complete.2.2
              fixedTranscript := history}
            selected.1 (coin.2.1.encodeAffine selected.1)
            ((sharedOfflineFrame coin).selectedCurve selected.1,
              (checkedScalarMultiplication scalar.value selected.1).map fun point =>
                (sharedOfflineFrame coin).selectedPoints selected.1 point (Vector.ofFn random.1) random.2)
          if next.bad then PMF.pure false else
            ((adversary.decide parameter (publicSourceTable coin.1)
              (Lamport.selectedLabels (coin.2.1.encodeAffine selected.1)) auxiliary selected.2).run
                idealOracleHandler next).map Prod.fst) :
    lazyChosenDecision lazyCompiledMachine adversary parameter scalar auxiliary memory
      (publicSourceTable coin.1) LazyOracle.empty =
      (publicCompletion (LazyOracle.empty : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind
        fun complete => sharedStrictFrameDecision (SimulatorSampling.online.total 256).law
          (sharedWireAdversary adversary) parameter scalar auxiliary (Shared.Simulator.initialState coin complete) := by
  /-- Complete the choose phase with the online premise. The chosen decision unfolds to the same bind
    on the support. The strict frame decision agrees with the completed run because the public run
    keeps the bad flag false. -/
  have completed := lazyChoose_completion (adversary.chooseInput parameter (publicSourceTable coin.1) auxiliary)
    (sharedOfflineFrame coin).oracle LazyOracle.empty _ _ history_empty online
  refine Eq.trans ?_ (completed.trans ?_)
  · unfold lazyChosenDecision
    apply ThreePhase.bind_eq_on_support
    intro selected _
    apply ThreePhase.bind_eq_on_support
    intro encoded _
    cases encoded <;> rfl
  · apply ThreePhase.bind_eq_on_support
    intro complete _
    unfold sharedStrictFrameDecision
    change ((adversary.chooseInput parameter (publicSourceTable coin.1) auxiliary).run idealOracleHandler
      (Shared.Simulator.initialState coin complete).oracle).bind _ =
      ((adversary.chooseInput parameter (publicSourceTable coin.1) auxiliary).run idealOracleHandler
      (Shared.Simulator.initialState coin complete).oracle).bind _
    apply ThreePhase.bind_eq_on_support
    intro selected member
    apply ThreePhase.bind_eq_on_support
    intro random _
    apply sharedStrictViewDecision_congr
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (sharedPublicRun_bad _ _ selected member).symm

end
end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.OperationalOracle
noncomputable section

/-- The actual closed simulator has the complete finite strict-source decision law. -/
@[blueprint "ArithmeticSimulator.lazyCompiledIdealGame_eqStrict"
  (statement := /-- The compiled machine implements the strict simulator. The ideal world of the compiled machine
    equals the ideal world of $(\mathsf{Sim}_1, \mathsf{Sim}_2)$ (Construction~3) with $256$
    attempts per draw. -/)
  (title := /-- BABE Construction~3 -/)]
theorem lazyCompiledIdealGame_eqStrict [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    GarbledCircuit.LazySimulatorProtocol.idealGame Shared.programCircuit Wire.encoding 9806076
      lazyCompiledMachine adversary parameter scalar auxiliary =
    sharedStrictSourceDecision (SimulatorSampling.offline.total 256).law
      (SimulatorSampling.online.total 256).law (sharedWireAdversary adversary) parameter scalar auxiliary := by
  /-- Apply \cref{ArithmeticSimulator.lazyCompiledIdealGame_finiteSource}. For each setup in the
    support, apply \cref{ArithmeticSimulator.lazyChosenDecision_completion}. The online premise is
    \cref{ArithmeticSimulator.lazyCompiledOnline_decision} with the offline coin stored in memory. -/
  apply lazyCompiledIdealGame_finiteSource
  intro memory coin member
  apply lazyChosenDecision_completion
  intro selected updated history matching
  exact lazyCompiledOnline_decision memory selected.1 (Shared.programCircuit.function scalar selected.1)
    coin (lazySetupJoint_words parameter memory coin member)
    {(sharedOfflineFrame coin).oracle with fixedTranscript := history} updated matching rfl
    (fun labels => adversary.decide parameter (publicSourceTable coin.1) labels auxiliary selected.2)

/-- The closed simulator proves the public privacy obligation without hardness axioms. -/
@[blueprint "ArithmeticSimulator.lazyCompiledAdaptivePrivacy"
  (statement := /-- Adaptive privacy of the optimized garbling scheme (Theorem~8) at the concrete level of Lemma~14.
    The compiled simulator $(\mathsf{Sim}_1, \mathsf{Sim}_2)$ proves the public privacy obligation
    for the program circuit, the Lamport wire encoding, the ciphertext size $9806076$ bytes, and the
    uniform private tape: every adversary with work $T$ has advantage $\delta$ with $T / \delta \geq
    2^{100}$. The proof uses no hardness assumption beyond the programmable random permutation
    model. -/)
  (title := /-- BABE Theorem~8 -/)
  (proof := /-- Apply \cref{Security.sharedStrictOraclePrivacy} to the compiled machine.
    \Cref{ArithmeticSimulator.lazyCompiledIdealGame_eqStrict} shows that the machine implements the
    strict simulator. -/)]
theorem lazyCompiledAdaptivePrivacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    [Fintype Shared.PrivateCoins] (witness : Shared.Randomness) :
    GarbledCircuit.OracleAdaptivePrivacy Shared.programCircuit Wire.encoding 9806076
      (uniformRandomTape Shared.PrivateCoins (Shared.privateCoins witness))
      (fun parameter scalar random => (Shared.garbleProgram parameter scalar random).toOracleProgram) :=
  sharedStrictOraclePrivacy witness lazyCompiledMachine
    (fun adversary parameter scalar => lazyCompiledIdealGame_eqStrict adversary parameter scalar ())

end
end Kriterion.ArgoMAC.ArithmeticSimulator
