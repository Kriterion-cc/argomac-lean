import Proof.HiddenEncPRFGame
import Security.AdaptivePrivacy

namespace Kriterion.ArgoMAC.Security

open Cryptography

/-- This operation adds unused query capacity. -/
def padOracleProgram {oracle : OracleSpec} {Result : Type} (extra : Nat) :
    {budget : Nat} → OracleProgram oracle Result budget → OracleProgram oracle Result (extra + budget)
  | _, .pure distribution => .pure distribution
  | _, .query request next => .query request (fun answer => padOracleProgram extra (next answer))
  | _, .sample distribution next => .sample distribution (fun value => padOracleProgram extra (next value))

/-- Unused query capacity does not change the program run. -/
theorem padOracleProgram_run {oracle : OracleSpec} {Result State : Type}
    (handler : OracleHandler oracle State) (extra : Nat) {budget : Nat}
    (program : OracleProgram oracle Result budget) (state : State) :
    (padOracleProgram extra program).run handler state = program.run handler state := by
  induction program generalizing state with
  | pure distribution => rfl
  | query request next ih => exact ih _ _
  | sample distribution next ih =>
      simp only [padOracleProgram, OracleProgram.run]
      apply congrArg distribution.bind
      funext value
      exact ih value state

/-- This program runs both adaptive phases under their combined query budget. -/
def appendOracleProgram {oracle : OracleSpec} {First Second : Type} {secondBudget : Nat}
    (next : First → OracleProgram oracle Second secondBudget) :
    {firstBudget : Nat} → OracleProgram oracle First firstBudget →
      OracleProgram oracle Second (firstBudget + secondBudget)
  | firstBudget, .pure distribution =>
      .sample distribution (fun value => padOracleProgram firstBudget (next value))
  | Nat.succ firstBudget, .query request continuation =>
      (Nat.add_right_comm firstBudget secondBudget 1) ▸
        (OracleProgram.query request fun answer => appendOracleProgram next (continuation answer))
  | _, .sample distribution continuation =>
      .sample distribution (fun value => appendOracleProgram next (continuation value))

/-- The combined program has the exact two-phase state and result distribution. -/
theorem appendOracleProgram_run {oracle : OracleSpec} {First Second State : Type}
    (handler : OracleHandler oracle State) {firstBudget secondBudget : Nat}
    (first : OracleProgram oracle First firstBudget)
    (next : First → OracleProgram oracle Second secondBudget) (state : State) :
    (appendOracleProgram next first).run handler state =
      (first.run handler state).bind (fun selected => (next selected.1).run handler selected.2) := by
  induction first generalizing state with
  | pure distribution =>
      simp only [appendOracleProgram, OracleProgram.run, PMF.bind_map,
        Function.comp_def, padOracleProgram_run]
  | query request continuation ih =>
      simp only [appendOracleProgram]
      have castRun {left right : Nat} (equal : left = right)
          (program : OracleProgram oracle Second left) :
          (equal ▸ program).run handler state = program.run handler state := by
        cases equal
        rfl
      rw [castRun]
      exact ih _ _
  | sample distribution continuation ih =>
      simp only [appendOracleProgram, OracleProgram.run, PMF.bind_bind]
      apply congrArg distribution.bind
      funext value
      exact ih value state

/-- This program gives an adaptive adversary its selected labels between both phases. -/
def adaptiveDecisionProgram {oracle : OracleSpec} {Input Public Labels Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (table : Public) (auxiliary : Aux) (labels : Input → Labels) :
    OracleProgram oracle Bool
      (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) :=
  appendOracleProgram (fun selected =>
    adversary.decide parameter table (labels selected.1) auxiliary selected.2)
    (adversary.chooseInput parameter table auxiliary)

/-- The combined adaptive program gives the exact decision law with the original oracle state. -/
theorem adaptiveDecisionProgram_run {oracle : OracleSpec} {Input Public Labels Aux State : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (table : Public) (auxiliary : Aux) (labels : Input → Labels)
    (handler : OracleHandler oracle State) (state : State) :
    (adaptiveDecisionProgram adversary parameter table auxiliary labels).run handler state =
      ((adversary.chooseInput parameter table auxiliary).run handler state).bind
        (fun selected => (adversary.decide parameter table (labels selected.1.1)
          auxiliary selected.1.2).run handler selected.2) :=
  appendOracleProgram_run handler _ _ state

/-- The real decision game uses the exact combined adaptive program. -/
theorem realGame_adaptiveDecisionProgram {oracle : OracleSpec}
    {Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle Aux : Type}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
    (randomTape : Nat → PMF Randomness) (handler : OracleHandler oracle Randomness)
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    GarbledCircuit.realGame scheme randomTape handler adversary parameter circuit auxiliary =
      (randomTape parameter).bind (fun randomness =>
        ((adaptiveDecisionProgram adversary parameter (scheme.garble parameter circuit randomness).1
          auxiliary (scheme.encode (scheme.garble parameter circuit randomness).2)).run
          handler randomness).map Prod.fst) := by
  simp only [GarbledCircuit.realGame, adaptiveDecisionProgram_run, PMF.map_bind]

/-- This operation changes only the result of an oracle program. -/
noncomputable def mapOracleProgram {oracle : OracleSpec} {First Second : Type} (mapResult : First → Second) :
    {budget : Nat} → OracleProgram oracle First budget → OracleProgram oracle Second budget
  | _, .pure distribution => .pure (distribution.map mapResult)
  | _, .query request next => .query request (fun answer => mapOracleProgram mapResult (next answer))
  | _, .sample distribution next => .sample distribution (fun value => mapOracleProgram mapResult (next value))

/-- The result map preserves every oracle state transition. -/
theorem mapOracleProgram_run {oracle : OracleSpec} {First Second State : Type}
    (mapResult : First → Second) (handler : OracleHandler oracle State) {budget : Nat}
    (program : OracleProgram oracle First budget) (state : State) :
    (mapOracleProgram mapResult program).run handler state =
      (program.run handler state).map (fun output => (mapResult output.1, output.2)) := by
  induction program generalizing state with
  | pure distribution => simp only [mapOracleProgram, OracleProgram.run, PMF.map_comp, Function.comp_def]
  | query request next inductionHypothesis => exact inductionHypothesis _ _
  | sample distribution next inductionHypothesis =>
      simp only [mapOracleProgram, OracleProgram.run, PMF.map_bind]
      apply congrArg distribution.bind
      funext value
      exact inductionHypothesis value state

/-- This combined program retains the selected input for branch-specific events. -/
noncomputable def adaptiveInputDecisionProgram {oracle : OracleSpec} {Input Public Labels Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (table : Public) (auxiliary : Aux) (labels : Input → Labels) :
    OracleProgram oracle (Input × Bool)
      (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) :=
  appendOracleProgram (fun selected => mapOracleProgram (Prod.mk selected.1)
    (adversary.decide parameter table (labels selected.1) auxiliary selected.2))
    (adversary.chooseInput parameter table auxiliary)

/-- The tagged program has the exact two-phase result and selected input. -/
theorem adaptiveInputDecisionProgram_run {oracle : OracleSpec} {Input Public Labels Aux State : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (table : Public) (auxiliary : Aux) (labels : Input → Labels)
    (handler : OracleHandler oracle State) (state : State) :
    (adaptiveInputDecisionProgram adversary parameter table auxiliary labels).run handler state =
      ((adversary.chooseInput parameter table auxiliary).run handler state).bind fun selected =>
        ((adversary.decide parameter table (labels selected.1.1) auxiliary selected.1.2).run
          handler selected.2).map (fun output => ((selected.1.1, output.1), output.2)) := by
  simp only [adaptiveInputDecisionProgram, appendOracleProgram_run, mapOracleProgram_run]

end Kriterion.ArgoMAC.Security
