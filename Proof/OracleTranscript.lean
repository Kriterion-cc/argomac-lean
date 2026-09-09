import Cryptography.Primitives

namespace Kriterion.ArgoMAC.Security

open Cryptography

universe uQuery uAnswer uResult uState uOther

/-- This interpreter records the public query-answer pairs. -/
noncomputable def runOracleProgramWithTranscript
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} (handler : OracleHandler oracle State) :
    {budget : Nat} → OracleProgram oracle Result budget → State →
      PMF (Result × State × List (Sigma oracle.Answer))
  | _, .pure result, state => result.map fun value => (value, state, [])
  | _, .query request next, state =>
      let answered := handler request state
      (runOracleProgramWithTranscript handler (next answered.1) answered.2).map
        fun output => (output.1, output.2.1, ⟨request, answered.1⟩ :: output.2.2)
  | _, .sample distribution next, state =>
      distribution.bind fun value => runOracleProgramWithTranscript handler (next value) state

/-- The program has the same distribution after transcript erasure. -/
theorem runOracleProgramWithTranscript_erase
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} (handler : OracleHandler oracle State)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State) :
    (runOracleProgramWithTranscript handler program state).map
        (fun output => (output.1, output.2.1)) = program.run handler state := by
  induction program generalizing state with
  | pure result =>
      rw [runOracleProgramWithTranscript, OracleProgram.run, PMF.map_comp]
      rfl
  | query request next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript, OracleProgram.run, PMF.map_comp]
      exact inductionHypothesis _ _
  | sample distribution next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript, OracleProgram.run, PMF.map_bind]
      congr 1
      funext value
      exact inductionHypothesis value state

/-- A compatible oracle gives each recorded answer in order. -/
def OracleTranscriptCompatible
    {oracle : OracleSpec.{uQuery, uAnswer}} {State : Type uState}
    (handler : OracleHandler oracle State) : State → List (Sigma oracle.Answer) → Prop
  | _, [] => True
  | state, ⟨request, answer⟩ :: tail =>
      (handler request state).1 = answer ∧
        OracleTranscriptCompatible handler (handler request state).2 tail

/-- Each supported transcript is compatible with its oracle. -/
theorem runOracleProgramWithTranscript_compatible
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} (handler : OracleHandler oracle State)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State)
    (output : Result × State × List (Sigma oracle.Answer))
    (member : output ∈ (runOracleProgramWithTranscript handler program state).support) :
    OracleTranscriptCompatible handler state output.2.2 := by
  induction program generalizing state output with
  | pure result =>
      simp only [runOracleProgramWithTranscript, PMF.mem_support_map_iff] at member
      rcases member with ⟨value, _, rfl⟩
      trivial
  | query request next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript, PMF.mem_support_map_iff] at member
      rcases member with ⟨tailOutput, tailMember, rfl⟩
      exact ⟨rfl, inductionHypothesis _ _ tailOutput tailMember⟩
  | sample distribution next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript, PMF.mem_support_bind_iff] at member
      rcases member with ⟨value, _, tailMember⟩
      exact inductionHypothesis value state output tailMember

/-- A compatible oracle can replay every supported program output. -/
theorem runOracleProgramWithTranscript_replay
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} {Other : Type uOther}
    (handler : OracleHandler oracle State) (other : OracleHandler oracle Other)
    {budget : Nat} (program : OracleProgram oracle Result budget)
    (state : State) (otherState : Other) (output : Result × State × List (Sigma oracle.Answer))
    (member : output ∈ (runOracleProgramWithTranscript handler program state).support)
    (compatible : OracleTranscriptCompatible other otherState output.2.2) :
    ∃ finalState, (output.1, finalState, output.2.2) ∈
      (runOracleProgramWithTranscript other program otherState).support := by
  induction program generalizing state otherState output with
  | pure result =>
      simp only [runOracleProgramWithTranscript, PMF.mem_support_map_iff] at member ⊢
      rcases member with ⟨value, valueMember, rfl⟩
      exact ⟨otherState, value, valueMember, rfl⟩
  | query request next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript, PMF.mem_support_map_iff] at member ⊢
      rcases member with ⟨tailOutput, tailMember, rfl⟩
      obtain ⟨sameAnswer, compatibleTail⟩ := compatible
      obtain ⟨finalState, finalMember⟩ := inductionHypothesis
        (handler request state).1 (handler request state).2
        (other request otherState).2 tailOutput tailMember compatibleTail
      refine ⟨finalState, (tailOutput.1, finalState, tailOutput.2.2), ?_, ?_⟩
      · simpa only [sameAnswer] using finalMember
      · simp only [sameAnswer]
  | sample distribution next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript, PMF.mem_support_bind_iff] at member ⊢
      rcases member with ⟨value, valueMember, tailMember⟩
      obtain ⟨finalState, finalMember⟩ :=
        inductionHypothesis value state otherState output tailMember compatible
      exact ⟨finalState, value, valueMember, finalMember⟩

/-- Attainability turns compatibility into an exact support condition. -/
theorem runOracleProgramWithTranscript_support_iff
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} {Other : Type uOther}
    (handler : OracleHandler oracle State) (other : OracleHandler oracle Other)
    {budget : Nat} (program : OracleProgram oracle Result budget)
    (state : State) (otherState : Other) (output : Result × State × List (Sigma oracle.Answer))
    (member : output ∈ (runOracleProgramWithTranscript handler program state).support) :
    (∃ finalState, (output.1, finalState, output.2.2) ∈
      (runOracleProgramWithTranscript other program otherState).support) ↔
        OracleTranscriptCompatible other otherState output.2.2 := by
  constructor
  · rintro ⟨finalState, finalMember⟩
    exact runOracleProgramWithTranscript_compatible other program otherState
      (output.1, finalState, output.2.2) finalMember
  · exact runOracleProgramWithTranscript_replay handler other program state otherState output member

/-- Compatible oracles assign equal mass to each public result and transcript. -/
theorem runOracleProgramWithTranscript_mass_eq
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} {Other : Type uOther}
    (handler : OracleHandler oracle State) (other : OracleHandler oracle Other)
    {budget : Nat} (program : OracleProgram oracle Result budget)
    (state : State) (otherState : Other) (result : Result)
    (transcript : List (Sigma oracle.Answer))
    (compatible : OracleTranscriptCompatible handler state transcript)
    (otherCompatible : OracleTranscriptCompatible other otherState transcript) :
    ((runOracleProgramWithTranscript handler program state).map
        (fun output => (output.1, output.2.2))) (result, transcript) =
      ((runOracleProgramWithTranscript other program otherState).map
        (fun output => (output.1, output.2.2))) (result, transcript) := by
  classical
  induction program generalizing state otherState transcript with
  | pure distribution =>
      simp only [runOracleProgramWithTranscript, PMF.map_comp, Function.comp_def]
  | query request next inductionHypothesis =>
      cases transcript with
      | nil =>
          simp [runOracleProgramWithTranscript, PMF.map_comp, PMF.map_apply]
      | cons entry tail =>
          rcases entry with ⟨query, answer⟩
          by_cases sameQuery : query = request
          · subst query
            obtain ⟨sameAnswer, compatibleTail⟩ := compatible
            obtain ⟨otherAnswer, otherTail⟩ := otherCompatible
            simpa only [runOracleProgramWithTranscript, PMF.map_comp, PMF.map_apply,
              Function.comp_apply, Prod.mk.injEq, List.cons.injEq, Sigma.mk.inj_iff,
              sameAnswer, otherAnswer, heq_eq_eq, true_and, and_true] using
              inductionHypothesis answer (handler request state).2
                (other request otherState).2 tail compatibleTail otherTail
          · simp [runOracleProgramWithTranscript, PMF.map_comp, PMF.map_apply, sameQuery]
  | sample distribution next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript, PMF.map_bind, PMF.bind_apply]
      apply tsum_congr
      intro value
      rw [inductionHypothesis value state otherState transcript compatible otherCompatible]

/-- An incompatible transcript has zero mass. -/
theorem runOracleProgramWithTranscript_mass_zero
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} (handler : OracleHandler oracle State)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State)
    (result : Result) (transcript : List (Sigma oracle.Answer))
    (incompatible : ¬ OracleTranscriptCompatible handler state transcript) :
    ((runOracleProgramWithTranscript handler program state).map
        (fun output => (output.1, output.2.2))) (result, transcript) = 0 := by
  rw [PMF.apply_eq_zero_iff]
  intro member
  rw [PMF.mem_support_map_iff] at member
  obtain ⟨output, outputMember, same⟩ := member
  apply incompatible
  have compatible := runOracleProgramWithTranscript_compatible handler program state output outputMember
  have sameTrace : output.2.2 = transcript := congrArg Prod.snd same
  rwa [sameTrace] at compatible

/-- Oracle sampling separates from the common adversary mass. -/
theorem runOracleProgramWithTranscript_mass_factor
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} {Other : Type uOther}
    (handler : OracleHandler oracle State) (reference : OracleHandler oracle Other)
    {budget : Nat} (program : OracleProgram oracle Result budget)
    (states : PMF State) (referenceState : Other) (result : Result)
    (transcript : List (Sigma oracle.Answer))
    (referenceCompatible : OracleTranscriptCompatible reference referenceState transcript) :
    ((states.bind (runOracleProgramWithTranscript handler program)).map
        (fun output => (output.1, output.2.2))) (result, transcript) =
      ((runOracleProgramWithTranscript reference program referenceState).map
        (fun output => (output.1, output.2.2))) (result, transcript) *
          states.toOuterMeasure {state | OracleTranscriptCompatible handler state transcript} := by
  classical
  rw [PMF.map_bind, PMF.bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro state
  by_cases compatible : OracleTranscriptCompatible handler state transcript
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, compatible, if_true]
    rw [runOracleProgramWithTranscript_mass_eq handler reference program
      state referenceState result transcript compatible referenceCompatible, mul_comm]
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, compatible, if_false, mul_zero]
    rw [runOracleProgramWithTranscript_mass_zero handler program state result transcript compatible,
      mul_zero]

end Kriterion.ArgoMAC.Security
