import Proof.SimulatorFinitePrivacy
import Proof.SimulatorPrefixCost

namespace Kriterion.ArgoMAC.Security
open Cryptography OperationalOracle BoundedIntegerSampling
namespace SimulatorMachine.ExternalCost

noncomputable section

/-- This interpreter retains sparse work from every completed or failed external prefix.
The adversary supplies its own private probability distributions. -/
def runWithCost {A : Type} (attempts : Nat) :
    {budget : Nat} → OracleProgram Garbling.oracleSpec A budget → SparseState → Nat →
      PMF (Option (A × SparseState) × Nat)
  | _, .pure distribution, state, _ => distribution.map (fun value => (some (value, state), 0))
  | _, .sample distribution next, state, depth =>
      distribution.bind (fun value => runWithCost attempts (next value) state depth)
  | _, .query request next, state, depth =>
      let charge := Cost.combinedCharge depth (.inr request) state
      (cutoffDraw attempts (externalDraw request state)).law.bind fun result =>
        match result with
        | none => PMF.pure (none, charge)
        | some answer => (runWithCost attempts (next answer.1) answer.2 (depth + 1)).map
            (fun result => (result.1, charge + result.2))

/-- Erasing the work counter gives the exact finite external-phase law. -/
theorem runWithCost_law {A : Type} {budget : Nat} (attempts : Nat)
    (program : OracleProgram Garbling.oracleSpec A budget) (state : SparseState) (depth : Nat) :
    (runWithCost attempts program state depth).map Prod.fst =
      runCutoff externalDraw attempts program state := by
  induction program generalizing state depth with
  | pure distribution => simp only [runWithCost, runCutoff, PMF.map_comp, Function.comp_def]
  | sample distribution next ih =>
      simp only [runWithCost, runCutoff, PMF.map_bind, ih]
  | query request next ih =>
      simp only [runWithCost, runCutoff, PMF.map_bind]
      apply congrArg (PMF.bind (cutoffDraw attempts (externalDraw request state)).law)
      funext result
      cases result with
      | none => simp only [optionalPMF, PMF.pure_map]
      | some answer =>
          simp only [optionalPMF, PMF.map_comp, Function.comp_def]
          exact ih answer.1 answer.2 (depth + 1)

private theorem supportedDraw {A : Type} (attempts : Nat) (draw : Draw A) (value : A)
    (reached : some value ∈ (cutoffDraw attempts draw).law.support) :
    value ∈ draw.distribution.support := by
  rw [PMF.mem_support_iff] at reached ⊢
  exact ne_of_gt ((pos_iff_ne_zero.mpr reached).trans_le (cutoffDraw_upper attempts draw value))

/-- Every supported result has a bounded charge, including terminal failure.
Every successful result also retains its sparse-state certificate. -/
theorem runWithCost_resources {A : Type} {budget : Nat} (attempts : Nat)
    (program : OracleProgram Garbling.oracleSpec A budget) (state : SparseState)
    (depth capacity : Nat) (bound : Cost.StateBound state capacity) (depthBound : depth ≤ capacity)
    (result : Option (A × SparseState) × Nat)
    (reached : result ∈ (runWithCost attempts program state depth).support) :
    result.2 ≤ budget * (10 * (capacity + budget) + 16) ∧
      (∀ value, result.1 = some value → Nonempty (Cost.StateBound value.2 (capacity + budget))) := by
  induction program generalizing state depth capacity result with
  | pure distribution =>
      simp only [runWithCost] at reached
      obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      rw [← same]
      refine ⟨Nat.zero_le _, ?_⟩
      intro output equal
      cases equal
      exact ⟨bound.mono (Nat.le_add_right _ _)⟩
  | sample distribution next ih =>
      simp only [runWithCost] at reached
      obtain ⟨value, _, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      exact ih value state depth capacity bound depthBound result supported
  | @query budget request next ih =>
      simp only [runWithCost] at reached
      have step := Cost.combinedCharge_le depth capacity (.inr request) state bound depthBound
      obtain ⟨answer, supported, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      cases answer with
      | none =>
          simp only [PMF.mem_support_pure_iff] at tail
          rw [tail]
          refine ⟨?_, ?_⟩
          · dsimp only
            nlinarith
          · intro value impossible
            cases impossible
      | some answer =>
          obtain ⟨nextBound⟩ := Cost.external_resources request state capacity bound answer
            (supportedDraw attempts (externalDraw request state) answer supported)
          obtain ⟨output, outputReached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp tail
          obtain ⟨tailCost, finalBound⟩ := ih answer.1 answer.2 (depth + 1) (capacity + 1)
            nextBound (Nat.add_le_add_right depthBound 1) output outputReached
          rw [← same]
          refine ⟨?_, ?_⟩
          · dsimp only
            nlinarith
          · intro value equal
            have certificate := finalBound value equal
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using certificate

/-- The work bound needs no successful-output premise. -/
theorem runWithCost_bound {A : Type} {budget : Nat} (attempts : Nat)
    (program : OracleProgram Garbling.oracleSpec A budget) (state : SparseState)
    (depth capacity : Nat) (bound : Cost.StateBound state capacity) (depthBound : depth ≤ capacity)
    (result : Option (A × SparseState) × Nat)
    (reached : result ∈ (runWithCost attempts program state depth).support) :
    result.2 ≤ budget * (10 * (capacity + budget) + 16) :=
  (runWithCost_resources attempts program state depth capacity bound depthBound result reached).1

end
end SimulatorMachine.ExternalCost
end Kriterion.ArgoMAC.Security
