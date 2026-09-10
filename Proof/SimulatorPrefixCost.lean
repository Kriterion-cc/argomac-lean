import Proof.SimulatorMachineCost
import Proof.SimulatorCutoff

namespace Kriterion.ArgoMAC.Security
open Cryptography OperationalOracle BoundedIntegerSampling
namespace SimulatorMachine

/-- Every fair-bit tape selects a value in the program law. -/
theorem bitRun_support {A Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (code : BitCode A) (seed : Seed) :
    (code.run random seed).1.1 ∈ code.law.support := by
  induction code generalizing seed with
  | pure value => simp only [BitCode.run, BitCode.law, PMF.mem_support_pure_iff]
  | bits width next ih =>
      apply (PMF.mem_support_bind_iff _ _ _).mpr
      exact ⟨(random width seed).1, PMF.mem_support_uniformOfFintype _, ih _ _⟩

/-- A successful finite draw selects a value in the exact draw law. -/
theorem cutoffDraw_run_support {A Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (draw : Draw A) (seed : Seed) (value : A)
    (same : ((cutoffDraw attempts draw).run random seed).1.1 = some value) :
    value ∈ draw.distribution.support := by
  have member := bitRun_support random (cutoffDraw attempts draw) seed
  rw [same, PMF.mem_support_iff] at member
  rw [PMF.mem_support_iff]
  exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr member)
    (cutoffDraw_upper attempts draw value))

namespace Cost

/-- The finite interpreter retains sparse charges when a draw fails.
The query count includes the failed request. -/
def executeCutoffCost {A Seed : Type} {budget : Nat}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat) :
    Program combinedSpec A budget → SparseState → Seed → Nat →
      (Option (A × SparseState) × Seed) × Nat × Nat × Nat
  | .pure value, state, seed, _ => ((some (value, state), seed), 0, 0, 0)
  | .query query next, state, seed, depth =>
      let answer := (cutoffDraw attempts (combinedDraw query state)).run random seed
      match answer.1.1 with
      | none => ((none, answer.1.2), 1, combinedCharge depth query state, answer.2)
      | some value =>
          let tail := executeCutoffCost random attempts (next value.1) value.2 answer.1.2 (depth + 1)
          (tail.1, tail.2.1 + 1, combinedCharge depth query state + tail.2.2.1,
            answer.2 + tail.2.2.2)
  | .map f source, state, seed, depth =>
      let answer := executeCutoffCost random attempts source state seed depth
      ((answer.1.1.map (fun value => (f value.1, value.2)), answer.1.2), answer.2)
  | .bind source next, state, seed, depth =>
      let first := executeCutoffCost random attempts source state seed depth
      match first.1.1 with
      | none => ((none, first.1.2), first.2)
      | some value =>
          let second := executeCutoffCost random attempts (next value.1) value.2 first.1.2
            (depth + first.2.1)
          (second.1, first.2.1 + second.2.1, first.2.2.1 + second.2.2.1,
            first.2.2.2 + second.2.2.2)
  | .weaken source _, state, seed, depth => executeCutoffCost random attempts source state seed depth

/-- The counters preserve the finite result, the random tape, and the bit count. -/
theorem executeCutoffCost_correct {A Seed : Type} {budget : Nat}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat)
    (program : Program combinedSpec A budget) (state : SparseState) (seed : Seed) (depth : Nat) :
    ((executeCutoffCost random attempts program state seed depth).1,
      (executeCutoffCost random attempts program state seed depth).2.2.2) =
      (program.cutoff combinedDraw attempts state).run random seed := by
  induction program generalizing state seed depth with
  | pure => rfl
  | query query next ih =>
      simp only [executeCutoffCost, Program.cutoff, BitCode.bind_run]
      split
      · simp_all [optional, BitCode.run]
      · rename_i value same
        simp only [same, optional]
        have tail := ih value.1 value.2
          ((cutoffDraw attempts (combinedDraw query state)).run random seed).1.2 (depth + 1)
        rw [← tail]
  | map f source ih =>
      simp only [executeCutoffCost, Program.cutoff, BitCode.bind_run, ← ih state seed depth]
      cases same : (executeCutoffCost random attempts source state seed depth).1.1 <;>
        simp [optional, BitCode.run]
  | bind source next first second =>
      simp only [executeCutoffCost, Program.cutoff, BitCode.bind_run, ← first state seed depth]
      split
      · simp_all [optional, BitCode.run]
      · rename_i value same
        simp only [same, optional]
        rw [← second value.1 value.2
          (executeCutoffCost random attempts source state seed depth).1.2
          (depth + (executeCutoffCost random attempts source state seed depth).2.1)]
  | weaken source bounded ih => exact ih state seed depth

/-- The certificate applies to successful outputs and to failed prefixes. -/
theorem executeCutoffCost_resources {A Seed : Type} {budget : Nat}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat)
    (program : Program combinedSpec A budget) (state : SparseState) (seed : Seed)
    (depth capacity : Nat) (bound : StateBound state capacity) (depthBound : depth ≤ capacity) :
    let result := executeCutoffCost random attempts program state seed depth
    result.2.1 ≤ budget ∧
    (∀ value, result.1.1 = some value → Nonempty (StateBound value.2 (capacity + result.2.1))) ∧
    result.2.2.1 ≤ result.2.1 * (10 * (capacity + result.2.1) + 16) := by
  induction program generalizing state seed depth capacity with
  | pure value =>
      refine ⟨Nat.le_refl _, ?_, by simp [executeCutoffCost]⟩
      intro result same
      cases same
      exact ⟨bound⟩
  | @query A budget query next ih =>
      let answer := (cutoffDraw attempts (combinedDraw query state)).run random seed
      have stepCost := combinedCharge_le depth capacity query state bound depthBound
      simp only [executeCutoffCost]
      split
      · refine ⟨by simp only; omega, ?_, ?_⟩
        · intro value same; cases same
        · dsimp only; omega
      · rename_i value same
        obtain ⟨nextBound⟩ := combined_resources query state capacity bound value
          (cutoffDraw_run_support random attempts (combinedDraw query state) seed value same)
        obtain ⟨calls, finalBound, tailCost⟩ := ih value.1 value.2 answer.1.2
          (depth + 1) (capacity + 1) nextBound (by omega)
        dsimp only [answer] at calls finalBound tailCost
        refine ⟨by dsimp only; omega, ?_, ?_⟩
        · intro result reached
          have certificate := finalBound result reached
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using certificate
        · dsimp only at *
          nlinarith
  | map f source ih =>
      obtain ⟨calls, finalBound, total⟩ := ih state seed depth capacity bound depthBound
      refine ⟨calls, ?_, total⟩
      intro result same
      simp only [executeCutoffCost] at same
      cases reached : (executeCutoffCost random attempts source state seed depth).1.1 with
      | none => simp [reached] at same
      | some value =>
          simp only [reached, Option.map_some, Option.some.injEq] at same
          cases same
          exact finalBound value reached
  | bind source next first second =>
      obtain ⟨firstCalls, middleBound, firstCost⟩ := first state seed depth capacity bound depthBound
      simp only [executeCutoffCost]
      split
      · refine ⟨firstCalls.trans (Nat.le_add_right _ _), ?_, firstCost⟩
        intro value same; cases same
      · rename_i value same
        obtain ⟨middle⟩ := middleBound value same
        obtain ⟨secondCalls, finalBound, secondCost⟩ := second value.1 value.2
          (executeCutoffCost random attempts source state seed depth).1.2
          (depth + (executeCutoffCost random attempts source state seed depth).2.1)
          (capacity + (executeCutoffCost random attempts source state seed depth).2.1)
          middle (Nat.add_le_add_right depthBound _)
        refine ⟨Nat.add_le_add firstCalls secondCalls, ?_, ?_⟩
        · intro result reached
          simpa only [Nat.add_assoc] using finalBound result reached
        · dsimp only at *
          nlinarith [Nat.zero_le
            ((executeCutoffCost random attempts source state seed depth).2.1 *
             (executeCutoffCost random attempts (next value.1) value.2
               (executeCutoffCost random attempts source state seed depth).1.2
               (depth + (executeCutoffCost random attempts source state seed depth).2.1)).2.1)]
  | weaken source larger ih =>
      obtain ⟨calls, resources, total⟩ := ih state seed depth capacity bound depthBound
      exact ⟨calls.trans larger, resources, total⟩

/-- The finite interpreter has a strict sparse-work bound on every tape. -/
theorem executeCutoffCost_budget {A Seed : Type} {budget : Nat}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat)
    (program : Program combinedSpec A budget) (state : SparseState) (seed : Seed)
    (depth capacity : Nat) (bound : StateBound state capacity) (depthBound : depth ≤ capacity) :
    (executeCutoffCost random attempts program state seed depth).2.2.1 ≤
      budget * (10 * (capacity + budget) + 16) := by
  obtain ⟨calls, _, total⟩ := executeCutoffCost_resources random attempts program state seed
    depth capacity bound depthBound
  exact total.trans (Nat.mul_le_mul calls (by omega))

end Cost
end SimulatorMachine
end Kriterion.ArgoMAC.Security
