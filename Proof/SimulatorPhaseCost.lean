import Proof.SimulatorExternalCost

namespace Kriterion.ArgoMAC.Security
open Cryptography OperationalOracle BoundedIntegerSampling
namespace SimulatorMachine.PhaseCost

/-- This bound starts from the actual empty oracle state. It bounds every terminal prefix.
The private stage uses the finite interpreter that retains failed-request charges. -/
theorem all_phase_bound {Before Chosen Encoded Result Seed : Type}
    {q0 q1 privateBudget q2 : Nat}
    (attempts : Nat) (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (seed : Seed)
    (first : OracleProgram Garbling.oracleSpec Before q0)
    (second : Before → OracleProgram Garbling.oracleSpec Chosen q1)
    (privateStage : Chosen → Program combinedSpec Encoded privateBudget)
    (last : Chosen → Encoded → OracleProgram Garbling.oracleSpec Result q2)
    (before : Option (Before × SparseState) × Nat)
    (beforeReached : before ∈ (ExternalCost.runWithCost attempts first
      (initial initialMetadata) 0).support) :
    let total := q0 + q1 + privateBudget + q2
    let limit := total * (10 * total + 16)
    before.2 ≤ limit ∧
      ∀ prior, before.1 = some prior →
      ∀ chosen : Option (Chosen × SparseState) × Nat,
        chosen ∈ (ExternalCost.runWithCost attempts (second prior.1) prior.2 q0).support →
        before.2 + chosen.2 ≤ limit ∧
          ∀ selected, chosen.1 = some selected →
          let encoded := Cost.executeCutoffCost random attempts (privateStage selected.1)
            selected.2 seed (q0 + q1)
          before.2 + chosen.2 + encoded.2.2.1 ≤ limit ∧
            ∀ value, encoded.1.1 = some value →
            ∀ decided : Option (Result × SparseState) × Nat,
              decided ∈ (ExternalCost.runWithCost attempts (last selected.1 value.1)
                value.2 (q0 + q1 + privateBudget)).support →
              before.2 + chosen.2 + encoded.2.2.1 + decided.2 ≤ limit := by
  let total := q0 + q1 + privateBudget + q2
  let unit := 10 * total + 16
  have empty : Cost.StateBound (initial initialMetadata) 0 :=
    Cost.initialBound initialMetadata 0 (by rfl) (by rfl) (by rfl)
  obtain ⟨firstCost, firstState⟩ := ExternalCost.runWithCost_resources attempts first
    (initial initialMetadata) 0 0 empty (Nat.le_refl _) before beforeReached
  have h0 : before.2 ≤ q0 * unit := firstCost.trans
    (Nat.mul_le_mul_left q0 (by dsimp [unit, total]; omega))
  refine ⟨h0.trans (Nat.mul_le_mul_right unit (by omega)), ?_⟩
  intro prior priorSame chosen chosenReached
  obtain ⟨priorBound⟩ := firstState prior priorSame
  have priorBound' : Cost.StateBound prior.2 q0 := by simpa only [Nat.zero_add] using priorBound
  obtain ⟨secondCost, secondState⟩ := ExternalCost.runWithCost_resources attempts (second prior.1)
    prior.2 q0 q0 priorBound' (Nat.le_refl _) chosen chosenReached
  have h1 : chosen.2 ≤ q1 * unit := secondCost.trans
    (Nat.mul_le_mul_left q1 (by dsimp [unit, total]; omega))
  have h01 : before.2 + chosen.2 ≤ (q0 + q1) * unit := by
    rw [Nat.add_mul]
    exact Nat.add_le_add h0 h1
  refine ⟨h01.trans (Nat.mul_le_mul_right unit (by omega)), ?_⟩
  intro selected selectedSame
  obtain ⟨selectedBound⟩ := secondState selected selectedSame
  let encoded := Cost.executeCutoffCost random attempts (privateStage selected.1)
    selected.2 seed (q0 + q1)
  have privateCost := Cost.executeCutoffCost_budget random attempts (privateStage selected.1)
    selected.2 seed (q0 + q1) (q0 + q1) selectedBound (Nat.le_refl _)
  have hPrivate : encoded.2.2.1 ≤ privateBudget * unit := privateCost.trans
    (Nat.mul_le_mul_left privateBudget (by dsimp [unit, total]; omega))
  have h012 : before.2 + chosen.2 + encoded.2.2.1 ≤ (q0 + q1 + privateBudget) * unit := by
    rw [Nat.add_mul]
    exact Nat.add_le_add h01 hPrivate
  refine ⟨h012.trans (Nat.mul_le_mul_right unit (by omega)), ?_⟩
  intro value valueSame decided decidedReached
  obtain ⟨calls, state, _⟩ := Cost.executeCutoffCost_resources random attempts
    (privateStage selected.1) selected.2 seed (q0 + q1) (q0 + q1)
    selectedBound (Nat.le_refl _)
  obtain ⟨valueBound⟩ := state value valueSame
  have valueBound' := valueBound.mono (Nat.add_le_add_left calls (q0 + q1))
  have lastCost := (ExternalCost.runWithCost_resources attempts (last selected.1 value.1)
    value.2 (q0 + q1 + privateBudget) (q0 + q1 + privateBudget) valueBound'
    (Nat.le_refl _) decided decidedReached).1
  have h2 : decided.2 ≤ q2 * unit := lastCost
  have bound := Nat.add_le_add h012 h2
  simpa only [← Nat.add_mul] using bound

end SimulatorMachine.PhaseCost
end Kriterion.ArgoMAC.Security
