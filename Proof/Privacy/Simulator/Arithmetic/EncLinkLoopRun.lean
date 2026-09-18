import Proof.Privacy.Simulator.Arithmetic.EncLinkContinuation

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The finite source uses the final return only after all scheduled rows finish. -/
def encLinkLoopEntry (indices : List EncPRF.PermutationIndex) : Fin 7468 :=
  if indices = [] then 7466 else 7208

/-- The fixed machine implements the complete finite loop in every caller machine. -/
theorem encLinkBlock_loop [BN254.FieldCertificate] (host : Machine) (attempts fuel : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (state : SparseOracleFamily) (memory : Memory) (indices : List EncPRF.PermutationIndex)
    (suffix : List Bool) (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory indices suffix firstKey output limit)
    (attemptFits : attempts < 2 ^ 256) :
    let reserve := encLinkLoopBudget attempts limit indices.length + fuel
    run host reserve ⟨labels (encLinkLoopEntry indices), memory⟩ =
      (encLinkLoopSamples attempts firstKey suffix indices memory state).bind
        (encLinkContinue host labels reserve) := by
  dsimp only
  induction indices generalizing state memory output limit fuel with
  | nil =>
      simp [encLinkLoopSamples, encLinkContinue, encLinkLoopEntry, encLinkLoopBudget, PMF.map_id]
  | cons index indices ih =>
      have enough : encLinkRowBudget attempts (limit + indices.length + 1) ≤
          encLinkLoopBudget attempts limit (index :: indices).length + fuel := by
        rw [List.length_cons, encLinkLoopBudget_step]
        omega
      change run host _ ⟨labels 7208, memory⟩ = _
      rw [encLinkBlock_readyBudget host attempts _ labels present state memory index indices suffix
        firstKey output limit ready attemptFits enough, encLinkLoopSamples, PMF.bind_bind]
      apply Security.ThreePhase.bind_eq_on_support
      intro row supported
      by_cases failed : row.1.2.2 = 7467
      · simp only [if_pos failed, PMF.pure_bind]
      · simp only [if_neg failed]
        have progress := encLinkRowSamples_progress attempts state memory index indices suffix firstKey
          output limit ready row supported
        have next := (progress.resolve_left failed).1
        have target : row.1.2.2 = encLinkLoopEntry indices := (progress.resolve_left failed).2
        have rowBound := encLinkRowSamples_budget attempts state memory index indices suffix firstKey
          output limit ready attemptFits row supported
        let extra := encLinkRowBudget attempts (limit + indices.length + 1) - row.1.2.1 + fuel
        let remaining := encLinkLoopBudget attempts (limit + 1) indices.length + extra
        have difference : encLinkLoopBudget attempts limit (index :: indices).length + fuel - row.1.2.1 =
            remaining := by
          rw [List.length_cons, encLinkLoopBudget_step]
          dsimp [remaining, extra]
          omega
        have complete : row.1.2.1 + remaining =
            encLinkLoopBudget attempts limit (index :: indices).length + fuel := by
          rw [List.length_cons, encLinkLoopBudget_step]
          dsimp [remaining, extra]
          omega
        have continued := ih extra row.2 row.1.1 (output + 1) (limit + 1) next
        change run host remaining ⟨labels (encLinkLoopEntry indices), row.1.1⟩ = _ at continued
        change (run host (_ - row.1.2.1) ⟨labels row.1.2.2, row.1.1⟩).map
          (Option.map fun final => (final.1, final.2 + row.1.2.1)) = _
        rw [difference, target, continued,
          encLinkCharge_continue host labels _ row.1.2.1 remaining, complete]

end Kriterion.ArgoMAC.ArithmeticSimulator
