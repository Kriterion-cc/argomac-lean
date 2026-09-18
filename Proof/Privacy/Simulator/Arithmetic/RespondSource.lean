import Proof.Privacy.Simulator.Arithmetic.RunReserve

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A sufficient shared budget preserves the exact completed request source and its charge. -/
theorem respond_source [BN254.FieldCertificate] (machine : Machine) (request : List Bool) (state : State)
    (fuel : Nat) (source : PMF (Configuration (machine.size + 1) × Nat))
    (enough : state.spent + fuel ≤ budget state.queries)
    (implemented : run machine fuel
      ⟨0, {state.memory with bits := Function.update (Function.update state.memory.bits 0 request) 3 []}⟩ =
        source.map some) :
    respond machine request state = source.map (fun result =>
      some (result.1.memory.bits 3, (⟨result.1.memory, state.spent + result.2, state.queries⟩ : State))) := by
  have complete : none ∉ (run machine fuel
      ⟨0, {state.memory with bits := Function.update (Function.update state.memory.bits 0 request) 3 []}⟩).support := by
    rw [implemented]
    simp [PMF.mem_support_map_iff]
  unfold respond
  rw [if_pos (by omega)]
  rw [run_reserve_of_complete machine fuel (budget state.queries - state.spent) _ (by omega) complete,
    implemented, PMF.map_comp]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
