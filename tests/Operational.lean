import Proof.Privacy.Simulator.Arithmetic.WordInputBlock

open Kriterion.ArgoMAC Kriterion.ArgoMAC.Security Kriterion.Cryptography

namespace ClosedSimulatorRegression
open BoundedMachine LazyOracle OperationalOracle

private def machine (conflict : Bool) : Simulator := {
  size := 3
  code := #v[.program 0 0 1 2 3 1, .lookup 0 0 1 4 5 6 2,
    if conflict then .program 0 0 1 9 3 3 else .query 0 0 1 7 8 3, .compute .halt]
  addressBound := by decide
  firstFuel := 4
  secondFuel := 3
  within := by decide }

private def memory : Memory := {
  registers := fun register => if register = 1 then 7 else if register = 2 then 9
    else if register = 9 then 10 else 0 }

private noncomputable def result [Kriterion.BN254.FieldCertificate]
    (conflict : Bool) (fuel : Nat) :=
  ((machine conflict).run fuel ⟨0, memory⟩ (empty : State Unit Unit)).map
    (Option.map fun result => (result.1.memory.registers 4,
      result.1.memory.registers 6, result.1.memory.registers 7, result.2.2))

/-- The lookup and query return the fresh programmed value. -/
theorem fresh [Kriterion.BN254.FieldCertificate] :
    result false (machine false).firstFuel = PMF.pure (some (9, 1, 9, 4)) := by
  simp [Option.map, result, machine, memory, Simulator.run, Simulator.step, queryFromRegisters,
    program, lookup, LazyOracle.query, empty, permutationProgram, permutationLookup,
    SparsePermutation.empty, SparsePermutation.knownInput, SparsePermutation.knownOutput,
    SparsePermutation.extend, SparsePermutation.input, SparsePermutation.output,
    SparsePermutation.forward, swaps, Draw.distribution, answerFromWords, answerWords,
    BoundedMachine.step, Simulator.arithmetic, PMF.pure_map, Function.update]

/-- The conflicting program aborts the run. -/
theorem conflict [Kriterion.BN254.FieldCertificate] :
    result true (machine true).firstFuel = PMF.pure none := by
  simp [Option.map, result, machine, memory, Simulator.run, Simulator.step, queryFromRegisters,
    program, lookup, LazyOracle.query, empty, permutationProgram, permutationLookup,
    SparsePermutation.empty, SparsePermutation.knownInput, SparsePermutation.knownOutput,
    SparsePermutation.extend, SparsePermutation.input, SparsePermutation.output,
    SparsePermutation.forward, swaps, Draw.distribution, answerFromWords, answerWords,
    BoundedMachine.step, Simulator.arithmetic, PMF.pure_map, Function.update]

/-- The shorter stage fuel cannot reach the halt instruction. -/
theorem exhausted [Kriterion.BN254.FieldCertificate] :
    result false (machine false).secondFuel = PMF.pure none := by
  simp [Option.map, result, machine, memory, Simulator.run, Simulator.step, queryFromRegisters,
    program, lookup, LazyOracle.query, empty, permutationProgram, permutationLookup,
    SparsePermutation.empty, SparsePermutation.knownInput, SparsePermutation.knownOutput,
    SparsePermutation.extend, SparsePermutation.input, SparsePermutation.output,
    SparsePermutation.forward, swaps, Draw.distribution, answerFromWords, answerWords,
    BoundedMachine.step, Simulator.arithmetic, PMF.pure_map, Function.update]

#print axioms fresh
#print axioms conflict
#print axioms exhausted
end ClosedSimulatorRegression

namespace InputMachineRegression
open Kriterion.ArgoMAC.ArithmeticSimulator Kriterion.Cryptography.BoundedMachine

private def labels (pc : Fin 15) : Fin 16 := ⟨pc.val, by omega⟩

private def readStore : Machine := ⟨15, Vector.ofFn (fun pc : Fin 16 =>
  if inside : pc.val < 14 then
    relocate labels ((wordInput 3).code[pc.val]'(by change pc.val < 15; omega))
  else if pc.val = 14 then .store 8 0 15 else .halt), by decide⟩

private theorem contains : ContainsWordInput readStore 3 labels := by
  intro pc inside
  simp [readStore, labels, inside]

private def initialMemory : Memory := {
  bits := Function.update (fun _ => []) 0 [true, false, true, false]
  registers := Function.update (fun _ => 0) 8 37 }

/-- The caller stores five at its saved address and retains the unread fourth bit. -/
example [Kriterion.BN254.FieldCertificate] :
    (run readStore 29 ⟨0, initialMemory⟩).map
      (Option.map fun result => (result.1.memory.ram 37,
        result.1.memory.bits 0, result.1.memory.registers 7, result.2)) =
      PMF.pure (some (5, [false], 1, 29)) := by
  have continued := wordInputBlock_continue readStore 3 2 labels contains
    initialMemory [true, false, true] [false] rfl rfl (by decide)
  change (run readStore (7 * 3 + 6 + 2) ⟨labels 0, initialMemory⟩).map _ = _
  rw [continued]
  simp [run, step, readStore, labels, inputFinal, inputFrame, inputFold,
    initialMemory, PMF.pure_map]

end InputMachineRegression
