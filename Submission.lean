import Solution
import Construction
import Construction.OraclePrograms
import Proof
import Proof.Privacy.Simulator.Arithmetic.CompiledAdaptiveGame

set_option maxRecDepth 4096

namespace Submission
open Kriterion Kriterion.BN254 Kriterion.ArgoMAC

/-- The submission uses 92 digits and three shared permutation slots. -/
def solution : Kriterion.Solution := {
  FixedIndex := Shared.FixedKeyIndex
  EncIndex := EncPRF.PermutationIndex
  fixedFinite := inferInstance
  encFinite := inferInstance
  Randomness := Shared.PrivateCoins
  randomnessFinite := inferInstance
  randomness := Shared.privateCoins (Shared.Randomness.ofLegacy (Seed.randomness 0))
  Public := Pipeline.Table
  EncodingKey := InputMacKey
  encoding := Wire.encoding
  ciphertextBytes := 9806076
  garbleQueries := Shared.garbleQueries
  evaluateQueries := Shared.evaluateQueries
  garbleProgram := fun field group => @Shared.garbleProgram field group
  evaluateProgram := fun field group => @Shared.evaluateProgram field group
  garbleProgramCorrect := fun field group => @Shared.garbleProgram_correct field group
  evaluateProgramCorrect := fun field group => @Shared.evaluateProgram_correct field group
  scheme := fun field group => @Shared.programCircuit field group
  ciphertextSize := fun field group => @Shared.programCiphertextSize field group
  lamportCompatible := fun field group => @Shared.programLamportCompatible field group
  functionCorrect := fun _ _ _ _ => rfl
  perfectCorrectness := fun field group => @Shared.programPerfectCorrectness field group
  adaptivePrivacy := by
    intro field group
    let := field
    let := group
    let : Fintype Shared.PrivateCoins := Fintype.ofFinite _
    have fixed : (Fintype.ofFinite Shared.FixedKeyIndex) =
        (inferInstance : Fintype Shared.FixedKeyIndex) := Subsingleton.elim _ _
    have enc : (Fintype.ofFinite EncPRF.PermutationIndex) =
        (inferInstance : Fintype EncPRF.PermutationIndex) := Subsingleton.elim _ _
    have fixedEq : (Classical.decEq Shared.FixedKeyIndex) =
        (inferInstance : DecidableEq Shared.FixedKeyIndex) := Subsingleton.elim _ _
    have encEq : (Classical.decEq EncPRF.PermutationIndex) =
        (inferInstance : DecidableEq EncPRF.PermutationIndex) := Subsingleton.elim _ _
    rw [fixed, enc, fixedEq, encEq]
    exact ArithmeticSimulator.lazyCompiledAdaptivePrivacy
      (Shared.Randomness.ofLegacy (Seed.randomness 0))
}

end Submission
