import Construction.SharedGarbling
import Proof.Correctness
import Proof.CiphertextSize
import Proof.LamportCompatibility

namespace Kriterion.ArgoMAC.Shared
open BN254

attribute [local irreducible] Wire.encoding Garbling.garble Garbling.evaluate

/-- The construction uses the paper's digit count and slot count. -/
theorem paperParameters : FieldMacToECMac.outputMacCount = 92 ∧
    Fintype.card (Fin 3) = 3 := ⟨rfl, rfl⟩

/-- Sharing permutations does not change the table encoding. -/
theorem ciphertextSize [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar) (tape : Randomness) :
    (Wire.encoding.encode (wireCircuit.garble parameter scalar tape).1).length = 9806076 :=
  Wire.ciphertextSize parameter scalar tape.val

/-- The shared-slot circuit sends the same 508 selected Lamport labels. -/
def lamportCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility wireCircuit affineLamportBits := {
  keyPairs := Lamport.compatible.keyPairs
  encodeSelectsLabels := Lamport.compatible.encodeSelectsLabels
}

/-- Correctness holds for every coherent tape and every input. -/
theorem perfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness wireCircuit evaluationOracle := by
  intro parameter scalar tape input
  dsimp only [wireCircuit, evaluationOracle, Lamport.wireCircuit,
    GarbledCircuit.mapLabels, Garbling.garbledCircuit]
  rw [tape.property]
  dsimp only [Garbling.encode]
  rw [Lamport.restore_selected]
  exact RCBComplete.perfectCorrectness parameter scalar tape.val input

theorem programCiphertextSize [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar)
    (tape : PrivateCoins × Cryptography.PublicOracle FixedKeyIndex EncPRF.PermutationIndex) :
    (Wire.encoding.encode (programCircuit.garble parameter scalar tape).1).length = 9806076 :=
  ciphertextSize parameter scalar (replaceOracle tape.1.val tape.2)

def programLamportCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility programCircuit affineLamportBits where
  keyPairs := Lamport.keyPairs
  encodeSelectsLabels := Lamport.selectedLabels_eq

theorem programPerfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness programCircuit Prod.snd := by
  intro parameter scalar tape input
  have correct := perfectCorrectness parameter scalar (replaceOracle tape.1.val tape.2) input
  simpa [programCircuit, wireCircuit, Lamport.wireCircuit, GarbledCircuit.mapLabels,
    Garbling.garbledCircuit, Garbling.garble, Garbling.encode, replaceOracle,
    evaluationOracle, restrict_expand] using correct

end Kriterion.ArgoMAC.Shared
