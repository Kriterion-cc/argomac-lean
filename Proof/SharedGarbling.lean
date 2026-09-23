import Construction.SharedGarbling
import Proof.Correctness
import Proof.CiphertextSize
import Proof.LamportCompatibility
import Architect

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
@[blueprint "Shared.perfectCorrectness"
  (statement := /-- Perfect correctness of the wire circuit, the garbling scheme of Fig.~21 whose input labels are
    the Lamport signatures of the bits of $\pi$ (Eqs.~15--16). For every coherent tape and every
    input $\pi$, evaluation under the evaluation oracle returns $f[r](\pi)$. -/)
  (title := /-- BABE Fig.~21 -/)]
theorem perfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness wireCircuit evaluationOracle := by
  /-- Fix $r$, a coherent tape, and $\pi$. Unfold the wire circuit and rewrite the evaluation oracle
    with the tape property. By \cref{Lamport.restore_selected} the Lamport signature restores the
    bit labels $L$. Conclude with \cref{RCBComplete.perfectCorrectness}. -/
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

@[blueprint "Shared.programLamportCompatible"
  (statement := /-- Lamport compatibility (Eqs.~15--16). The Lamport key pairs $\{(L^0_{x,i}, L^1_{x,i}),
    (L^0_{y,i}, L^1_{y,i})\}_{i < 254}$ of $\mathsf{ek}$ and the bit decomposition $\mathbf{b}$ of
    $\pi$ select exactly the labels $\mathsf{Encode}(\mathsf{ek}, \pi)$, so the input labels are the
    Lamport signature of $\pi$. -/)
  (title := /-- BABE Eqs.~15--16 -/)]
def programLamportCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility programCircuit affineLamportBits where
  keyPairs := Lamport.keyPairs
  encodeSelectsLabels := Lamport.selectedLabels_eq

@[blueprint "Shared.programPerfectCorrectness"
  (statement := /-- Perfect correctness of the garbling scheme $(\mathsf{Garble}, \mathsf{Encode}, \mathsf{Eval})$
    of Fig.~21 for $f[r]$ (Eq.~27). For every secret scalar $r$, every random tape, and every input
    $\pi = (x(\pi), y(\pi))$: $\mathsf{Eval}(\mathsf{ct}_{\mathsf{gc}}, \mathsf{Encode}(\mathsf{ek},
    \pi), \pi) = f[r](\pi)$, where $(\mathsf{ct}_{\mathsf{gc}}, \mathsf{ek}) =
    \mathsf{Garble}(C[r])$. The tape supplies the private coins and the public oracles
    $\mathsf{CTPRF}$, $\mathsf{EncPRF}$, and the hash. -/)
  (title := /-- BABE Fig.~21 -/)]
theorem programPerfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness programCircuit Prod.snd := by
  /-- Fix $r$, the tape, and $\pi$. Apply \cref{Shared.perfectCorrectness} to the tape whose public
    oracle is replaced by the oracle component of the tape. Unfold the program circuit, the wire
    circuit, and the label map. The two sides agree. -/
  intro parameter scalar tape input
  have correct := perfectCorrectness parameter scalar (replaceOracle tape.1.val tape.2) input
  simpa [programCircuit, wireCircuit, Lamport.wireCircuit, GarbledCircuit.mapLabels,
    Garbling.garbledCircuit, Garbling.garble, Garbling.encode, replaceOracle,
    evaluationOracle, restrict_expand] using correct

end Kriterion.ArgoMAC.Shared
