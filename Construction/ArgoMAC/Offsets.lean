/-
This file defines the constrained ArgoMAC offsets.
-/

import Construction.ArgoMAC.Base7
import Architect

namespace Kriterion.ArgoMAC

open BN254

def clampOffsets [FieldCertificate] [GroupCertificate]
    (beta : ScalarField) (freeOffsets : List Point) : List Point :=
  -(beta • pointHorner beta freeOffsets) :: freeOffsets

theorem pointHornerClampOffsets [FieldCertificate] [GroupCertificate]
    (beta : ScalarField) (freeOffsets : List Point) :
    pointHorner beta (clampOffsets beta freeOffsets) = 0 := by
  simp [clampOffsets, pointHorner]

structure OffsetRandomness [FieldCertificate] where
  freeOffsets : List Point
  freeOffsetCount : freeOffsets.length = 91

def Construction.offsets [FieldCertificate] [GroupCertificate]
    (_construction : Construction) (randomness : OffsetRandomness) : List Point :=
  clampOffsets radix randomness.freeOffsets

theorem Construction.offsetsLength [FieldCertificate] [GroupCertificate]
    (construction : Construction) (randomness : OffsetRandomness) :
    (construction.offsets randomness).length = 92 := by
  simp [Construction.offsets, clampOffsets, randomness.freeOffsetCount]

@[blueprint "Construction.offsetsCancel"
  (statement := /-- The clamped offsets of $\mathsf{Garble}_1$ (Fig.~7) cancel: $\sum_{j=0}^{\ell-1} (2-\omega)^j
    K_j = 0$ for every offset randomness, because $K_0 = -\sum_{j \geq 1} (2-\omega)^j K_j$. -/)
  (title := /-- BABE Fig.~7 -/)
  (proof := /-- The clamp lemma cancels the Horner sum of the free offsets $K_1, \ldots, K_{\ell-1}$. -/)]
theorem Construction.offsetsCancel [FieldCertificate] [GroupCertificate]
    (construction : Construction) (randomness : OffsetRandomness) :
    pointHorner radix (construction.offsets randomness) = 0 :=
  pointHornerClampOffsets radix randomness.freeOffsets

end Kriterion.ArgoMAC
