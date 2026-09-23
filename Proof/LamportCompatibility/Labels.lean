/-
This file proves that ArgoMAC input labels match the 508-bit Lamport order.
-/

import Construction.Garbling
import Solution
import Architect

namespace Kriterion.ArgoMAC.Lamport

open BN254 Cryptography

@[blueprint "Lamport.affineLamportBits_eq_append"
  (statement := /-- The bit decomposition $\mathbf{b}$ of $\pi$ is the $254$ bits of $y(\pi)$ appended to the $254$
    bits of $x(\pi)$. -/)
  (title := /-- BABE Section~5.1 -/)]
theorem affineLamportBits_eq_append (input : AffineInput) :
    affineLamportBits input = coordinateBits input.y ++ coordinateBits input.x := by
  /-- Compare the natural values. The appended value is $y(\pi)$ shifted by $254$ bits or $x(\pi)$.
    Both coordinates are below $2^{254}$, so no reduction occurs. -/
  apply BitVec.eq_of_toNat_eq
  simp only [affineLamportBits, BitVec.toNat_ofNat, BitVec.toNat_append,
    coordinateBitsToNat]
  rw [Nat.mod_eq_of_lt]
  · change input.x.val + input.y.val * 2 ^ 254 =
      input.y.val <<< 254 ||| input.x.val
    calc
      input.x.val + input.y.val * 2 ^ 254 =
          input.y.val <<< 254 + input.x.val := by
        rw [Nat.shiftLeft_eq]
        omega
      _ = input.y.val <<< 254 ||| input.x.val :=
        Nat.shiftLeft_add_eq_or_of_lt (lt_trans input.x.val_lt (by decide)) _
  · have xBound : input.x.val < 2 ^ 254 := lt_trans input.x.val_lt (by decide)
    have yBound : input.y.val < 2 ^ 254 := lt_trans input.y.val_lt (by decide)
    omega

@[blueprint "Lamport.appendGetLow"
  (statement := /-- For $i < 254$, bit $i$ of the appended vector is bit $i$ of the low vector. -/)
  (title := /-- BABE Section~5.1 -/)
  (proof := /-- The bit of an appended vector below the low width reads the low vector. -/)]
private theorem appendGetLow (highBits lowBits : BitVec 254) (index : Nat)
    (bound : index < 508) (low : index < 254) :
    (highBits ++ lowBits).getLsb ⟨index, bound⟩ =
      lowBits.getLsb ⟨index, low⟩ := by
  change (highBits ++ lowBits).getLsbD index = lowBits.getLsbD index
  rw [BitVec.getLsbD_append, if_pos low]

@[blueprint "Lamport.appendGetHigh"
  (statement := /-- For $i \geq 254$, bit $i$ of the appended vector is bit $i - 254$ of the high vector. -/)
  (title := /-- BABE Section~5.1 -/)
  (proof := /-- The bit of an appended vector at or above the low width reads the high vector at $i - 254$. -/)]
private theorem appendGetHigh (highBits lowBits : BitVec 254) (index : Nat)
    (bound : index < 508) (high : 254 ≤ index) :
    (highBits ++ lowBits).getLsb ⟨index, bound⟩ =
      highBits.getLsb ⟨index - 254, by omega⟩ := by
  change (highBits ++ lowBits).getLsbD index = highBits.getLsbD (index - 254)
  rw [BitVec.getLsbD_append, if_neg (Nat.not_lt.mpr high)]

@[blueprint "Lamport.keyPairsGetLow"
  (statement := /-- For $i < 254$, key pair $i$ is $(L^0_{x,i}, L^1_{x,i})$. -/)
  (title := /-- BABE Section~5.1 -/)
  (proof := /-- Unfold the key pairs. The low index selects the $x$ item. -/)]
private theorem keyPairsGetLow (key : InputMacKey) (index : Nat)
    (bound : index < 508) (low : index < 254) :
    (keyPairs key)[index] =
      ((key.x.get ⟨index, low⟩).falseLabel, (key.x.get ⟨index, low⟩).trueLabel) := by
  unfold keyPairs
  rw [Vector.getElem_ofFn bound, dif_pos low]

@[blueprint "Lamport.keyPairsGetHigh"
  (statement := /-- For $i \geq 254$, key pair $i$ is $(L^0_{y,i-254}, L^1_{y,i-254})$. -/)
  (title := /-- BABE Section~5.1 -/)
  (proof := /-- Unfold the key pairs. The high index selects the $y$ item at $i - 254$. -/)]
private theorem keyPairsGetHigh (key : InputMacKey) (index : Nat)
    (bound : index < 508) (high : 254 ≤ index) :
    (keyPairs key)[index] =
      ((key.y.get ⟨index - 254, by
        change index - 254 < 254
        omega⟩).falseLabel,
      (key.y.get ⟨index - 254, by
        change index - 254 < 254
        omega⟩).trueLabel) := by
  unfold keyPairs
  rw [Vector.getElem_ofFn bound, dif_neg (Nat.not_lt.mpr high)]

@[blueprint "Lamport.selectedLabelsEncodeLow"
  (statement := /-- For $i < 254$, label $i$ of $\mathsf{Encode}_3(\mathsf{ek}_3, \mathbf{b})$ is
    $L^{x_i(\pi)}_{x,i}$. -/)
  (title := /-- BABE Section~5.1 -/)
  (proof := /-- Unfold the selected labels and the encoding. The low index selects the $x$ coordinate encoding. -/)]
private theorem selectedLabelsEncodeLow (key : InputMacKey) (input : AffineInput)
    (index : Nat) (bound : index < 508) (low : index < 254) :
    (selectedLabels (key.encodeAffine input))[index] =
      BitAdaptor.encode (key.x.get ⟨index, low⟩)
        ((coordinateBits input.x).getLsb ⟨index, low⟩) := by
  unfold selectedLabels InputMacKey.encodeAffine InputMacKey.encode
  rw [Vector.getElem_ofFn bound, dif_pos low]
  unfold encodeCoordinate
  change (Vector.ofFn fun coordinateIndex =>
    BitAdaptor.encode (key.x.get coordinateIndex)
      ((BitInput.ofAffine input).xBits.getLsb coordinateIndex))[index] = _
  simp only [Vector.getElem_ofFn]
  rfl

@[blueprint "Lamport.selectedLabelsEncodeHigh"
  (statement := /-- For $i \geq 254$, label $i$ of $\mathsf{Encode}_3(\mathsf{ek}_3, \mathbf{b})$ is
    $L^{y_{i-254}(\pi)}_{y,i-254}$. -/)
  (title := /-- BABE Section~5.1 -/)
  (proof := /-- Unfold the selected labels and the encoding. The high index selects the $y$ coordinate encoding
    at $i - 254$. -/)]
private theorem selectedLabelsEncodeHigh (key : InputMacKey) (input : AffineInput)
    (index : Nat) (bound : index < 508) (high : 254 ≤ index) :
    (selectedLabels (key.encodeAffine input))[index] =
      BitAdaptor.encode (key.y.get ⟨index - 254, by
        change index - 254 < 254
        omega⟩)
        ((coordinateBits input.y).getLsb ⟨index - 254, by
          change index - 254 < 254
          omega⟩) := by
  unfold selectedLabels InputMacKey.encodeAffine InputMacKey.encode
  rw [Vector.getElem_ofFn bound, dif_neg (Nat.not_lt.mpr high)]
  unfold encodeCoordinate
  have yBound : index - 254 < coordinateBitCount := by
    change index - 254 < 254
    omega
  change (Vector.ofFn fun coordinateIndex =>
    BitAdaptor.encode (key.y.get coordinateIndex)
      ((BitInput.ofAffine input).yBits.getLsb coordinateIndex))[index - 254] = _
  simp only [Vector.getElem_ofFn]
  rfl

@[blueprint "Lamport.selectedLabels_eq"
  (statement := /-- $\mathsf{Encode}_3(\mathsf{ek}_3, \mathbf{b}) = \{L^{x_i(\pi)}_{x,i}, L^{y_i(\pi)}_{y,i}\}_{i <
    254}$ equals the Lamport signature of the bits $\mathbf{b}$ of $\pi$ under the key pairs. -/)
  (title := /-- BABE Eqs.~15--16 -/)]
theorem selectedLabels_eq (key : InputMacKey) (input : AffineInput) :
    selectedLabels (key.encodeAffine input) =
      GarbledCircuit.selectLamportLabels (keyPairs key) (affineLamportBits input) := by
  /-- Rewrite $\mathbf{b}$ as an append with \cref{Lamport.affineLamportBits_eq_append}. Compare index
    by index. For $i < 254$ use \cref{Lamport.appendGetLow}, \cref{Lamport.selectedLabelsEncodeLow},
    and \cref{Lamport.keyPairsGetLow}. For $i \geq 254$ use \cref{Lamport.appendGetHigh},
    \cref{Lamport.selectedLabelsEncodeHigh}, and \cref{Lamport.keyPairsGetHigh}. -/
  rw [affineLamportBits_eq_append]
  apply Vector.ext
  intro index bound
  by_cases low : index < 254
  · have bitEq := appendGetLow (coordinateBits input.y) (coordinateBits input.x)
      index bound low
    rw [selectedLabelsEncodeLow key input index bound low]
    unfold GarbledCircuit.selectLamportLabels; rw [Vector.getElem_ofFn]
    change BitAdaptor.encode (key.x.get ⟨index, low⟩)
        ((coordinateBits input.x).getLsb ⟨index, low⟩) =
      if (coordinateBits input.y ++ coordinateBits input.x).getLsb ⟨index, bound⟩
      then (keyPairs key)[index].2 else (keyPairs key)[index].1
    rw [bitEq]
    rw [keyPairsGetLow key index bound low]
    rfl
  · have high : 254 ≤ index := Nat.le_of_not_gt low
    have bitEq := appendGetHigh (coordinateBits input.y) (coordinateBits input.x)
      index bound high
    rw [selectedLabelsEncodeHigh key input index bound high]
    unfold GarbledCircuit.selectLamportLabels; rw [Vector.getElem_ofFn]
    change BitAdaptor.encode (key.y.get ⟨index - 254, by
          change index - 254 < 254
          omega⟩)
        ((coordinateBits input.y).getLsb ⟨index - 254, by
          change index - 254 < 254
          omega⟩) =
      if (coordinateBits input.y ++ coordinateBits input.x).getLsb ⟨index, bound⟩
      then (keyPairs key)[index].2 else (keyPairs key)[index].1
    rw [bitEq]
    rw [keyPairsGetHigh key index bound high]
    rfl

/-- The wire adapter restores exactly the internal labels for the chosen input. -/
@[blueprint "Lamport.restore_selected"
  (statement := /-- The wire adapter inverts the Lamport encoding. For every input $\pi$ and every label vector $L =
    \{L^{x_i(\pi)}_{x,i}, L^{y_i(\pi)}_{y,i}\}_{i < 254}$, restoring $L$ from its $508$ Lamport
    signature slots returns the bits of $\pi$ together with $L$. -/)
  (title := /-- BABE Eqs.~15--16 -/)]
theorem restore_selected (input : AffineInput) (mac : InputMac) :
    restore input (selectedLabels mac) = ⟨BitInput.ofAffine input, mac⟩ := by
  /-- Compare the $x$ and $y$ label vectors index by index. For $i < 254$ slot $i$ holds
    $L^{x_i(\pi)}_{x,i}$. For $i \geq 254$ slot $i$ holds $L^{y_{i-254}(\pi)}_{y,i-254}$. -/
  apply congrArg (Garbling.Labels.mk (BitInput.ofAffine input))
  apply InputMac.ext
  · apply Vector.ext
    intro index bound
    simp only [restore, selectedLabels, Vector.getElem_ofFn]
    rw [dif_pos (show index < 254 from bound)]
    rfl
  · apply Vector.ext
    intro index bound
    simp only [restore, selectedLabels, Vector.getElem_ofFn]
    rw [dif_neg (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rfl


end Kriterion.ArgoMAC.Lamport
