/-
Blueprint nodes for the lamport compatibility proof.
-/
import Architect
import Batteries.Tactic.OpenPrivate
import Blueprint.Correctness
import Construction.Garbling
import Proof.LamportCompatibility.Labels
import Proof.SharedGarbling

open private appendGetLow selectedLabelsEncodeLow keyPairsGetLow appendGetHigh selectedLabelsEncodeHigh keyPairsGetHigh from Proof.LamportCompatibility.Labels

attribute [blueprint "Shared.programLamportCompatible"
  (statement := /-- Lamport compatibility (Eqs.~15--16). The Lamport key pairs $\{(L^0_{x,i}, L^1_{x,i}),
    (L^0_{y,i}, L^1_{y,i})\}_{i < 254}$ of $\mathsf{ek}$ and the bit decomposition $\mathbf{b}$ of
    $\pi$ select exactly the labels $\mathsf{Encode}(\mathsf{ek}, \pi)$, so the input labels are the
    Lamport signature of $\pi$. -/)
  (title := /-- BABE Eqs.~15--16 -/)] Kriterion.ArgoMAC.Shared.programLamportCompatible

attribute [blueprint "Lamport.keyPairs"
  (statement := /-- The Lamport secret key of $\mathsf{ek}_3$. Slot $i < 254$ holds $(L^0_{x,i}, L^1_{x,i})$ and
    slot $i \geq 254$ holds $(L^0_{y,i-254}, L^1_{y,i-254})$. -/)
  (title := /-- BABE Section~5.1 -/)] Kriterion.ArgoMAC.Lamport.keyPairs

attribute [blueprint "Lamport.selectedLabels_eq"
  (statement := /-- $\mathsf{Encode}_3(\mathsf{ek}_3, \mathbf{b}) = \{L^{x_i(\pi)}_{x,i}, L^{y_i(\pi)}_{y,i}\}_{i <
    254}$ equals the Lamport signature of the bits $\mathbf{b}$ of $\pi$ under the key pairs. -/)
  (title := /-- BABE Eqs.~15--16 -/)
  (proof := /-- Rewrite $\mathbf{b}$ as an append with \cref{Lamport.affineLamportBits_eq_append}. Compare index
    by index. For $i < 254$ use \cref{Lamport.appendGetLow}, \cref{Lamport.selectedLabelsEncodeLow},
    and \cref{Lamport.keyPairsGetLow}. For $i \geq 254$ use \cref{Lamport.appendGetHigh},
    \cref{Lamport.selectedLabelsEncodeHigh}, and \cref{Lamport.keyPairsGetHigh}. -/)] Kriterion.ArgoMAC.Lamport.selectedLabels_eq

attribute [blueprint "Lamport.affineLamportBits_eq_append"
  (statement := /-- The bit decomposition $\mathbf{b}$ of $\pi$ is the $254$ bits of $y(\pi)$ appended to the $254$
    bits of $x(\pi)$. -/)
  (title := /-- BABE Section~5.1 -/)
  (proof := /-- Compare the natural values. The appended value is $y(\pi)$ shifted by $254$ bits or $x(\pi)$.
    Both coordinates are below $2^{254}$, so no reduction occurs. -/)] Kriterion.ArgoMAC.Lamport.affineLamportBits_eq_append

attribute [blueprint "Lamport.appendGetLow"
  (statement := /-- For $i < 254$, bit $i$ of the appended vector is bit $i$ of the low vector. -/)
  (title := /-- BABE Section~5.1 -/)
  (proof := /-- The bit of an appended vector below the low width reads the low vector. -/)] appendGetLow

attribute [blueprint "Lamport.selectedLabelsEncodeLow"
  (statement := /-- For $i < 254$, label $i$ of $\mathsf{Encode}_3(\mathsf{ek}_3, \mathbf{b})$ is
    $L^{x_i(\pi)}_{x,i}$. -/)
  (title := /-- BABE Section~5.1 -/)
  (proof := /-- Unfold the selected labels and the encoding. The low index selects the $x$ coordinate encoding. -/)] selectedLabelsEncodeLow

attribute [blueprint "Lamport.keyPairsGetLow"
  (statement := /-- For $i < 254$, key pair $i$ is $(L^0_{x,i}, L^1_{x,i})$. -/)
  (title := /-- BABE Section~5.1 -/)
  (proof := /-- Unfold the key pairs. The low index selects the $x$ item. -/)] keyPairsGetLow

attribute [blueprint "Lamport.appendGetHigh"
  (statement := /-- For $i \geq 254$, bit $i$ of the appended vector is bit $i - 254$ of the high vector. -/)
  (title := /-- BABE Section~5.1 -/)
  (proof := /-- The bit of an appended vector at or above the low width reads the high vector at $i - 254$. -/)] appendGetHigh

attribute [blueprint "Lamport.selectedLabelsEncodeHigh"
  (statement := /-- For $i \geq 254$, label $i$ of $\mathsf{Encode}_3(\mathsf{ek}_3, \mathbf{b})$ is
    $L^{y_{i-254}(\pi)}_{y,i-254}$. -/)
  (title := /-- BABE Section~5.1 -/)
  (proof := /-- Unfold the selected labels and the encoding. The high index selects the $y$ coordinate encoding
    at $i - 254$. -/)] selectedLabelsEncodeHigh

attribute [blueprint "Lamport.keyPairsGetHigh"
  (statement := /-- For $i \geq 254$, key pair $i$ is $(L^0_{y,i-254}, L^1_{y,i-254})$. -/)
  (title := /-- BABE Section~5.1 -/)
  (proof := /-- Unfold the key pairs. The high index selects the $y$ item at $i - 254$. -/)] keyPairsGetHigh
