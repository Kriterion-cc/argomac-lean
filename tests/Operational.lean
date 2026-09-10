import Proof.SimulatorPrefixCost
import Proof.SimulatorCutoff
import Proof.SimulatorFiniteArithmetic
import Proof.SimulatorSamplingCost

open Kriterion.ArgoMAC Kriterion.ArgoMAC.Security
open Kriterion.ArgoMAC.Security.SimulatorMachine
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.BoundedIntegerSampling
open Kriterion.Cryptography

private def integerSource (size : Nat) (positive : 0 < size) (seed : Nat) : Fin size × Nat :=
  (⟨0, positive⟩, seed + 1)

private def fixedIndex : Pipeline.FixedKeyIndex := ⟨.curve .y4, ⟨0, by decide⟩, .hash 0⟩

private def emptyState : SparseState :=
  ⟨((fun _ => ProgrammedPermutation.empty _), []), ⟨[], [], [], [], none, false⟩⟩

private def collisionTrace : Program combinedSpec (Block × Block) 4 :=
  .query (.inl (.program (fixedIndex, 0, 1))) fun _ =>
  .query (.inr (.fixedForward fixedIndex 0)) fun first =>
  .query (.inl (.program (fixedIndex, 0, 2))) fun _ =>
  .query (.inr (.fixedForward fixedIndex 0)) fun second => .pure (first, second)

private def traceResult :=
  let result := Cost.executeCost integerSource collisionTrace emptyState 0 0
  (result.1.1.1.toNat, result.1.1.2.toNat, result.1.2.1.metadata.bad,
    result.1.2.1.metadata.fixedTranscript.length, result.1.2.2, result.2.1, result.2.2)

/-- The failed program preserves the first mapping and records the collision. -/
example : traceResult = (1, 1, true, 3, 1, 4, 56) := by decide

private def bitSource (width : Nat) (seed : Nat) : Fin (2 ^ width) × Nat :=
  (⟨(if seed = 0 then 3 else 2) % (2 ^ width), Nat.mod_lt _ (Nat.two_pow_pos width)⟩, seed + 1)

/-- One rejected block exhausts the one-retry sampler. -/
example : ((cutoff 3 1).run bitSource 0).1.1 = none := by decide

/-- A second block supplies the requested value after four fair-bit reads. -/
example : (cutoff 3 2).run bitSource 0 = ((some ⟨2, by decide⟩, 2), 4) := by decide

#print axioms operational_small_error
#print axioms cutoffEnvelope_has100Bits
#print axioms Program.cutoff_failure
#print axioms Program.cutoff_bit_bound
#print axioms Cost.executeCost_budget

private def failingBits (width : Nat) (seed : Nat) : Fin (2 ^ width) × Nat :=
  (⟨if seed = 0 then 0 else 2 ^ width - 1, by
    split <;> have := Nat.two_pow_pos width <;> omega⟩, seed + 1)

private def twoDrawTrace : Program combinedSpec Unit 2 :=
  .query (.inr (.fixedForward fixedIndex 0)) fun _ =>
  .query (.inr (.fixedForward fixedIndex 1)) fun _ => .pure ()

private def failedPrefix :=
  let result := Cost.executeCutoffCost failingBits 2 twoDrawTrace emptyState 0 0
  (result.1.1.isNone, result.1.2, result.2)

/-- The failed second draw retains the first request charge and all fair-bit reads. -/
#eval show IO Unit from do
  unless failedPrefix == (true, 3, 2, 31, 385) do
    throw (IO.userError "The sparse prefix cost check failed.")
#print axioms Cost.executeCutoffCost_correct
#print axioms Cost.executeCutoffCost_budget

private def twoPrivateDraws :=
  let draw := SimulatorSamplingCost.FiniteRecipe.draw 3 (by decide) (by decide)
  (draw.pair draw).run 2

/-- The private sampler keeps the first draw charge after the second draw fails. -/
example : (twoPrivateDraws.run failingBits 0) = (((none, 1), 3), 6) := by decide

/-- Two sampled blocks incur eight rejection-control operations. -/
example : (SimulatorRejectionCost.runWithCost bitSource (cutoff 3 2) 0).2 = (2, 8) := by decide
