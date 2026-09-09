import Proof.EncPRFGame

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal

noncomputable section

/-- A finite source gives the real weighted sum of its conditional event masses. -/
theorem finiteBind_event_mass {Source Output : Type*} [Fintype Source]
    (source : PMF Source) (next : Source → PMF Output) (event : Set Output) :
    ((source.bind next).toOuterMeasure event).toReal =
      ∑ value, (source value).toReal * ((next value).toOuterMeasure event).toReal := by
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro value _
    apply ENNReal.mul_ne_top (source.apply_ne_top value)
    rw [PMF.toOuterMeasure_apply]
    exact (next value).tsum_coe_indicator_ne_top event

/-- A finite mixture preserves a common conditional event bound. -/
theorem finiteBind_event_bound {Source Output : Type*} [Fintype Source]
    (source : PMF Source) (real ideal : Source → PMF Output)
    (event : Set Output) (error : ℝ)
    (bound : ∀ value,
      |((real value).toOuterMeasure event).toReal -
        ((ideal value).toOuterMeasure event).toReal| ≤ error) :
    |((source.bind real).toOuterMeasure event).toReal -
      ((source.bind ideal).toOuterMeasure event).toReal| ≤ error := by
  classical
  rw [finiteBind_event_mass, finiteBind_event_mass, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simp_rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  calc
    _ ≤ ∑ value, (source value).toReal * error :=
      Finset.sum_le_sum fun value _ => mul_le_mul_of_nonneg_left (bound value) ENNReal.toReal_nonneg
    _ = error := by
      have total : (∑ value : Source, (source value).toReal) = 1 := by
        rw [← (tsum_fintype (L := .unconditional _) (fun value : Source => (source value).toReal)),
          ← ENNReal.tsum_toReal_eq source.apply_ne_top, source.tsum_coe]
        rfl
      rw [← Finset.sum_mul, total, one_mul]

variable [Fintype Block] [Fintype BaseField]

/-- A fresh answer becomes the actual answer after a uniform hash-tape update. -/
theorem uniformHashAt_bind {Output : Type*} (hidden : BaseField)
    (observe : EncPRF.HashOracle → (Block × Block) → PMF Output) :
    (PMF.uniformOfFintype (EncPRF.HashOracle × (Block × Block))).bind
        (fun sample => observe (Function.update sample.1 hidden sample.2) sample.2) =
      (PMF.uniformOfFintype EncPRF.HashOracle).bind (fun hash => observe hash (hash hidden)) := by
  have law := congrArg (fun distribution => distribution.bind
    (fun hash => observe hash (hash hidden))) (map_uniform_hash_resample hidden)
  simpa only [PMF.bind_map, Function.comp_def, Function.update_self] using law

/-- This game uses the actual hash answer at the hidden bridge key. -/
def hiddenEncPRFRun {Result : Type} {budget : Nat}
    (source : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget) :=
  (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)).bind fun oracle =>
    withUniformHidden fun hidden =>
      (PMF.uniformOfFintype EncPRF.HashOracle).bind fun hash =>
        let target := EncPRF.transformKey oracle ⟨(hash hidden).1, (hash hidden).2⟩ source
        (hashTranscriptRun (program target)
          {randomness with encPRFOracle := oracle, hashOracle := hash}).map (Prod.mk target)

/-- This source replaces one hash answer with the private fresh whitening pair. -/
def patchedEncPRFRun {Result : Type} {budget : Nat}
    (source : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget) :=
  (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)).bind fun oracle =>
    (PMF.uniformOfFintype (EncPRF.HashOracle × (Block × Block))).bind fun sample =>
      let target := EncPRF.transformKey oracle ⟨sample.2.1, sample.2.2⟩ source
      (withUniformHidden fun hidden => hashTranscriptRun (program target)
        (replaceHashAt {randomness with encPRFOracle := oracle, hashOracle := sample.1}
          hidden sample.2)).map (fun output => (output.1, target, output.2))

/-- This source keeps the fresh whitening pair independent of the public hash tape. -/
def freshHiddenEncPRFRun {Result : Type} {budget : Nat}
    (source : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget) :=
  (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)).bind fun oracle =>
    (PMF.uniformOfFintype (EncPRF.HashOracle × (Block × Block))).bind fun sample =>
      let target := EncPRF.transformKey oracle ⟨sample.2.1, sample.2.2⟩ source
      (withUniformHidden fun _ => hashTranscriptRun (program target)
        {randomness with encPRFOracle := oracle, hashOracle := sample.1}).map
          (fun output => (output.1, target, output.2))

/-- The patched source is exactly the actual hidden-hash game. -/
theorem patchedEncPRFRun_eq_hidden {Result : Type} {budget : Nat}
    (source : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget) :
    patchedEncPRFRun source randomness program = hiddenEncPRFRun source randomness program := by
  simp only [patchedEncPRFRun, hiddenEncPRFRun, withUniformHidden,
    PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg ((PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)).bind)
  funext oracle
  rw [PMF.bind_comm]
  apply congrArg ((PMF.uniformOfFintype BaseField).bind)
  funext hidden
  exact uniformHashAt_bind hidden (fun hash keys =>
    (hashTranscriptRun (program (EncPRF.transformKey oracle ⟨keys.1, keys.2⟩ source))
      {randomness with encPRFOracle := oracle, hashOracle := hash}).map
        (fun output => (hidden, EncPRF.transformKey oracle ⟨keys.1, keys.2⟩ source, output)))

/-- The actual hidden hash answer costs at most q/p to replace by a fresh private pair. -/
theorem hiddenEncPRFRun_fresh_bound {Result : Type} {budget : Nat}
    (source : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget)
    (event : Set (BaseField × InputMacKey × Result × List (Sigma Garbling.oracleSpec.Answer))) :
    |((hiddenEncPRFRun source randomness program).toOuterMeasure event).toReal -
      ((freshHiddenEncPRFRun source randomness program).toOuterMeasure event).toReal| ≤
        (budget : ℝ) / baseFieldModulus := by
  rw [← patchedEncPRFRun_eq_hidden]
  unfold patchedEncPRFRun freshHiddenEncPRFRun
  apply finiteBind_event_bound
  intro oracle
  apply finiteBind_event_bound
  intro sample
  simp only [PMF.toOuterMeasure_map_apply]
  exact replaceHashAt_event_bound
    (program (EncPRF.transformKey oracle ⟨sample.2.1, sample.2.2⟩ source))
    {randomness with encPRFOracle := oracle, hashOracle := sample.1}
    (fun _ => sample.2) _

/-- This ideal game samples the hidden key and the linked key independently. -/
def independentHiddenEncPRFRun {Result : Type} {budget : Nat}
    (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget) :=
  (PMF.uniformOfFintype EncPRF.HashOracle).bind fun hash =>
    (PMF.uniformOfFintype BaseField).bind fun hidden =>
      (idealEncPRFRun {randomness with hashOracle := hash} program).map (Prod.mk hidden)

/-- The fresh hidden source contains the exact fresh-whitening game. -/
theorem freshHiddenEncPRFRun_factor {Result : Type} {budget : Nat}
    (source : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget) :
    freshHiddenEncPRFRun source randomness program =
      (PMF.uniformOfFintype EncPRF.HashOracle).bind (fun hash =>
        (PMF.uniformOfFintype BaseField).bind (fun hidden =>
          (realEncPRFRun source {randomness with hashOracle := hash} program).map (Prod.mk hidden))) := by
  simp only [freshHiddenEncPRFRun, realEncPRFRun,
    uniform_prod_eq_bind (First := EncPRF.HashOracle) (Second := Block × Block),
    uniform_prod_eq_bind (First := Block × Block)
      (Second := PermutationOracle EncPRF.PermutationIndex Block), PMF.bind_bind,
    PMF.bind_map, withUniformHidden, PMF.map_bind, PMF.map_comp, Function.comp_def]
  simp_rw [PMF.bind_comm (PMF.uniformOfFintype (Block × Block))
    (PMF.uniformOfFintype EncPRF.HashOracle)]
  rw [PMF.bind_comm (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block))
    (PMF.uniformOfFintype EncPRF.HashOracle)]
  simp_rw [PMF.bind_comm (PMF.uniformOfFintype (Block × Block))
    (PMF.uniformOfFintype BaseField)]
  simp_rw [PMF.bind_comm (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block))
    (PMF.uniformOfFintype BaseField)]

/-- The independent hidden source inherits the complete adaptive whitening bound. -/
theorem freshHiddenEncPRFRun_event_bound {Result : Type} {budget : Nat}
    (source : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget)
    (fits : 2 + budget ≤ Fintype.card Block)
    (event : Set (BaseField × InputMacKey × Result × List (Sigma Garbling.oracleSpec.Answer))) :
    |((freshHiddenEncPRFRun source randomness program).toOuterMeasure event).toReal -
      ((independentHiddenEncPRFRun randomness program).toOuterMeasure event).toReal| ≤
        ((508 + 4 * budget : Nat) : ℝ) / Fintype.card Block := by
  rw [freshHiddenEncPRFRun_factor]
  unfold independentHiddenEncPRFRun
  apply finiteBind_event_bound
  intro hash
  apply finiteBind_event_bound
  intro hidden
  simp only [PMF.toOuterMeasure_map_apply]
  exact encPRFRun_event_bound source {randomness with hashOracle := hash} program fits _

/-- The actual hidden hash link has the hash-query loss and the adaptive whitening loss. -/
theorem hiddenEncPRFRun_event_bound {Result : Type} {budget : Nat}
    (source : InputMacKey) (randomness : Garbling.Randomness)
    (program : InputMacKey → OracleProgram Garbling.oracleSpec Result budget)
    (fits : 2 + budget ≤ Fintype.card Block)
    (event : Set (BaseField × InputMacKey × Result × List (Sigma Garbling.oracleSpec.Answer))) :
    |((hiddenEncPRFRun source randomness program).toOuterMeasure event).toReal -
      ((independentHiddenEncPRFRun randomness program).toOuterMeasure event).toReal| ≤
        (budget : ℝ) / baseFieldModulus +
          ((508 + 4 * budget : Nat) : ℝ) / Fintype.card Block := by
  apply (abs_sub_le _ ((freshHiddenEncPRFRun source randomness program).toOuterMeasure event).toReal _).trans
  exact add_le_add (hiddenEncPRFRun_fresh_bound source randomness program event)
    (freshHiddenEncPRFRun_event_bound source randomness program fits event)

end

end Kriterion.ArgoMAC.Security
