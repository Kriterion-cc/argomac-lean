import Proof.SimulatorFiniteArithmetic
import Proof.SimulatorCutoff

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions OperationalOracle
open SimulatorSampling BoundedIntegerSampling
namespace SimulatorMachine
noncomputable section

/-- This continuation stops the experiment after a failed draw. -/
def optionalPMF {A B : Type} (next : A → PMF (Option B)) : Option A → PMF (Option B)
  | none => PMF.pure none
  | some value => next value

private theorem optionalPMF_bitCode {A B : Type} (next : A → BitCode (Option B))
    (value : Option A) :
    (optional next value).law = optionalPMF (fun item => (next item).law) value := by
  cases value <;> rfl

private theorem option_sum {A : Type} (f : Option A → ENNReal) :
    (∑' value, f value) = f none + ∑' value, f (some value) := by
  rw [← (Equiv.optionEquivSumPUnit.{0, 0} A).symm.tsum_eq]
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
  simp [add_comm]

/-- This relation bounds the full successful output distribution. -/
def CutoffLaw {A : Type} (attempts count : Nat) (exact : PMF A) (finite : PMF (Option A)) : Prop :=
  (∀ value, retained attempts ^ count * exact value ≤ finite (some value)) ∧
    (∀ value, finite (some value) ≤ exact value)

/-- A finite private sampler satisfies the output relation. -/
theorem CutoffLaw.code {A : Type} {count : Nat} (attempts : Nat) (code : Code A count) :
    CutoffLaw attempts count code.law (code.cutoff attempts).law :=
  ⟨code.cutoff_lower attempts, code.cutoff_upper attempts⟩

/-- A finite machine program satisfies the output relation. -/
theorem CutoffLaw.program {oracle : OracleSpec.{0, 0}} {A State : Type} {count : Nat}
    (sparse : ∀ query, State → Draw (oracle.Answer query × State))
    (attempts : Nat) (program : Program oracle A count) (state : State) :
    CutoffLaw attempts count (program.sampledLaw sparse state)
      (program.cutoff sparse attempts state).law :=
  ⟨program.cutoff_lower sparse attempts state, program.cutoff_upper sparse attempts state⟩

/-- A successful pure sample consumes no bounded integer draws. -/
theorem CutoffLaw.exact {A : Type} (attempts : Nat) (distribution : PMF A) :
    CutoffLaw attempts 0 distribution (distribution.map some) := by
  classical
  have same (value : A) : (distribution.map some) (some value) = distribution value := by
    rw [PMF.map_apply]
    calc
      _ = ∑' item, if item = value then distribution value else 0 := by
        congr 1
        funext item
        by_cases h : item = value
        · subst item; simp
        · simp [h, Ne.symm h]
      _ = _ := tsum_ite_eq _ _
  constructor <;> intro value <;> simp only [pow_zero, one_mul, same, le_refl]

/-- A larger draw budget preserves the output relation. -/
theorem CutoffLaw.weaken {A : Type} {attempts first second : Nat}
    {exact : PMF A} {finite : PMF (Option A)}
    (law : CutoffLaw attempts first exact finite) (bounded : first ≤ second) :
    CutoffLaw attempts second exact finite := by
  refine ⟨fun value => ?_, law.2⟩
  exact (mul_le_mul_right' (pow_le_pow_right_of_le_one'
    (tsub_le_self : retained attempts ≤ 1) bounded) _).trans (law.1 value)

private theorem optionalPMF_apply {A B : Type} (source : PMF (Option A))
    (next : A → PMF (Option B)) (value : B) :
    (source.bind (optionalPMF next)) (some value) =
      ∑' item, source (some item) * next item (some value) := by
  rw [PMF.bind_apply, option_sum]
  simp only [optionalPMF, PMF.pure_apply, reduceCtorEq, if_false, mul_zero, zero_add]

/-- Adaptive composition adds the two draw budgets. -/
theorem CutoffLaw.bind {A B : Type} {attempts first second : Nat}
    {source : PMF A} {finiteSource : PMF (Option A)}
    {next : A → PMF B} {finiteNext : A → PMF (Option B)}
    (left : CutoffLaw attempts first source finiteSource)
    (right : ∀ item, CutoffLaw attempts second (next item) (finiteNext item)) :
    CutoffLaw attempts (first + second) (source.bind next)
      (finiteSource.bind (optionalPMF finiteNext)) := by
  constructor
  · intro value
    rw [optionalPMF_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro item
    calc
      retained attempts ^ (first + second) * (source item * next item value) =
          (retained attempts ^ first * source item) *
            (retained attempts ^ second * next item value) := by rw [pow_add]; ac_rfl
      _ ≤ _ := mul_le_mul' (left.1 item) ((right item).1 value)
  · intro value
    rw [optionalPMF_apply, PMF.bind_apply]
    exact ENNReal.tsum_le_tsum fun item => mul_le_mul' (left.2 item) ((right item).2 value)

/-- Ordinary private adversary randomness adds no simulator draw loss. -/
theorem CutoffLaw.sample {A B : Type} {attempts count : Nat}
    (source : PMF A) {next : A → PMF B} {finiteNext : A → PMF (Option B)}
    (law : ∀ item, CutoffLaw attempts count (next item) (finiteNext item)) :
    CutoffLaw attempts count (source.bind next) (source.bind finiteNext) := by
  simpa only [Nat.zero_add, PMF.bind_map, Function.comp_def, optionalPMF] using
    (CutoffLaw.exact attempts source).bind law

/-- A deterministic observation preserves the output relation. -/
theorem CutoffLaw.map {A B : Type} {attempts count : Nat}
    {exact : PMF A} {finite : PMF (Option A)}
    (law : CutoffLaw attempts count exact finite) (observe : A → B) :
    CutoffLaw attempts count (exact.map observe) (finite.map (Option.map observe)) := by
  have result := law.bind (fun item => CutoffLaw.exact attempts (PMF.pure (observe item)))
  have same : (optionalPMF (fun item => (PMF.pure (observe item)).map some)) =
      (fun value => PMF.pure (Option.map observe value)) := by
    funext value
    cases value <;> simp only [optionalPMF, PMF.pure_map, Option.map]
  rw [same] at result
  exact result

/-- This interpreter applies the finite retry limit to each adversary oracle query. -/
def runCutoff {oracle : OracleSpec.{0, 0}} {A State : Type}
    (sparse : ∀ query, State → Draw (oracle.Answer query × State)) (attempts : Nat) :
    {budget : Nat} → OracleProgram oracle A budget → State → PMF (Option (A × State))
  | _, .pure distribution, state => distribution.map (fun value => some (value, state))
  | _, .sample distribution next, state => distribution.bind (fun item => runCutoff sparse attempts (next item) state)
  | _, .query request next, state => (cutoffDraw attempts (sparse request state)).law.bind
      (optionalPMF fun answer => runCutoff sparse attempts (next answer.1) answer.2)

/-- The finite adversary interpreter preserves the full adaptive output relation. -/
theorem runCutoff_law {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (sparse : ∀ query, State → Draw (oracle.Answer query × State))
    (attempts : Nat) (program : OracleProgram oracle A budget) (state : State) :
    CutoffLaw attempts budget
      (runSampled (fun query state => (sparse query state).distribution) program state)
      (runCutoff sparse attempts program state) := by
  induction program generalizing state with
  | pure distribution =>
      simpa only [runCutoff, runSampled, PMF.map_comp, Function.comp_def] using
        (CutoffLaw.exact attempts (distribution.map (fun value => (value, state)))).weaken (Nat.zero_le _)
  | sample distribution next ih => exact CutoffLaw.sample distribution (fun item => ih item state)
  | @query budget request next ih =>
      have drawLaw : CutoffLaw attempts 1 (sparse request state).distribution
          (cutoffDraw attempts (sparse request state)).law :=
        ⟨by simpa only [pow_one] using cutoffDraw_lower attempts (sparse request state),
          cutoffDraw_upper attempts (sparse request state)⟩
      simpa only [Nat.add_comm, runCutoff, runSampled] using
        drawLaw.bind (fun answer => ih answer.1 answer.2)


end

/-- The online encoder uses a finite sampler for its private coins and oracle draws. -/
def encodeCutoff [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (coin : OfflineCoin) (input : AffineInput) (output : Option Point)
    (state : SparseState) : BitCode (Option (Garbling.Labels × SparseState)) :=
  match output with
  | none => (invalidProgram (privateView coin) input).cutoff sparseDraw attempts state
  | some point => (online.cutoff attempts).bind (optional fun sample =>
      (validProgram (privateView coin) input point (Vector.ofFn sample.1) sample.2).cutoff
        sparseDraw attempts state)

noncomputable section

/-- The finite online encoder retains the joint label and oracle distribution. -/
theorem encodeCutoff_law [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (coin : OfflineCoin) (input : AffineInput) (output : Option Point)
    (state : SparseState) :
    CutoffLaw attempts 905946 (runSampled sparseHandler (encodeProgram coin input output) state)
      (encodeCutoff attempts coin input output state).law := by
  cases output with
  | none =>
      change CutoffLaw attempts 905946
        (runSampled (fun query state => (sparseDraw query state).distribution)
          (invalidProgram (privateView coin) input).toOracle state)
        ((invalidProgram (privateView coin) input).cutoff sparseDraw attempts state).law
      rw [Program.sampledLaw_toOracle]
      exact (CutoffLaw.program sparseDraw attempts (invalidProgram (privateView coin) input) state).weaken
        (by norm_num : 3810 ≤ 905946)
  | some point =>
      have law := (CutoffLaw.code attempts online).bind (fun sample =>
        CutoffLaw.program sparseDraw attempts
          (validProgram (privateView coin) input point (Vector.ofFn sample.1) sample.2) state)
      rw [encodeProgram, sampled_append]
      change CutoffLaw attempts 905946
        ((online.law.map (fun sample => (sample, state))).bind (fun sample =>
          runSampled (fun query state => (sparseDraw query state).distribution)
            (validProgram (privateView coin) input point (Vector.ofFn sample.1.1) sample.1.2).toOracle sample.2)) _
      simp only [PMF.bind_map, Function.comp_def, Program.sampledLaw_toOracle]
      change CutoffLaw attempts 905946 _
        ((online.cutoff attempts).bind (optional fun sample =>
          (validProgram (privateView coin) input point (Vector.ofFn sample.1) sample.2).cutoff
            sparseDraw attempts state)).law
      rw [BitCode.bind_law]
      simp only [optionalPMF_bitCode]
      exact law

/-- This continuation applies the finite retry limit to all three adversary phases. -/
def finiteContinuation [FieldCertificate] [GroupCertificate] {Aux : Type}
    (attempts : Nat) (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) (coin : OfflineCoin) (state : SparseState) :
    PMF (Option Bool) :=
  (runCutoff externalDraw attempts (adversary.prepare parameter auxiliary) state).bind
    (optionalPMF fun prepared =>
      (runCutoff externalDraw attempts
        (adversary.chooseInput parameter (privateView coin).table auxiliary prepared.1) prepared.2).bind
        (optionalPMF fun selected =>
          (encodeCutoff attempts coin selected.1.1
            ((Garbling.garbledCircuit construction).function scalar selected.1.1) selected.2).law.bind
            (optionalPMF fun encoded =>
              (runCutoff externalDraw attempts
                (adversary.decide parameter (privateView coin).table encoded.1 auxiliary selected.1.2)
                encoded.2).map (Option.map Prod.fst))))

/-- The continuation loss counts every external query and every online simulator draw. -/
theorem finiteContinuation_law [FieldCertificate] [GroupCertificate] {Aux : Type}
    (attempts : Nat) (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) (coin : OfflineCoin) (state : SparseState) :
    CutoffLaw attempts
      (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter + 905946)
      (sparseContinuation adversary parameter scalar auxiliary coin state)
      (finiteContinuation attempts adversary parameter scalar auxiliary coin state) := by
  have law := (runCutoff_law externalDraw attempts (adversary.prepare parameter auxiliary) state).bind
    (fun prepared => (runCutoff_law externalDraw attempts
      (adversary.chooseInput parameter (privateView coin).table auxiliary prepared.1) prepared.2).bind
      (fun selected => (encodeCutoff_law attempts coin selected.1.1
        ((Garbling.garbledCircuit construction).function scalar selected.1.1) selected.2).bind
        (fun encoded => (runCutoff_law externalDraw attempts
          (adversary.decide parameter (privateView coin).table encoded.1 auxiliary selected.1.2)
          encoded.2).map Prod.fst)))
  simpa only [sparseContinuation, finiteContinuation, externalHandler,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using law

/-- This optional game stops after any failed simulator rejection sampler. -/
def finiteIdealOption [FieldCertificate] [GroupCertificate] {Aux : Type}
    (attempts : Nat) (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) : PMF (Option Bool) :=
  (offline.cutoff attempts).law.bind (optionalPMF fun coin =>
    finiteContinuation attempts adversary parameter scalar auxiliary coin (initial initialMetadata))

/-- The whole finite game retains the exact successful decision distribution. -/
theorem finiteIdealOption_law [FieldCertificate] [GroupCertificate] {Aux : Type}
    (attempts : Nat) (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) :
    CutoffLaw attempts
      (1813496 + adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter)
      (operationalIdealGame adversary parameter scalar auxiliary)
      (finiteIdealOption attempts adversary parameter scalar auxiliary) := by
  have law := (CutoffLaw.code attempts offline).bind (fun coin =>
    finiteContinuation_law attempts adversary parameter scalar auxiliary coin (initial initialMetadata))
  convert law using 1
  omega


/-- The finite output relation bounds the probability of a failed draw. -/
theorem CutoffLaw.failure {A : Type} {attempts count : Nat}
    {exact : PMF A} {finite : PMF (Option A)} (law : CutoffLaw attempts count exact finite) :
    finite none ≤ count * (2 : ENNReal)⁻¹ ^ attempts := by
  have total := finite.tsum_coe
  rw [option_sum] at total
  have lower : retained attempts ^ count ≤ ∑' value, finite (some value) := by
    calc
      retained attempts ^ count = retained attempts ^ count * ∑' value, exact value := by
        rw [exact.tsum_coe, mul_one]
      _ = _ := ENNReal.tsum_mul_left.symm
      _ ≤ _ := ENNReal.tsum_le_tsum law.1
  exact (ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top total).le.trans
    ((tsub_le_tsub_left lower 1).trans
      (loss_pow_le _ (pow_le_one₀ (zero_le _) (by norm_num)) count))

/-- The finite output relation bounds the real probability lost at each output. -/
theorem CutoffLaw.point_error {A : Type} {attempts count : Nat}
    {exact : PMF A} {finite : PMF (Option A)} (law : CutoffLaw attempts count exact finite)
    (value : A) :
    (exact value).toReal - (finite (some value)).toReal ≤
      (count : ℝ) * (2 : ℝ)⁻¹ ^ attempts := by
  have retainedLe : retained attempts ^ count ≤ 1 :=
    pow_le_one₀ (zero_le _) (tsub_le_self : retained attempts ≤ 1)
  have lower := ENNReal.toReal_mono (finite.apply_ne_top _) (law.1 value)
  have pointLe := ENNReal.toReal_mono ENNReal.one_ne_top (exact.coe_le_one value)
  have factorLe := ENNReal.toReal_mono ENNReal.one_ne_top retainedLe
  have loss := loss_pow_le ((2 : ENNReal)⁻¹ ^ attempts)
    (pow_le_one₀ (zero_le _) (by norm_num)) count
  have realLoss := ENNReal.toReal_mono (by finiteness) loss
  change (1 - retained attempts ^ count).toReal ≤ _ at realLoss
  rw [ENNReal.toReal_sub_of_le retainedLe ENNReal.one_ne_top] at realLoss
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one] at lower pointLe factorLe realLoss ⊢
  nlinarith

/-- A failed simulator draw returns the fixed decision false. -/
def finiteIdealGame [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  (finiteIdealOption 256 adversary parameter scalar auxiliary).map (fun value => value.getD false)

/-- The fixed failure decision adds no mass to the decision true. -/
theorem finiteIdealGame_true [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) :
    finiteIdealGame adversary parameter scalar auxiliary true =
      finiteIdealOption 256 adversary parameter scalar auxiliary (some true) := by
  rw [finiteIdealGame, PMF.map_apply, option_sum, tsum_bool]
  simp

/-- The finite retry simulator changes the exact game by at most the complete draw residual. -/
theorem finiteIdealGame_error [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) :
    advantage (operationalIdealGame adversary parameter scalar auxiliary)
      (finiteIdealGame adversary parameter scalar auxiliary) ≤
      cutoffResidual (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter) := by
  have law := finiteIdealOption_law 256 adversary parameter scalar auxiliary
  have upper := ENNReal.toReal_mono
    ((operationalIdealGame adversary parameter scalar auxiliary).apply_ne_top true) (law.2 true)
  unfold advantage
  rw [finiteIdealGame_true, abs_of_nonneg (sub_nonneg.mpr upper)]
  convert law.point_error true using 1
  simp only [cutoffResidual, Nat.cast_add, inv_pow, div_eq_mul_inv]
  ring

/-- The finite retry simulator preserves the 100-bit three-phase privacy bound. -/
theorem finitePrivacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type} (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) (witness : Garbling.Randomness) :
    WorkPerAdvantage 100
      (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter + 1)
      (advantage (ThreePhase.realGame adversary parameter scalar auxiliary witness)
        (finiteIdealGame adversary parameter scalar auxiliary)) := by
  let queries := adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
    adversary.decisionQueryBudget parameter
  by_cases small : queries < 2 ^ 100
  · have first := operational_small_error adversary parameter scalar auxiliary witness small
    have second := finiteIdealGame_error adversary parameter scalar auxiliary
    have triangle := abs_sub_le
      ((ThreePhase.realGame adversary parameter scalar auxiliary witness) true).toReal
      ((operationalIdealGame adversary parameter scalar auxiliary) true).toReal
      ((finiteIdealGame adversary parameter scalar auxiliary) true).toReal
    have bound : advantage (ThreePhase.realGame adversary parameter scalar auxiliary witness)
        (finiteIdealGame adversary parameter scalar auxiliary) ≤
        adaptiveErrorEnvelope queries + cutoffResidual queries :=
      triangle.trans (add_le_add first second)
    exact (mul_le_mul_of_nonneg_right bound (by positivity)).trans (cutoffEnvelope_has100Bits queries)
  · exact largeBudget_has100Bits _ _ queries (Nat.le_of_not_gt small)

end
end SimulatorMachine
end Kriterion.ArgoMAC.Security
