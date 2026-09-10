import Proof.SimulatorPhaseCost
import Proof.SimulatorExternalCost
import Proof.SimulatorRejectionCost
import Proof.SimulatorOfflineSetup
import Proof.SimulatorPrefixCost
import Proof.SimulatorPublicCost
import Proof.SimulatorSamplingCost
import Proof.SimulatorPrivateCache
import Proof.SimulatorMachineLift
import Proof.SimulatorFinitePrivacy
import Proof.SimulatorScheduleCost
import Proof.SimulatorLinkCost
import Proof.SimulatorLabels
import Proof.SimulatorCommandCost
import Proof.SimulatorMachineCost

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions OperationalOracle
open SimulatorSampling BoundedIntegerSampling SimulatorScheduleCost SimulatorCommandCost
namespace SimulatorMachine
namespace Implementation

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
attribute [local irreducible] SimulatorRejectionCost.PositiveWidths

/-- This expression reads the cached curve targets. -/
def hashWithCost (curve : PreparedCurve) (input : AffineInput) : BaseField × Nat :=
  (curveResultExpr curve.request input curve.tables.x3.targets curve.tables.x5.targets
    curve.tables.x7.targets curve.tables.y4.targets curve.tables.y6.targets).run

theorem hashWithCost_value (curve : PreparedCurve) (input : AffineInput) :
    (hashWithCost curve input).1 = curve.request.result input :=
  curveResultExpr_value _ _ _ _ _ _ _

theorem hashWithCost_bound (curve : PreparedCurve) (input : AffineInput) :
    (hashWithCost curve input).2 ≤ 6500 :=
  curveResultExpr_bound _ _ _ _ _ _ _

private theorem command_bound (prepared : Prepared) (input : AffineInput)
    (original linked : InputMac) :
    (scheduleCommandsWithCost (prepared.scheduleWithCost input original linked).1).1.length ≤ 905256 := by
  rw [scheduleCommandsWithCost_value]
  apply (scheduleCommands_length _).trans
  rw [Prepared.scheduleWithCost_value, pipelineGateSchedule_length_value]

/-- The cached encoder constructs its labels and selected schedules once. -/
def valid [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) :
    Program spec (Garbling.Labels × Nat) 905765 :=
  let labels := labelsWithCost coin.2.1 input
  let prepared := prepareWithCost (privateView coin) tables input point free scales
  let hash := hashWithCost prepared.1.curve input
  .bind (LinkCost.linkWithCost hash.1 input labels.1.inputMac) fun linked =>
    let schedule := prepared.1.scheduleWithCost input labels.1.inputMac linked.1
    let compiled := scheduleCommandsWithCost schedule.1
    .map (fun _ => (labels.1, labels.2 + prepared.2 + hash.2 + linked.2 + schedule.2 + compiled.2))
      (.weaken (second := 905256) (commands compiled.1) (command_bound prepared.1 input labels.1.inputMac linked.1))

/-- The cached encoder has exactly the original eager label and oracle result. -/
theorem valid_run [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) (oracle : SimulatorState) :
    ((valid coin tables input point free scales).run handler oracle).1.1 =
        (privateView coin).labels input ∧
      ((valid coin tables input point free scales).run handler oracle).2 =
        ((privateState coin oracle).programForOutput input point free scales.get).oracle := by
  simp only [valid, Program.run_bind, LinkCost.linkWithCost_run _ _ _ _
    (hashWithCost_value _ _), Program.run_map, Program.run_weaken, commands_run,
    scheduleCommandsWithCost_value, scheduleCommands_correct, Prepared.scheduleWithCost_value, prepareWithCost_curve,
    prepareWithCost_points, (labelsWithCost_spec coin input).1,
    CircuitSimulatorState.programForOutput, CircuitSimulatorState.selectedSchedule,
    linkedPipelineGateSchedule]
  exact ⟨trivial, rfl⟩

/-- The cached arithmetic cost is independent of the oracle answers. -/
theorem valid_local_bound [FieldCertificate] [GroupCertificate] {State : Type}
    (oracleHandler : OracleHandler spec State)
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) (state : State) :
    ((valid coin tables input point free scales).run oracleHandler state).1.2 ≤ 50000000 := by
  have prepared := prepareWithCost_bound (privateView coin) tables input point free scales
  have hashed := hashWithCost_bound (prepareWithCost (privateView coin) tables input point free scales).1.curve input
  have compiled (linked : InputMac) := scheduleCommandsWithCost_bound
    ((prepareWithCost (privateView coin) tables input point free scales).1.scheduleWithCost
      input (labelsWithCost coin.2.1 input).1.inputMac linked).1
  simp only [Prepared.scheduleWithCost_value, pipelineGateSchedule_length_value] at compiled
  simp only [valid, Program.run_bind, Program.run_map]
  rw [LinkCost.linkWithCost_cost, Prepared.scheduleWithCost_count, (labelsWithCost_spec coin input).2]
  have current := compiled ((LinkCost.linkWithCost
    (hashWithCost (prepareWithCost (privateView coin) tables input point free scales).1.curve input).1
    input (labelsWithCost coin.2.1 input).1.inputMac).run oracleHandler state).1.1
  simp only [Prepared.scheduleWithCost_value]
  omega


private theorem curve_command_bound (curve : PreparedCurve) (input : AffineInput) (mac : InputMac) :
    (scheduleCommandsWithCost (curveScheduleWithCost curve.request input mac curve.tables).1).1.length ≤ 3810 := by
  rw [scheduleCommandsWithCost_value]
  apply (scheduleCommands_length _).trans
  rw [curveScheduleWithCost_value, CurveGateRequest.schedule_length]
  decide

/-- The invalid encoder caches only the curve path. -/
def invalid (coin : OfflineCoin) (tables : SimulatorTables (privateView coin)) (input : AffineInput) :
    Program spec (Garbling.Labels × Nat) 3810 :=
  let labels := labelsWithCost coin.2.1 input
  let curve := prepareCurveWithCost (privateView coin).curve input (privateView coin).bridgeKey tables.curve
  let schedule := curveScheduleWithCost curve.1.request input labels.1.inputMac curve.1.tables
  let compiled := scheduleCommandsWithCost schedule.1
  .map (fun _ => (labels.1, labels.2 + curve.2 + schedule.2 + compiled.2))
    (.weaken (commands compiled.1) (curve_command_bound curve.1 input labels.1.inputMac))

/-- The cached invalid encoder has exactly the original eager result. -/
theorem invalid_run (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (oracle : SimulatorState) :
    ((invalid coin tables input).run handler oracle).1.1 = (privateView coin).labels input ∧
      ((invalid coin tables input).run handler oracle).2 =
        ((invalidProgram (privateView coin) input).run handler oracle).2 := by
  simp only [invalid, Program.run_map, Program.run_weaken, commands_run,
    scheduleCommandsWithCost_value, scheduleCommands_correct, curveScheduleWithCost_value,
    prepareCurveWithCost_value, (labelsWithCost_spec coin input).1,
    invalidProgram, CircuitSimulatorState.selectedCurve]
  exact ⟨trivial, trivial⟩

/-- The invalid encoder has the same fixed local bound under every handler. -/
theorem invalid_local_bound {State : Type} (oracleHandler : OracleHandler spec State)
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (state : State) :
    ((invalid coin tables input).run oracleHandler state).1.2 ≤ 50000000 := by
  have curve := prepareCurveWithCost_bound (privateView coin).curve input (privateView coin).bridgeKey tables.curve
  have compiled := scheduleCommandsWithCost_bound
    (curveScheduleWithCost
      (prepareCurveWithCost (privateView coin).curve input (privateView coin).bridgeKey tables.curve).1.request
      input (labelsWithCost coin.2.1 input).1.inputMac
      (prepareCurveWithCost (privateView coin).curve input (privateView coin).bridgeKey tables.curve).1.tables).1
  simp only [curveScheduleWithCost_value, CurveGateRequest.schedule_length, coordinateBitCount] at compiled
  simp only [invalid, Program.run_map, curveScheduleWithCost_count, (labelsWithCost_spec coin input).2,
    curveScheduleWithCost_value]
  omega

/-- The selected encoder keeps its actual deterministic operation counter. -/
def selected [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point)
    (sample : (Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)) :
    Program spec (Garbling.Labels × Nat) (onlineBudget output) :=
  match output with
  | none => invalid coin tables input
  | some point => .map (fun answer => (answer.1, answer.2 + 362))
      (valid coin tables input point (Vector.ofFn sample.1) (Vector.ofFn sample.2))

/-- The selected encoder has a fixed local bound under every handler. -/
theorem selected_local_bound [FieldCertificate] [GroupCertificate] {State : Type}
    (oracleHandler : OracleHandler spec State)
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point)
    (sample : (Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)) (state : State) :
    ((selected coin tables input output sample).run oracleHandler state).1.2 ≤ 51000000 := by
  cases output with
  | none => exact (invalid_local_bound oracleHandler coin tables input state).trans (by decide)
  | some point =>
      have bound := valid_local_bound oracleHandler coin tables input point (Vector.ofFn sample.1) (Vector.ofFn sample.2) state
      simp only [selected, Program.run_map]
      omega


/-- This projection keeps the cached encoder's exact semantic result. -/
theorem selected_run [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point)
    (sample : (Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase))
    (oracle : SimulatorState) :
    ((selected coin tables input output sample).map Prod.fst).run handler oracle =
      match output with
      | none => (invalidProgram (privateView coin) input).run handler oracle
      | some point => (validProgram (privateView coin) input point (Vector.ofFn sample.1) sample.2).run handler oracle := by
  cases output with
  | none =>
      have result := invalid_run coin tables input oracle
      apply Prod.ext
      · exact result.1
      · exact result.2
  | some point =>
      have result := valid_run coin tables input point (Vector.ofFn sample.1) (Vector.ofFn sample.2) oracle
      have same : (Vector.ofFn sample.2).get = sample.2 := funext (Vector.get_ofFn sample.2)
      simp only [selected, Program.run_map]
      conv_rhs => rw [← same]
      rw [validProgram_private_run]
      generalize (valid coin tables input point (Vector.ofFn sample.1)
        (Vector.ofFn sample.2)).run handler oracle = answer at result ⊢
      generalize ((privateState coin oracle).programForOutput input point (Vector.ofFn sample.1)
        (Vector.ofFn sample.2).get).oracle = nextState at result ⊢
      generalize (privateView coin).labels input = labels at result ⊢
      exact @Prod.ext Garbling.Labels SimulatorState _ _ result.1 result.2

/-- The cached encoder samples its online coin before it executes the selected path. -/
noncomputable def encoding [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point) :
    OracleProgram spec Garbling.Labels (onlineBudget output) :=
  .sample online.law (fun sample => ((selected coin tables input output sample).map Prod.fst).toOracle)

/-- The cached online encoder has the exact original eager distribution. -/
theorem encoding_run [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point) (oracle : SimulatorState) :
    (encoding coin tables input output).run handler oracle =
      (encodeProgram coin input output).run handler oracle := by
  cases output with
  | none =>
      simp only [encoding, OracleProgram.run, Program.toOracle_run, selected_run, encodeProgram]
      simp
  | some point =>
      simp only [encoding, OracleProgram.run, Program.toOracle_run, selected_run,
        encodeProgram, ThreePhase.run_append, PMF.bind_map, Function.comp_def]

/-- The finite online sampler keeps its prefix counter before the decision projection. -/
def onlineCutoff [FieldCertificate] (attempts : Nat) : BitCode (Option SimulatorSamplingCost.OnlineCoin) :=
  SimulatorSamplingCost.eraseCost (SimulatorSamplingCost.onlineFinite.run attempts)

theorem onlineCutoff_law [FieldCertificate] (attempts : Nat) :
    CutoffLaw attempts 181 online.law (onlineCutoff attempts).law := by
  rw [onlineCutoff, SimulatorSamplingCost.eraseCost_law]
  exact SimulatorSamplingCost.onlineFinite.law attempts

theorem onlineCutoff_bits [FieldCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat) (seed : Seed) :
    ((onlineCutoff attempts).run random seed).2 ≤ 181 * (257 * attempts) := by
  rw [onlineCutoff, SimulatorSamplingCost.eraseCost_bits]
  exact SimulatorSamplingCost.onlineFinite.bits attempts Seed random seed

/-- The actual cached encoder uses finite rejection for every private and sparse draw. -/
def encode [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point) (state : SparseState) :
    BitCode (Option (Garbling.Labels × SparseState)) :=
  (onlineCutoff attempts).bind (optional fun sample =>
    ((selected coin tables input output sample).map Prod.fst).cutoff sparseDraw attempts state)

/-- The cached encoder retains its own exact joint output law. -/
theorem encode_law [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point) (state : SparseState) :
    CutoffLaw attempts 905946 (runSampled sparseHandler (encoding coin tables input output) state)
      (encode attempts coin tables input output state).law := by
  have bounded : onlineBudget output ≤ 905765 := by cases output <;> simp [onlineBudget]
  have law := (onlineCutoff_law attempts).bind (fun sample =>
    (CutoffLaw.program sparseDraw attempts ((selected coin tables input output sample).map Prod.fst) state).weaken bounded)
  change CutoffLaw attempts 905946
    (online.law.bind (fun sample => runSampled
      (fun query state => (sparseDraw query state).distribution)
      ((selected coin tables input output sample).map Prod.fst).toOracle state)) _
  simp only [Program.sampledLaw_toOracle]
  unfold encode
  rw [BitCode.bind_law]
  have same (value : Option ((Fin 90 → Point) ×
      (Fin FieldMacToECMac.outputMacCount → NonZeroBase))) :
      (optional (fun sample => ((selected coin tables input output sample).map Prod.fst).cutoff
        sparseDraw attempts state) value).law =
      optionalPMF (fun sample => (((selected coin tables input output sample).map Prod.fst).cutoff
        sparseDraw attempts state).law) value := by cases value <;> rfl
  simp only [same]
  exact law



/-- This budget padding adds no oracle request or random draw. -/
def fixedProgram [FieldCertificate] [GroupCertificate]
    (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (sample : SimulatorSamplingCost.OnlineCoin) : Program combinedSpec Garbling.Labels 905765 :=
  (((selected cache.coin cache.tables input output sample).map Prod.fst).internal).weaken
    (by cases output <;> simp [onlineBudget])

private theorem fixedProgram_cutoff [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (sample : SimulatorSamplingCost.OnlineCoin) (state : SparseState) :
    (fixedProgram cache input output sample).cutoff combinedDraw attempts state =
      ((selected cache.coin cache.tables input output sample).map Prod.fst).cutoff sparseDraw attempts state := by
  exact Program.internal_cutoff ((selected cache.coin cache.tables input output sample).map Prod.fst) attempts state

/-- This runtime retains local work, sparse work, and fair-bit counts after failure. -/
def encodeWithCost [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat)
    (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (state : SparseState) (seed : Seed) (depth : Nat) :
    (Option (Garbling.Labels × SparseState) × Seed) × Nat × Nat × Nat :=
  let sampled := (SimulatorSamplingCost.onlineFinite.run attempts).run random seed
  match sampled.1.1.1 with
  | none => ((none, sampled.1.2), 0, sampled.1.1.2, sampled.2)
  | some sample =>
      let result := Cost.executeCutoffCost random attempts
        (fixedProgram cache input output sample) state sampled.1.2 depth
      (result.1, result.2.1, sampled.1.1.2 + 51000000 + result.2.2.1, sampled.2 + result.2.2.2)

/-- The counted runtime has the actual finite encoder's result, seed, and bit count. -/
theorem encodeWithCost_value [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat)
    (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (state : SparseState) (seed : Seed) (depth : Nat) :
    ((encodeWithCost random attempts cache input output state seed depth).1,
      (encodeWithCost random attempts cache input output state seed depth).2.2.2) =
      (encode attempts cache.coin cache.tables input output state).run random seed := by
  simp only [encodeWithCost, encode, onlineCutoff, BitCode.bind_run, SimulatorSamplingCost.eraseCost_run]
  split
  · rename_i value same
    simp only [optional, same, BitCode.run, Nat.add_zero]
  · rename_i sample same
    simp only [optional, same]
    have exact := Cost.executeCutoffCost_correct random attempts
      (fixedProgram cache input output sample) state
      ((SimulatorSamplingCost.onlineFinite.run attempts).run random seed).1.2 depth
    rw [fixedProgram_cutoff] at exact
    have first := congrArg Prod.fst exact
    have bits := congrArg Prod.snd exact
    rw [first, bits]

/-- The finite runtime charges every sparse prefix and a proved full local reserve. -/
theorem encodeWithCost_work [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat)
    (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (state : SparseState) (seed : Seed) (depth capacity : Nat)
    (bound : Cost.StateBound state capacity) (depthBound : depth ≤ capacity) :
    (encodeWithCost random attempts cache input output state seed depth).2.2.1 ≤
      51184061 + 905765 * (10 * (capacity + 905765) + 16) := by
  have sampled := SimulatorSamplingCost.onlineFinite.cost attempts Seed random seed
  simp only [encodeWithCost]
  split
  · simp only
    omega
  · rename_i sample same
    simp only
    have sparse := (Cost.executeCutoffCost_budget random attempts
      (fixedProgram cache input output sample) state
      ((SimulatorSamplingCost.onlineFinite.run attempts).run random seed).1.2 depth capacity bound depthBound)
    have upper := sparse
    omega

/-- The actual cached encoder has a strict fair-bit limit on every success or failure path. -/
theorem encode_bits [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point) (state : SparseState) (seed : Seed) :
    ((encode attempts coin tables input output state).run random seed).2 ≤ 905946 * (257 * attempts) := by
  have budget : onlineBudget output ≤ 905765 := by cases output <;> simp [onlineBudget]
  have result := optional_bit_bound random (onlineCutoff attempts)
    (fun sample => ((selected coin tables input output sample).map Prod.fst).cutoff sparseDraw attempts state)
    (181 * (257 * attempts)) (905765 * (257 * attempts))
    (fun seed => onlineCutoff_bits random attempts seed)
    (fun sample seed =>
      (((selected coin tables input output sample).map Prod.fst).sparse_cutoff_bits random attempts state seed).trans
        (Nat.mul_le_mul_right _ budget)) seed
  convert result using 1
  ring

/-- The counted runtime has the actual encoder's strict bit bound. -/
theorem encodeWithCost_bits [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat)
    (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (state : SparseState) (seed : Seed) (depth : Nat) :
    (encodeWithCost random attempts cache input output state seed depth).2.2.2 ≤
      905946 * (257 * attempts) := by
  have same := congrArg Prod.snd (encodeWithCost_value random attempts cache input output state seed depth)
  rw [same]
  exact encode_bits random attempts cache.coin cache.tables input output state seed

private theorem positive_optional_bind {A B : Type} (source : BitCode (Option A))
    (next : A → BitCode (Option B)) (first : SimulatorRejectionCost.PositiveWidths source)
    (second : ∀ value, SimulatorRejectionCost.PositiveWidths (next value)) :
    SimulatorRejectionCost.PositiveWidths (source.bind (optional next)) :=
  SimulatorRejectionCost.positive_bind source (optional next) first
    (SimulatorRejectionCost.optional_positive next second)

private theorem onlineCutoff_positive [FieldCertificate] (attempts : Nat) :
    SimulatorRejectionCost.PositiveWidths (onlineCutoff attempts) :=
  SimulatorSamplingCost.eraseCost_positive (SimulatorSamplingCost.onlineFinite.run attempts)
    (SimulatorSamplingCost.onlineFinite.positive attempts)

/-- Every executed encoder random block has positive width. -/
theorem encode_positive [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point) (state : SparseState) :
    SimulatorRejectionCost.PositiveWidths (encode attempts coin tables input output state) :=
  positive_optional_bind (onlineCutoff attempts)
    (fun sample => ((selected coin tables input output sample).map Prod.fst).cutoff sparseDraw attempts state)
    (onlineCutoff_positive attempts)
    (fun sample => SimulatorRejectionCost.program_positive sparseDraw attempts
      ((selected coin tables input output sample).map Prod.fst) state)

/-- The actual finite encoder's rejection control fits four operations per counted bit. -/
theorem encode_control [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat)
    (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (state : SparseState) (seed : Seed) :
    (SimulatorRejectionCost.runWithCost random
      (encode attempts cache.coin cache.tables input output state) seed).2.2 ≤
      4 * (905946 * (257 * attempts)) :=
  (SimulatorRejectionCost.runWithCost_bound random _
    (encode_positive attempts cache.coin cache.tables input output state) seed).trans
    (Nat.mul_le_mul_left 4 (encode_bits random attempts cache.coin cache.tables input output state seed))

/-- The final encoder adds the proved rejection-control allowance without rerunning the program. -/
def execute [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (state : SparseState) (seed : Seed) (depth : Nat) :
    (Option (Garbling.Labels × SparseState) × Seed) × Nat × Nat × Nat :=
  let result := encodeWithCost random 256 cache input output state seed depth
  (result.1, result.2.1, result.2.2.1 + 4 * result.2.2.2, result.2.2.2)

/-- The final encoder runs exactly the finite program used in the privacy game. -/
theorem execute_value [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (state : SparseState) (seed : Seed) (depth : Nat) :
    ((execute random cache input output state seed depth).1,
      (execute random cache input output state seed depth).2.2.2) =
      (encode 256 cache.coin cache.tables input output state).run random seed := by
  simpa only [execute] using encodeWithCost_value random 256 cache input output state seed depth

/-- The final encoder has a strict work and fair-bit bound on success and failure paths. -/
theorem execute_bound [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (state : SparseState) (seed : Seed) (depth capacity : Nat)
    (bound : Cost.StateBound state capacity) (depthBound : depth ≤ capacity) :
    (execute random cache input output state seed depth).2.2.1 ≤
        51184061 + 905765 * (10 * (capacity + 905765) + 16) + 4 * (905946 * (257 * 256)) ∧
      (execute random cache input output state seed depth).2.2.2 ≤ 905946 * (257 * 256) := by
  have work := encodeWithCost_work random 256 cache input output state seed depth capacity bound depthBound
  have bits := encodeWithCost_bits random 256 cache input output state seed depth
  simpa only [execute] using And.intro (Nat.add_le_add work (Nat.mul_le_mul_left 4 bits)) bits

/-- The actual offline setup has a strict fair-bit limit on every path. -/
theorem offline_bits {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat) (seed : Seed) :
    ((setupFinite.run attempts).run random seed).2 ≤ 907550 * (257 * attempts) :=
  setupFinite.bits attempts Seed random seed

/-- The actual offline setup retains its local-work bound after a failed draw. -/
theorem offline_work {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat) (seed : Seed) :
    ((setupFinite.run attempts).run random seed).1.1.2 ≤ 4635060 :=
  setupFinite.cost attempts Seed random seed

/-- Each external query has the same finite fair-bit limit. -/
theorem external_bits {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (query : Garbling.OracleQuery) (state : SparseState) (seed : Seed) :
    ((cutoffDraw attempts (externalDraw query state)).run random seed).2 ≤ 257 * attempts :=
  cutoffDraw_bit_bound random attempts _ (combinedDraw_sizeLe (.inr query) state) seed

noncomputable section

/-- Every adaptive external phase preserves the finite sparse state bound. -/
theorem external_reached {A : Type} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec A budget)
    (state : SparseState) (capacity : Nat) (bound : Cost.StateBound state capacity)
    (answer : A × SparseState) (reached : answer ∈ (runSampled externalHandler program state).support) :
    Nonempty (Cost.StateBound answer.2 (capacity + budget)) := by
  induction program generalizing state capacity with
  | pure distribution =>
      obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      rw [← same]
      exact ⟨bound.mono (Nat.le_add_right _ _)⟩
  | sample distribution next ih =>
      obtain ⟨value, _, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      exact ih value state capacity bound supported
  | @query budget request next ih =>
      obtain ⟨value, supported, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      obtain ⟨nextBound⟩ := Cost.external_resources request state capacity bound value supported
      have last := ih value.1 value.2 (capacity + 1) nextBound tail
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using last

/-- Every successful finite external phase reaches a certified sparse state. -/
theorem external_cutoff_reached {A : Type} {budget : Nat}
    (attempts : Nat) (program : OracleProgram Garbling.oracleSpec A budget)
    (state : SparseState) (capacity : Nat) (bound : Cost.StateBound state capacity)
    (answer : A × SparseState)
    (reached : some answer ∈ (runCutoff externalDraw attempts program state).support) :
    Nonempty (Cost.StateBound answer.2 (capacity + budget)) := by
  apply external_reached program state capacity bound answer
  apply (PMF.mem_support_iff _ _).mpr
  have nonzero := (PMF.mem_support_iff _ _).mp reached
  have upper := (runCutoff_law externalDraw attempts program state).2 answer
  exact ne_of_gt ((pos_iff_ne_zero.mpr nonzero).trans_le upper)

/-- The actual three external phases and cached private stage have one global sparse-work bound. -/
theorem sparse_prefixes [FieldCertificate] [GroupCertificate] {Aux Seed : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (cache : PrivateCache) (table : Pipeline.Table)
    (sample : SimulatorSamplingCost.OnlineCoin)
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (seed : Seed)
    (before : Option (adversary.Before × SparseState) × Nat)
    (beforeReached : before ∈ (ExternalCost.runWithCost 256
      (adversary.prepare parameter auxiliary) (initial initialMetadata) 0).support) :
    let n := adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
      adversary.decisionQueryBudget parameter + 905765
    let limit := n * (10 * n + 16)
    before.2 ≤ limit ∧
      ∀ prior, before.1 = some prior →
      ∀ chosen : Option ((AffineInput × adversary.After) × SparseState) × Nat,
        chosen ∈ (ExternalCost.runWithCost 256
          (adversary.chooseInput parameter table auxiliary prior.1) prior.2
          (adversary.preQueryBudget parameter)).support →
        before.2 + chosen.2 ≤ limit ∧
          ∀ selectedInput, chosen.1 = some selectedInput →
          let encoded := Cost.executeCutoffCost random 256
            (fixedProgram cache selectedInput.1.1
              ((Garbling.garbledCircuit construction).function scalar selectedInput.1.1) sample)
            selectedInput.2 seed (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter)
          before.2 + chosen.2 + encoded.2.2.1 ≤ limit ∧
            ∀ value, encoded.1.1 = some value →
            ∀ decided : Option (Bool × SparseState) × Nat,
              decided ∈ (ExternalCost.runWithCost 256
                (adversary.decide parameter table value.1 auxiliary selectedInput.1.2) value.2
                (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter + 905765)).support →
              before.2 + chosen.2 + encoded.2.2.1 + decided.2 ≤ limit := by
  have result := PhaseCost.all_phase_bound 256 random seed
    (adversary.prepare parameter auxiliary)
    (fun prior => adversary.chooseInput parameter table auxiliary prior)
    (fun selectedInput => fixedProgram cache selectedInput.1
      ((Garbling.garbledCircuit construction).function scalar selectedInput.1) sample)
    (fun selectedInput labels => adversary.decide parameter table labels auxiliary selectedInput.2)
    before beforeReached
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

/-- This exact game executes the cached encoder between the three adversary phases. -/
def continuation [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (cache : PrivateCache) (table : Pipeline.Table) (state : SparseState) : PMF Bool :=
  (runSampled externalHandler (adversary.prepare parameter auxiliary) state).bind (fun prepared =>
    (runSampled externalHandler
      (adversary.chooseInput parameter table auxiliary prepared.1) prepared.2).bind (fun selected =>
      (runSampled sparseHandler (encoding cache.coin cache.tables selected.1.1
        ((Garbling.garbledCircuit construction).function scalar selected.1.1)) selected.2).bind
        (fun encoded => (runSampled externalHandler
          (adversary.decide parameter table encoded.1 auxiliary selected.1.2) encoded.2).map Prod.fst)))

/-- The cached program has its own full sparse completion law. -/
theorem continuation_exact [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (cache : PrivateCache) (state : SparseState) :
    (completion state).bind (eagerContinuation adversary parameter scalar auxiliary cache.coin) =
      continuation adversary parameter scalar auxiliary cache (privateView cache.coin).table state := by
  unfold eagerContinuation continuation
  rw [joint_bind idealOracleHandler externalHandler completion _ _ (external_adaptive_joint _ _)]
  apply congrArg (PMF.bind (runSampled externalHandler (adversary.prepare parameter auxiliary) state))
  funext prepared
  simp only
  rw [joint_bind idealOracleHandler externalHandler completion _ _ (external_adaptive_joint _ _)]
  apply congrArg (PMF.bind (runSampled externalHandler
    (adversary.chooseInput parameter (privateView cache.coin).table auxiliary prepared.1) prepared.2))
  funext selected
  simp only
  have same : (encodeProgram cache.coin selected.1.1
      ((Garbling.garbledCircuit construction).function scalar selected.1.1)).run handler =
      (encoding cache.coin cache.tables selected.1.1
        ((Garbling.garbledCircuit construction).function scalar selected.1.1)).run handler := by
    funext oracle
    exact (encoding_run cache.coin cache.tables _ _ oracle).symm
  rw [same]
  rw [joint_bind handler sparseHandler completion _ _ (sparse_adaptive_joint _ _)]
  apply congrArg (PMF.bind (runSampled sparseHandler
    (encoding cache.coin cache.tables selected.1.1
      ((Garbling.garbledCircuit construction).function scalar selected.1.1)) selected.2))
  funext encoded
  simp only
  have last := congrArg (fun distribution : PMF (Bool × SimulatorState) => distribution.map Prod.fst)
    (external_adaptive_joint
      (adversary.decide parameter (privateView cache.coin).table encoded.1 auxiliary selected.1.2) encoded.2)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at last
  have finish (output : Bool × SparseState) :
      (completion output.2).map (fun _ => output.1) = PMF.pure output.1 := PMF.map_const _ _
  simp_rw [finish] at last
  simpa only [PMF.map] using last

/-- The array sampler supplies the actual cached simulator state. -/
def exactGame [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  offlineReady.law.bind (fun prepared =>
    continuation adversary parameter scalar auxiliary prepared.1 prepared.2 (initial initialMetadata))

/-- The actual cached implementation has exactly the original ideal decision distribution. -/
theorem exactGame_eq [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) :
    exactGame adversary parameter scalar auxiliary = operationalIdealGame adversary parameter scalar auxiliary := by
  unfold exactGame operationalIdealGame
  rw [offlineReady, Code.map_law, ← offlineArrays_law, PMF.bind_map, PMF.bind_map]
  apply congrArg (PMF.bind offlineArrays.law)
  funext arrays
  dsimp only [Function.comp_def, ready]
  rw [tableWithCost_value]
  have exact := continuation_exact adversary parameter scalar auxiliary (cacheWithCost arrays).1 (initial initialMetadata)
  rw [cacheWithCost_coin] at exact
  rw [← exact, ← continuation_law]

/-- The external phase executes its failure-preserving cost interpreter. -/
def externalPhase {A : Type} {budget : Nat} (attempts : Nat)
    (program : OracleProgram Garbling.oracleSpec A budget) (state : SparseState) (depth : Nat) :
    PMF (Option (A × SparseState)) := (ExternalCost.runWithCost attempts program state depth).map Prod.fst

theorem externalPhase_law {A : Type} {budget : Nat} (attempts : Nat)
    (program : OracleProgram Garbling.oracleSpec A budget) (state : SparseState) (depth : Nat) :
    externalPhase attempts program state depth = runCutoff externalDraw attempts program state :=
  ExternalCost.runWithCost_law attempts program state depth

/-- This continuation uses the cached encoder's actual finite retry program. -/
def finiteContinuation [FieldCertificate] [GroupCertificate] {Aux : Type}
    (attempts : Nat) (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) (cache : PrivateCache) (table : Pipeline.Table) (state : SparseState) :
    PMF (Option Bool) :=
  (externalPhase attempts (adversary.prepare parameter auxiliary) state 0).bind
    (optionalPMF fun prepared =>
      (externalPhase attempts
        (adversary.chooseInput parameter table auxiliary prepared.1) prepared.2 (adversary.preQueryBudget parameter)).bind
        (optionalPMF fun selected =>
          (encode attempts cache.coin cache.tables selected.1.1
            ((Garbling.garbledCircuit construction).function scalar selected.1.1) selected.2).law.bind
            (optionalPMF fun encoded =>
              (externalPhase attempts
                (adversary.decide parameter table encoded.1 auxiliary selected.1.2)
                encoded.2 (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter + 905765)).map (Option.map Prod.fst))))

theorem finiteContinuation_law [FieldCertificate] [GroupCertificate] {Aux : Type}
    (attempts : Nat) (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) (cache : PrivateCache) (table : Pipeline.Table) (state : SparseState) :
    CutoffLaw attempts
      (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter + 905946)
      (continuation adversary parameter scalar auxiliary cache table state)
      (finiteContinuation attempts adversary parameter scalar auxiliary cache table state) := by
  have law := (runCutoff_law externalDraw attempts (adversary.prepare parameter auxiliary) state).bind
    (fun prepared => (runCutoff_law externalDraw attempts
      (adversary.chooseInput parameter table auxiliary prepared.1) prepared.2).bind
      (fun selected => (encode_law attempts cache.coin cache.tables selected.1.1
        ((Garbling.garbledCircuit construction).function scalar selected.1.1) selected.2).bind
        (fun encoded => (runCutoff_law externalDraw attempts
          (adversary.decide parameter table encoded.1 auxiliary selected.1.2)
          encoded.2).map Prod.fst)))
  simpa only [continuation, finiteContinuation, externalPhase_law, externalHandler,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using law

/-- This optional game uses the executable array sampler and cached finite encoder. -/
def finiteOption [FieldCertificate] [GroupCertificate] {Aux : Type}
    (attempts : Nat) (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) : PMF (Option Bool) :=
  (SimulatorSamplingCost.eraseCost (setupFinite.run attempts)).law.bind (optionalPMF fun prepared =>
    finiteContinuation attempts adversary parameter scalar auxiliary prepared.1 prepared.2 (initial initialMetadata))

theorem finiteOption_law [FieldCertificate] [GroupCertificate] {Aux : Type}
    (attempts : Nat) (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) :
    CutoffLaw attempts
      (1813496 + adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter)
      (operationalIdealGame adversary parameter scalar auxiliary)
      (finiteOption attempts adversary parameter scalar auxiliary) := by
  rw [← exactGame_eq]
  have law := (setupFinite.law attempts).bind (fun prepared =>
    finiteContinuation_law attempts adversary parameter scalar auxiliary prepared.1 prepared.2 (initial initialMetadata))
  unfold finiteOption
  rw [SimulatorSamplingCost.eraseCost_law]
  convert law using 1
  omega

/-- The concrete implementation returns false after a failed finite sampler. -/
def game [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  (finiteOption 256 adversary parameter scalar auxiliary).map (fun value => value.getD false)

/-- The concrete cached implementation has the same finite retry residual. -/
theorem game_error [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) :
    advantage (operationalIdealGame adversary parameter scalar auxiliary)
      (game adversary parameter scalar auxiliary) ≤
      cutoffResidual (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter) := by
  have law := finiteOption_law 256 adversary parameter scalar auxiliary
  have trueLaw : game adversary parameter scalar auxiliary true =
      finiteOption 256 adversary parameter scalar auxiliary (some true) := by
    rw [game, PMF.map_apply, tsum_fintype]
    simp [Fintype.sum_option]
  have upper := ENNReal.toReal_mono
    ((operationalIdealGame adversary parameter scalar auxiliary).apply_ne_top true) (law.2 true)
  unfold advantage
  rw [trueLaw, abs_of_nonneg (sub_nonneg.mpr upper)]
  convert law.point_error true using 1
  simp only [cutoffResidual, Nat.cast_add, inv_pow, div_eq_mul_inv]
  ring

/-- The actual cached finite retry implementation preserves the 100-bit privacy bound. -/
theorem privacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type} (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) (witness : Garbling.Randomness) :
    WorkPerAdvantage 100
      (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter + 1)
      (advantage (ThreePhase.realGame adversary parameter scalar auxiliary witness)
        (game adversary parameter scalar auxiliary)) := by
  let queries := adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
    adversary.decisionQueryBudget parameter
  by_cases small : queries < 2 ^ 100
  · have first := operational_small_error adversary parameter scalar auxiliary witness small
    have second := game_error adversary parameter scalar auxiliary
    have triangle := abs_sub_le
      ((ThreePhase.realGame adversary parameter scalar auxiliary witness) true).toReal
      ((operationalIdealGame adversary parameter scalar auxiliary) true).toReal
      ((game adversary parameter scalar auxiliary) true).toReal
    have bound : advantage (ThreePhase.realGame adversary parameter scalar auxiliary witness)
        (game adversary parameter scalar auxiliary) ≤
        adaptiveErrorEnvelope queries + cutoffResidual queries :=
      triangle.trans (add_le_add first second)
    exact (mul_le_mul_of_nonneg_right bound (by positivity)).trans (cutoffEnvelope_has100Bits queries)
  · exact largeBudget_has100Bits _ _ queries (Nat.le_of_not_gt small)

end
end Implementation
end SimulatorMachine
end Kriterion.ArgoMAC.Security
