import Proof.ValidPrefixRestSum
import Proof.ValidEventSourceSum
import Proof.InvalidEndpointRatio
import Proof.GhostSourceGood
import Proof.ValidPrefixWeightExpansion

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1

/-- The full query budget gives a lower coefficient than the valid transcript length. -/
theorem validSourceRatio_coefficient_le (length budget : Nat) (denominator : ℝ≥0∞)
    (bounded : length ≤ budget) :
    1 - ((186 * budget + 508 : Nat) : ℝ≥0∞) / denominator ≤
      1 - ((182 * length : Nat) : ℝ≥0∞) / denominator := by
  apply tsub_le_tsub_left
  gcongr
  omega

private theorem validPhase_relative_bound (ghost prefixMass first second publicMass real factor larger phase : ℝ≥0∞)
    (ghostBound : ghost ≤ prefixMass) (prefixEq : prefixMass = phase * first)
    (sourceBound : larger * second ≤ publicMass) (realEq : real = phase * publicMass)
    (same : first = second) (coefficient : factor ≤ larger) : factor * ghost ≤ real := by
  subst second
  apply phase_relative_bound ghost first publicMass real factor phase
    (ghostBound.trans_eq prefixEq) _ realEq
  exact (mul_le_mul_left coefficient first).trans sourceBound

private theorem uniformWeighted_eq {A : Type*} (first second : Fintype A)
    (firstNonempty secondNonempty : Nonempty A) (left right : A → ℝ≥0∞)
    (same : ∀ a, left a = right a) :
    (∑' a, @PMF.uniformOfFintype A first firstNonempty a * left a) =
      ∑' a, @PMF.uniformOfFintype A second secondNonempty a * right a := by
  cases Subsingleton.elim first second
  exact tsum_congr fun a => congrArg (@PMF.uniformOfFintype A first firstNonempty a * ·) (same a)

private theorem uniformEvent_eq {A : Type*} (first second : Fintype A)
    (firstNonempty secondNonempty : Nonempty A) (left right : Set A) (same : left = right) :
    (@PMF.uniformOfFintype A first firstNonempty).toOuterMeasure left =
      (@PMF.uniformOfFintype A second secondNonempty).toOuterMeasure right := by
  cases Subsingleton.elim first second
  exact congrArg (@PMF.uniformOfFintype A first firstNonempty).toOuterMeasure same

set_option maxRecDepth 4096 in
private theorem validRestEventMass_eq [FieldCertificate] [GroupCertificate]
    (restFinite : Fintype GarblingSourceRest) (firstTag secondTag : Fintype FullCircuitSource)
    (firstSample secondSample : Fintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey))
    (restNonempty : Nonempty GarblingSourceRest)
    (scalar : ScalarField) (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer)) :
    (∑' rest, @PMF.uniformOfFintype GarblingSourceRest restFinite restNonempty rest *
      ∑' tag, @PMF.uniformOfFintype FullCircuitSource firstTag
        (@instNonemptyProd (RawCircuitGate → FullHashLift) CircuitMaskTables
          (@Pi.instNonempty RawCircuitGate (fun _ => FullHashLift) (fun _ => fullHashLiftNonempty))
          circuitMaskTablesNonempty) tag *
        if (fun _ : GarblingSourceRest => True) rest then
          (@PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
            firstSample (@instNonemptyProd (PermutationOracle Pipeline.FixedKeyIndex Block) InputMacKey
              (@instNonemptyPermutationOracle _ _) ⟨defaultSimulatorCoin.inputKey⟩)).toOuterMeasure
            ((fun rest tag => validTagGoodEvent rest (outputKeys construction scalar rest.reference.offsets)
              table input key (sourcePrefixReference reference rest) before after tag) rest tag) else 0) =
    ∑' rest, @PMF.uniformOfFintype GarblingSourceRest restFinite restNonempty rest *
      ∑' tag, @PMF.uniformOfFintype FullCircuitSource secondTag
        (@instNonemptyProd (RawCircuitGate → FullHashLift) CircuitMaskTables
          (@Pi.instNonempty RawCircuitGate (fun _ => FullHashLift) (fun _ => fullHashLiftNonempty))
          circuitMaskTablesNonempty) tag *
        (@PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
          secondSample (@instNonemptyProd (PermutationOracle Pipeline.FixedKeyIndex Block) InputMacKey
            (@instNonemptyPermutationOracle _ _) instNonemptyInputMacKey_proof_7)).toOuterMeasure
          (validTagGoodEvent rest (actualSourceOutputKeys scalar rest)
            table input key (sourcePrefixReference reference rest) before after tag) := by
  apply uniformWeighted_eq
  intro rest
  apply uniformWeighted_eq
  intro tag
  rw [if_pos trivial]
  apply uniformEvent_eq
  exact congrArg (fun keys => validTagGoodEvent rest keys table input key
    (sourcePrefixReference reference rest) before after tag)
    (show outputKeys construction scalar rest.reference.offsets = actualSourceOutputKeys scalar rest from rfl)

private theorem fullTagWeight_type {Tape : Type*} (tapes : PMF Tape)
    (tagFinite : Fintype FullCircuitSource) (weight : Tape → FullCircuitSource → ℝ≥0∞) :
    (∑' tape, tapes tape * ∑' tag : (RawCircuitGate → FullHashLift) × CircuitMaskTables,
      (@PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitMaskTables) tagFinite _) tag * weight tape tag) =
    ∑' tape, tapes tape * ∑' tag : FullCircuitSource,
      (@PMF.uniformOfFintype FullCircuitSource tagFinite _) tag * weight tape tag := rfl

set_option maxRecDepth 4096 in
/-- The actual valid source satisfies the full transcript ratio. -/
def validGhostEndpoint_mass_ge [FieldCertificate] [GroupCertificate]
    [blockFinite : Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : NonZeroScalar) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (table : Pipeline.Table) (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (key : InputMacKey)
    (valid : OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after)
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget) := by
  have ghost := fullGateGhostGood_le_prefixGood adversary parameter auxiliary scalar.value witness fallback
    (table, selected, before, labels, decision, after)
  have prefixEq := fullGatePrefixGood_weight_sum adversary parameter auxiliary scalar.value witness fallback
    (table, selected, before, labels, decision, after)
  have normalized := fullTagWeight_type (randomTape witness parameter)
    (@instFintypeProd (RawCircuitGate → FullHashLift) CircuitMaskTables
      (@Pi.instFintype RawCircuitGate (fun _ => FullHashLift)
        (fun a b => Classical.propDecidable (a = b)) instFintypeRawCircuitGate_1
        (fun _ => Fin.fintype _)) instFintypeCircuitMaskTables)
    (validPrefixPhaseWeight adversary parameter auxiliary scalar.value fallback
      (table, selected, before, labels, decision, after))
  have phases := validOriginalWeight_phase_sum adversary parameter auxiliary scalar.value witness fallback table
    referenceBefore referenceAfter selected labels decision before after key valid bits mac firstCompatible secondCompatible
  have source := validEventSourceSum_real_le witness parameter referenceBefore (actualSourceOutputKeys scalar.value)
    table selected.1 key before after firstCompatible valid budget small bounded
  have real := realAdaptiveTranscript_retained_factor adversary parameter auxiliary scalar witness table
    referenceBefore referenceAfter selected labels decision before after key bits mac firstCompatible secondCompatible
  have same := validRestEventMass_eq instFintypeGarblingSourceRest
      (@instFintypeProd (RawCircuitGate → FullHashLift) CircuitMaskTables
        (@Pi.instFintype RawCircuitGate (fun _ => FullHashLift)
          (fun a b => Classical.propDecidable (a = b)) instFintypeRawCircuitGate_1
          (fun _ => Fin.fintype _)) instFintypeCircuitMaskTables)
      (@instFintypeProd (RawCircuitGate → FullHashLift) CircuitMaskTables
        (@Pi.instFintype RawCircuitGate (fun _ => FullHashLift)
          instDecidableEqRawCircuitGate_1 instFintypeRawCircuitGate_1
          (fun _ => Fin.fintype _)) instFintypeCircuitMaskTables)
      (@instFintypeProd (PermutationOracle Pipeline.FixedKeyIndex Block) InputMacKey
        (@instFintypePermutationOracle _ _ Pipeline.instFintypeFixedKeyIndex blockFinite)
        instFintypeInputMacKey_proof_3)
      (@instFintypeProd (PermutationOracle Pipeline.FixedKeyIndex Block) InputMacKey
        (@instFintypePermutationOracle _ _ Pipeline.instFintypeFixedKeyIndex blockFinite)
        publicInputMacKeyFintype) ⟨(garblingOracleKeyEquiv witness).2⟩
      scalar.value table selected.1 key referenceBefore before after
  exact validPhase_relative_bound _ _ _ _ _ _ _ _ _ ghost (prefixEq.trans (normalized.trans phases)) source real same
    (validSourceRatio_coefficient_le _ _ _ bounded)

end
end Kriterion.ArgoMAC.Security
