import Proof.InvalidEndpointRatio
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
attribute [local instance] instNonemptyInputMacKey_proof_8

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

private theorem phase_alias_bound (ghost first second publicMass real factor phase : ℝ≥0∞)
    (ghostBound : ghost ≤ phase * first) (sourceBound : factor * second ≤ publicMass)
    (realEq : real = phase * publicMass) (same : first = second) : factor * ghost ≤ real := by
  subst second
  exact phase_relative_bound ghost first publicMass real factor phase ghostBound sourceBound realEq

set_option maxRecDepth 4096 in
private theorem invalidRestEventMass_eq [FieldCertificate] [GroupCertificate] [blockFinite : Fintype Block]
    (firstRest secondRest : Fintype GarblingSourceRest)
    (firstTag secondTag : Fintype FullCircuitSource)
    (firstSample secondSample : Fintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey))
    (restNonempty : Nonempty GarblingSourceRest)
    (scalar : ScalarField) (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer)) :
    (∑' rest, @PMF.uniformOfFintype GarblingSourceRest firstRest restNonempty rest *
      ∑' tag, @PMF.uniformOfFintype FullCircuitSource firstTag (@instNonemptyProd (RawCircuitGate → FullHashLift) CircuitMaskTables
        (@Pi.instNonempty RawCircuitGate (fun _ => FullHashLift) (fun _ => fullHashLiftNonempty))
        circuitMaskTablesNonempty) tag *
        if (fun rest : GarblingSourceRest => rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after)) rest then
          (@PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
            firstSample (@instNonemptyProd (PermutationOracle Pipeline.FixedKeyIndex Block) InputMacKey
              (@instNonemptyPermutationOracle _ _) ⟨defaultSimulatorCoin.inputKey⟩)).toOuterMeasure
            ((fun rest tag => invalidTagGoodEvent rest (outputKeys construction scalar rest.reference.offsets)
              table input key (sourcePrefixReference reference rest) before after tag) rest tag) else 0) =
    ∑' rest, @PMF.uniformOfFintype GarblingSourceRest secondRest restNonempty rest *
      @invalidRestEventMass _ _ secondTag secondSample _ _ _ scalar table input key reference before after rest := by
  apply uniformWeighted_eq
  intro rest
  unfold invalidRestEventMass
  apply uniformWeighted_eq
  intro tag
  apply congrArg (fun mass : ℝ≥0∞ =>
    if rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after) then mass else 0)
  exact uniformEvent_eq _ _ _ _ _ _ rfl

set_option maxRecDepth 4096 in
/-- The actual invalid source satisfies the full transcript ratio. -/
def invalidGhostEndpoint_mass_ge [FieldCertificate] [GroupCertificate] [blockFinite : Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : NonZeroScalar) (witness nonfixedWitness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (table : Pipeline.Table) (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (key : InputMacKey)
    (invalid : ¬ OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after)
    (nonfixed : NonFixedTranscriptCompatible nonfixedWitness (before ++ after))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget) := by
  have ghost := invalidGhostGood_rest_event_le adversary parameter auxiliary scalar.value witness fallback table
    referenceBefore referenceAfter selected labels decision before after key invalid bits mac firstCompatible secondCompatible
  have source := invalidRestEventMass_real_le witness nonfixedWitness parameter scalar.value table selected.1 key
    referenceBefore before after invalid firstCompatible nonfixed budget small bounded
  have real := realAdaptiveTranscript_retained_factor adversary parameter auxiliary scalar witness table
    referenceBefore referenceAfter selected labels decision before after key bits mac firstCompatible secondCompatible
  exact phase_alias_bound _ _ _ _ _ _ _ ghost source real
    (invalidRestEventMass_eq instFintypeGarblingSourceRest instFintypeGarblingSourceRest
      (@instFintypeProd (RawCircuitGate → FullHashLift) CircuitMaskTables
        (@Pi.instFintype RawCircuitGate (fun _ => FullHashLift)
          (fun a b => Classical.propDecidable (a = b)) instFintypeRawCircuitGate_1
          (fun _ => Fin.fintype _)) instFintypeCircuitMaskTables)
      (@instFintypeProd (RawCircuitGate → FullHashLift) CircuitMaskTables
        (@Pi.instFintype RawCircuitGate (fun _ => FullHashLift)
          instDecidableEqRawCircuitGate_1 instFintypeRawCircuitGate_1
          (fun _ => Fin.fintype _)) instFintypeCircuitMaskTables)
      (@instFintypeProd (PermutationOracle Pipeline.FixedKeyIndex Block) InputMacKey
        (@instFintypePermutationOracle _ _ Pipeline.instFintypeFixedKeyIndex instFintypeBlock)
        publicInputMacKeyFintype)
      (@instFintypeProd (PermutationOracle Pipeline.FixedKeyIndex Block) InputMacKey
        (@instFintypePermutationOracle _ _ Pipeline.instFintypeFixedKeyIndex blockFinite)
        publicInputMacKeyFintype) ⟨(garblingOracleKeyEquiv witness).2⟩
      scalar.value table selected.1 key referenceBefore before after)

end
end Kriterion.ArgoMAC.Security
