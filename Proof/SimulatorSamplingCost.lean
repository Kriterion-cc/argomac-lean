import Proof.SimulatorScheduleCost
import Proof.OperationalSimulator
import Proof.SimulatorFinitePrivacy
import Proof.SimulatorRejectionCost

namespace Kriterion.ArgoMAC.Security.SimulatorSamplingCost
open BN254 Cryptography SimulatorSampling SimulatorScheduleCost
set_option maxRecDepth 4096

/-- This predicate bounds the local charge on every random tape. -/
def Bounded {A : Type} {draws : Nat} (code : Code (A × Nat) draws) (bound : Nat) : Prop :=
  ∀ (Seed : Type) (random : (size : Nat) → 0 < size → Seed → Fin size × Seed) (seed : Seed),
    (code.run random seed).1.2 ≤ bound

/-- This constructor joins two sampled values and charges the value record. -/
def pair {A B : Type} {first second : Nat}
    (left : Code (A × Nat) first) (right : Code (B × Nat) second) :
    Code ((A × B) × Nat) (second + first) :=
  (left.pair right).map fun values => ((values.1.1, values.2.1), values.1.2 + values.2.2 + 2)

theorem pair_law {A B : Type} {first second : Nat}
    (left : Code (A × Nat) first) (right : Code (B × Nat) second) :
    (pair left right).law.map Prod.fst =
      (right.law.map Prod.fst).bind (fun b => (left.law.map Prod.fst).map fun a => (a, b)) := by
  simp only [pair, Code.map_law, Code.pair_law, PMF.map_bind, PMF.map_comp,
    PMF.bind_map, Function.comp_def]

theorem pair_bound {A B : Type} {first second l r : Nat}
    (left : Code (A × Nat) first) (right : Code (B × Nat) second)
    (hl : Bounded left l) (hr : Bounded right r) : Bounded (pair left right) (l + r + 2) := by
  intro Seed random seed
  have a := hl Seed random (right.run random seed).2
  have b := hr Seed random seed
  simp only [pair, Code.map_run, Code.pair, Code.run]
  omega

/-- Each recursion step appends one value to the sampled array. -/
def vector {A : Type} {draws : Nat} (code : Code (A × Nat) draws) :
    (count : Nat) → Code (Vector A count × Nat) (count * draws)
  | 0 => (Code.pure (#v[], 0)).cast (Nat.zero_mul draws).symm
  | count + 1 =>
    ((code.pair (vector code count)).map fun values =>
      (values.2.1.push values.1.1, values.2.2 + values.1.2 + 1)).cast (Nat.succ_mul count draws).symm

theorem vector_law {A : Type} {draws : Nat} (code : Code (A × Nat) draws)
    (reference : Code A draws) (same : code.law.map Prod.fst = reference.law) (count : Nat) :
    (vector code count).law.map Prod.fst = (reference.vector count).law := by
  induction count with
  | zero => simp [vector, Code.vector, Code.law, PMF.pure_map]
  | succ count ih =>
    simp only [vector, Code.cast_law, Code.map_law, Code.pair_law,
      PMF.map_bind, PMF.map_comp, Function.comp_def, Code.vector]
    have projected := congrArg (fun p : PMF (Vector A count) =>
      p.bind fun rest => reference.law.map (fun value => rest.push value)) ih
    simp only [PMF.bind_map] at projected
    have mappedSame (rest : Vector A count) :
        code.law.map (fun value => rest.push value.1) = reference.law.map rest.push := by
      rw [← same, PMF.map_comp]
      rfl
    simp_rw [mappedSame]
    simpa only [vectorPushEquiv, Equiv.coe_fn_mk] using projected

theorem vector_bound {A : Type} {draws limit : Nat} (code : Code (A × Nat) draws)
    (bounded : Bounded code limit) (count : Nat) :
    Bounded (vector code count) (count * (limit + 1)) := by
  induction count with
  | zero => intro Seed random seed; simp [vector, Code.run]
  | succ count ih =>
    intro Seed random seed
    have a := ih Seed random seed
    have b := bounded Seed random ((vector code count).run random seed).2
    simp only [vector, Code.cast_run, Code.map_run, Code.pair, Code.run, Code.map_run]
    nlinarith

private def mapped {A B : Type} {draws : Nat} (code : Code (A × Nat) draws)
    (f : A → B) (charge : Nat) : Code (B × Nat) draws :=
  code.map fun value => (f value.1, value.2 + charge)

private theorem mapped_law {A B : Type} {draws : Nat} (code : Code (A × Nat) draws)
    (f : A → B) (charge : Nat) :
    (mapped code f charge).law.map Prod.fst = (code.law.map Prod.fst).map f := by
  simp [mapped, Code.map_law, PMF.map_comp, Function.comp_def]

private theorem mapped_bound {A B : Type} {draws limit : Nat} (code : Code (A × Nat) draws)
    (bounded : Bounded code limit) (f : A → B) (charge : Nat) :
    Bounded (mapped code f charge) (limit + charge) := by
  intro Seed random seed
  simpa only [mapped, Code.map_run] using Nat.add_le_add_right (bounded Seed random seed) charge

private theorem cast_bound {A : Type} {first second limit : Nat} (same : first = second)
    (code : Code (A × Nat) first) (bounded : Bounded code limit) :
    Bounded (code.cast same) limit := by cases same; exact bounded

/-- The field callback charges its finite-residue conversion and result construction. -/
def fieldWithCost : Code (BaseField × Nat) 1 := field.map fun value => (value, 2)
/-- The block callback charges its finite-word conversion and result construction. -/
def bitsWithCost (width : Nat) : Code (BitVec width × Nat) 1 := (bits width).map fun value => (value, 2)
/-- The quotient draw already has the required finite type. -/
def quotientWithCost : Code (HashLiftQuotient × Nat) 1 := quotient.map fun value => (value, 1)
/-- The table constructor stores one sampled word. -/
def tableWithCost : Code (BitAdaptor.Table × Nat) 1 := mapped (bitsWithCost 256) tableEquiv 1

theorem field_law : fieldWithCost.law.map Prod.fst = field.law := by
  simp only [fieldWithCost, Code.map_law, PMF.map_comp, Function.comp_def ]
  exact PMF.map_id _
theorem bits_law (width : Nat) : (bitsWithCost width).law.map Prod.fst = (bits width).law := by
  simp only [bitsWithCost, Code.map_law, PMF.map_comp, Function.comp_def ]
  exact PMF.map_id _
theorem quotient_law : quotientWithCost.law.map Prod.fst = quotient.law := by
  simp only [quotientWithCost, Code.map_law, PMF.map_comp, Function.comp_def ]
  exact PMF.map_id _
theorem table_law : tableWithCost.law.map Prod.fst = table.law := by rw [tableWithCost, mapped_law, bits_law]; exact (Code.map_law _ _).symm

theorem field_bound : Bounded fieldWithCost 2 := by intro Seed random seed; simp [fieldWithCost, Code.map_run]
theorem bits_bound (width : Nat) : Bounded (bitsWithCost width) 2 := by intro Seed random seed; simp [bitsWithCost, Code.map_run]
theorem quotient_bound : Bounded quotientWithCost 1 := by intro Seed random seed; simp [quotientWithCost, Code.map_run]
theorem table_bound : Bounded tableWithCost 3 := mapped_bound _ (bits_bound 256) _ _

/-- This sampler counts every nested target, quotient, and table array push. -/
def gateWithCost (coefficients gates : Nat) : Code (GateArrays coefficients gates × Nat)
    (coefficients + 3 * gates * coordinateBitCount) :=
  (pair (vector fieldWithCost coefficients)
    (pair (vector (vector tableWithCost coordinateBitCount) gates)
      (pair (vector (vector quotientWithCost coordinateBitCount) gates)
        (vector (vector fieldWithCost coordinateBitCount) gates)))).cast (by ring)

theorem gate_law (coefficients gates : Nat) :
    (gateWithCost coefficients gates).law.map Prod.fst = (gateArrays coefficients gates).law := by
  simp only [gateWithCost, Code.cast_law, pair_law, vector_law _ _ field_law,
    gateArrays,
    Code.pair_law]
  rw [vector_law _ _ (vector_law _ _ table_law _) _,
    vector_law _ _ (vector_law _ _ quotient_law _) _,
    vector_law _ _ (vector_law _ _ field_law _) _]

theorem gate_bound (coefficients gates : Nat) :
    Bounded (gateWithCost coefficients gates)
      (3 * coefficients + gates * (9 * coordinateBitCount + 3) + 6) := by
  have bound := pair_bound _ _ (vector_bound _ field_bound coefficients)
    (pair_bound _ _ (vector_bound _ (vector_bound _ table_bound coordinateBitCount) gates)
      (pair_bound _ _ (vector_bound _ (vector_bound _ quotient_bound coordinateBitCount) gates)
        (vector_bound _ (vector_bound _ field_bound coordinateBitCount) gates)))
  apply cast_bound
  convert bound using 1
  ring

/-- The key sampler constructs each pair and each coordinate array. -/
def keyWithCost : Code (BitAdaptor.Key × Nat) 2 :=
  mapped (pair (bitsWithCost 128) (bitsWithCost 128)) keyEquiv 1

def inputKeyWithCost : Code (InputMacKey × Nat) 1016 :=
  mapped (pair (vector keyWithCost coordinateBitCount) (vector keyWithCost coordinateBitCount))
    inputKeyEquiv 1

theorem key_law : keyWithCost.law.map Prod.fst = key.law := by
  simp only [keyWithCost, mapped_law, pair_law, bits_law, key, Code.map_law, Code.pair_law]

theorem inputKey_law : inputKeyWithCost.law.map Prod.fst = inputKey.law := by
  simp only [inputKeyWithCost, mapped_law, pair_law, vector_law _ _ key_law,
    inputKey, Code.map_law, Code.pair_law]

theorem key_bound : Bounded keyWithCost 7 :=
  mapped_bound _ (pair_bound _ _ (bits_bound 128) (bits_bound 128)) _ _

theorem inputKey_bound : Bounded inputKeyWithCost 4067 :=
  mapped_bound _ (pair_bound _ _ (vector_bound _ key_bound _) (vector_bound _ key_bound _)) _ _

/-- The counted offline sampler retains all backing arrays. -/
def rowWithCost : Code (RowArrays × Nat) 9920 :=
  pair (gateWithCost 5 4) (pair (gateWithCost 4 4) (gateWithCost 5 5))

def publicWithCost : Code (PublicArrays × Nat) 906533 :=
  pair (gateWithCost 3 5) (vector rowWithCost FieldMacToECMac.outputMacCount)

def offlineWithCost : Code (OfflineArrays × Nat) 907550 :=
  pair publicWithCost (pair inputKeyWithCost fieldWithCost)

theorem row_law : rowWithCost.law.map Prod.fst = rowArrays.law := by
  simp only [rowWithCost, pair_law, gate_law, rowArrays, Code.pair_law]

theorem public_law : publicWithCost.law.map Prod.fst = publicArrays.law := by
  simp only [publicWithCost, pair_law, gate_law, vector_law _ _ row_law,
    publicArrays, Code.pair_law]

/-- Erasing the counter gives exactly the existing offline distribution. -/
theorem offline_law : offlineWithCost.law.map Prod.fst = offlineArrays.law := by
  simp only [offlineWithCost, pair_law, public_law, inputKey_law, field_law,
    offlineArrays, Code.pair_law]

theorem row_bound : Bounded rowWithCost 29821 :=
  pair_bound _ _ (gate_bound 5 4) (pair_bound _ _ (gate_bound 4 4) (gate_bound 5 5))

theorem public_bound : Bounded publicWithCost 2725264 :=
  pair_bound _ _ (gate_bound 3 5) (vector_bound _ row_bound FieldMacToECMac.outputMacCount)

/-- This bound includes every sampled array push and every value-record constructor. -/
theorem offline_bound : Bounded offlineWithCost 2729337 :=
  pair_bound _ _ public_bound (pair_bound _ _ inputKey_bound field_bound)

abbrev OnlineCoin [FieldCertificate] := (Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)

/-- Each scalar round charges division, remainder, a test, and three loop operations.
The addition count comes from the executed group algorithm. -/
def pointWithCost [FieldCertificate] : Code (Point × Nat) 1 :=
  scalar.map fun value =>
    let result := binaryPointMulWithCost 254 value.val standardGenerator
    (result.1, result.2 + 6 * 254 + 3)

def scaleWithCost : Code (NonZeroBase × Nat) 1 := scale.map fun value => (value, 4)

/-- The getter constructor retains the sampled array without copying it. -/
def arrayFunction {A : Type} {draws : Nat} (code : Code (A × Nat) draws) (count : Nat) :
    Code ((Fin count → A) × Nat) (count * draws) :=
  mapped (vector code count) (fun values => values.get) 1

def onlineWithCost [FieldCertificate] : Code (OnlineCoin × Nat) 181 :=
  pair (arrayFunction pointWithCost 90) (arrayFunction scaleWithCost FieldMacToECMac.outputMacCount)

theorem point_law [FieldCertificate] : pointWithCost.law.map Prod.fst = point.law := by
  simp only [pointWithCost, point, Code.map_law, PMF.map_comp, Function.comp_def]
  congr 1
  funext value
  exact (samplePoint_groupAdditions value).1

theorem scale_law : scaleWithCost.law.map Prod.fst = scale.law := by
  simp only [scaleWithCost, Code.map_law, PMF.map_comp, Function.comp_def]
  exact PMF.map_id scale.law

theorem arrayFunction_law {A : Type} {draws : Nat} (code : Code (A × Nat) draws)
    (reference : Code A draws) (same : code.law.map Prod.fst = reference.law) (count : Nat) :
    (arrayFunction code count).law.map Prod.fst = (reference.arrayFunction count).law := by
  rw [arrayFunction, mapped_law, vector_law _ _ same]
  exact (Code.map_law _ _).symm

/-- Erasing the counter gives exactly the existing online distribution. -/
theorem online_law [FieldCertificate] : onlineWithCost.law.map Prod.fst = online.law := by
  simp only [onlineWithCost, pair_law, arrayFunction_law _ _ point_law,
    arrayFunction_law _ _ scale_law, online, Code.pair_law]

theorem point_bound [FieldCertificate] : Bounded pointWithCost 2035 := by
  intro Seed random seed
  simp only [pointWithCost, Code.map_run]
  have bound := (samplePoint_groupAdditions (scalar.run random seed).1).2
  omega

theorem scale_bound : Bounded scaleWithCost 4 := by
  intro Seed random seed
  simp only [scaleWithCost, Code.map_run]
  exact Nat.le_refl _

theorem arrayFunction_bound {A : Type} {draws limit : Nat} (code : Code (A × Nat) draws)
    (bounded : Bounded code limit) (count : Nat) :
    Bounded (arrayFunction code count) (count * (limit + 1) + 1) :=
  mapped_bound _ (vector_bound _ bounded count) _ _

/-- The online bound includes 90 scalar loops and at most 45720 group additions. -/
theorem online_bound [FieldCertificate] : Bounded onlineWithCost 183699 :=
  pair_bound _ _ (arrayFunction_bound _ point_bound 90) (arrayFunction_bound _ scale_bound FieldMacToECMac.outputMacCount)

private theorem pair_size {A B : Type} {first second : Nat}
    (left : Code (A × Nat) first) (right : Code (B × Nat) second)
    (hl : left.DrawSizeLe (2 ^ 256)) (hr : right.DrawSizeLe (2 ^ 256)) :
    (pair left right).DrawSizeLe (2 ^ 256) :=
  Code.map_drawSizeLe _ _ (Code.pair_drawSizeLe _ _ hl hr)

private theorem vector_size {A : Type} {draws : Nat} (code : Code (A × Nat) draws)
    (bounded : code.DrawSizeLe (2 ^ 256)) (count : Nat) :
    (vector code count).DrawSizeLe (2 ^ 256) := by
  induction count with
  | zero => exact Code.cast_drawSizeLe _ _ trivial
  | succ count ih =>
    exact Code.cast_drawSizeLe _ _ (Code.map_drawSizeLe _ _ (Code.pair_drawSizeLe _ _ bounded ih))

private theorem mapped_size {A B : Type} {draws : Nat} (code : Code (A × Nat) draws)
    (bounded : code.DrawSizeLe (2 ^ 256)) (f : A → B) (charge : Nat) :
    (mapped code f charge).DrawSizeLe (2 ^ 256) := Code.map_drawSizeLe _ _ bounded

private theorem field_size : fieldWithCost.DrawSizeLe (2 ^ 256) := Code.map_drawSizeLe _ _ field_drawSizeLe
private theorem bits_size (width : Nat) (bounded : width ≤ 256) :
    (bitsWithCost width).DrawSizeLe (2 ^ 256) := Code.map_drawSizeLe _ _ (bits_drawSizeLe bounded)
private theorem quotient_size : quotientWithCost.DrawSizeLe (2 ^ 256) := Code.map_drawSizeLe _ _ quotient_drawSizeLe
private theorem table_size : tableWithCost.DrawSizeLe (2 ^ 256) := mapped_size _ (bits_size 256 (by decide)) _ _

private theorem gate_size (coefficients gates : Nat) :
    (gateWithCost coefficients gates).DrawSizeLe (2 ^ 256) :=
  Code.cast_drawSizeLe _ _ (pair_size _ _ (vector_size _ field_size coefficients)
    (pair_size _ _ (vector_size _ (vector_size _ table_size coordinateBitCount) gates)
      (pair_size _ _ (vector_size _ (vector_size _ quotient_size coordinateBitCount) gates)
        (vector_size _ (vector_size _ field_size coordinateBitCount) gates))))

private theorem key_size : keyWithCost.DrawSizeLe (2 ^ 256) :=
  mapped_size _ (pair_size _ _ (bits_size 128 (by decide)) (bits_size 128 (by decide))) _ _

/-- Every counted offline draw has the same finite range bound. -/
theorem offline_size : offlineWithCost.DrawSizeLe (2 ^ 256) :=
  pair_size _ _
    (pair_size _ _ (gate_size 3 5)
      (vector_size _ (pair_size _ _ (gate_size 5 4) (pair_size _ _ (gate_size 4 4) (gate_size 5 5))) _))
    (pair_size _ _ (mapped_size _
      (pair_size _ _ (vector_size _ key_size _) (vector_size _ key_size _)) _ _) field_size)

/-- Every counted online draw has the same finite range bound. -/
theorem online_size [FieldCertificate] : onlineWithCost.DrawSizeLe (2 ^ 256) := by
  have pointSize : pointWithCost.DrawSizeLe (2 ^ 256) :=
    Code.map_drawSizeLe _ _ (Code.map_drawSizeLe _ _ (by change scalarFieldModulus ≤ 2 ^ 256; decide))
  have scaleSize : scaleWithCost.DrawSizeLe (2 ^ 256) := Code.map_drawSizeLe _ _ scale_drawSizeLe
  exact pair_size _ _ (mapped_size _ (vector_size _ pointSize 90) _ _)
    (mapped_size _ (vector_size _ scaleSize FieldMacToECMac.outputMacCount) _ _)

open SimulatorMachine BoundedIntegerSampling SimulatorRejectionCost

private def mapBits {A B : Type} (f : A → B) (code : BitCode A) : BitCode B :=
  code.bind fun value => .pure (f value)

private theorem mapBits_law {A B : Type} (f : A → B) (code : BitCode A) :
    (mapBits f code).law = code.law.map f := by
  simp [mapBits, BitCode.bind_law, BitCode.law, PMF.map, Function.comp_def]

private theorem mapBits_run {A B Seed : Type} (f : A → B) (code : BitCode A)
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (seed : Seed) :
    (mapBits f code).run random seed =
      ((f (code.run random seed).1.1, (code.run random seed).1.2), (code.run random seed).2) := by
  simp [mapBits, BitCode.bind_run, BitCode.run]

/-- This bind retains work from a completed prefix when a later draw fails. -/
def chargedBind {A B : Type} (source : BitCode (Option A × Nat))
    (next : A → BitCode (Option B × Nat)) : BitCode (Option B × Nat) :=
  source.bind fun first => match first.1 with
    | none => .pure (none, first.2)
    | some value => mapBits (fun second => (second.1, first.2 + second.2)) (next value)

theorem chargedBind_law {A B : Type} (source : BitCode (Option A × Nat))
    (next : A → BitCode (Option B × Nat)) :
    (chargedBind source next).law.map Prod.fst =
      (source.law.map Prod.fst).bind (optionalPMF fun value => (next value).law.map Prod.fst) := by
  simp only [chargedBind, BitCode.bind_law, PMF.map_bind, PMF.bind_map]
  congr 1
  funext first
  rcases first with ⟨first, cost⟩
  cases first <;> simp only [optionalPMF, BitCode.law, PMF.pure_map, mapBits_law,
    PMF.map_comp, Function.comp_def]

theorem chargedBind_cost {A B Seed : Type} (source : BitCode (Option A × Nat))
    (next : A → BitCode (Option B × Nat)) (first second : Nat)
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (hl : ∀ seed, (source.run random seed).1.1.2 ≤ first)
    (hr : ∀ value seed, ((next value).run random seed).1.1.2 ≤ second) (seed : Seed) :
    ((chargedBind source next).run random seed).1.1.2 ≤ first + second := by
  simp only [chargedBind, BitCode.bind_run]
  split
  · simp only [BitCode.run]
    exact (hl seed).trans (Nat.le_add_right _ _)
  · rename_i value same
    simp only [mapBits_run]
    exact Nat.add_le_add (hl seed) (hr value _)

theorem chargedBind_bits {A B Seed : Type} (source : BitCode (Option A × Nat))
    (next : A → BitCode (Option B × Nat)) (first second : Nat)
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (hl : ∀ seed, (source.run random seed).2 ≤ first)
    (hr : ∀ value seed, ((next value).run random seed).2 ≤ second) (seed : Seed) :
    ((chargedBind source next).run random seed).2 ≤ first + second := by
  simp only [chargedBind, BitCode.bind_run]
  split
  · simp only [BitCode.run, Nat.add_zero]
    exact (hl seed).trans (Nat.le_add_right _ _)
  · rename_i value same
    simp only [mapBits_run]
    exact Nat.add_le_add (hl seed) (hr value _)

private theorem mapBits_positive {A B : Type} (f : A → B) (code : BitCode A)
    (positive : PositiveWidths code) : PositiveWidths (mapBits f code) :=
  positive_bind code _ positive (fun _ => trivial)

private theorem chargedBind_positive {A B : Type} (source : BitCode (Option A × Nat))
    (next : A → BitCode (Option B × Nat)) (left : PositiveWidths source)
    (right : ∀ value, PositiveWidths (next value)) : PositiveWidths (chargedBind source next) := by
  apply positive_bind _ _ left
  intro first
  cases first.1 with
  | none => trivial
  | some value => exact mapBits_positive _ _ (right value)

/-- The finite sampler proves its complete output law and its cost on failure too. -/
structure FiniteRecipe {A : Type} {draws : Nat} (reference : Code A draws) (limit : Nat) where
  run : Nat → BitCode (Option A × Nat)
  positive : ∀ attempts, PositiveWidths (run attempts)
  law : ∀ attempts, CutoffLaw attempts draws reference.law ((run attempts).law.map Prod.fst)
  cost : ∀ attempts (Seed : Type) (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) seed,
    ((run attempts).run random seed).1.1.2 ≤ limit
  bits : ∀ attempts (Seed : Type) (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) seed,
    ((run attempts).run random seed).2 ≤ draws * (257 * attempts)

namespace FiniteRecipe

def pure (value : A) (charge : Nat) : FiniteRecipe (Code.pure value) charge where
  run _ := .pure (some value, charge)
  positive _ := trivial
  law attempts := by
    simpa only [Code.law, BitCode.law, PMF.pure_map] using
      (CutoffLaw.exact attempts (PMF.pure value))
  cost := by intros; exact Nat.le_refl _
  bits := by intros; simp [BitCode.run]

def bind {A B : Type} {first second l r : Nat} {source : Code A first}
    {next : A → Code B second} (left : FiniteRecipe source l)
    (right : ∀ value, FiniteRecipe (next value) r) :
    FiniteRecipe (Code.bind source next) (l + r) where
  run attempts := chargedBind (left.run attempts) (fun value => (right value).run attempts)
  positive attempts := chargedBind_positive _ _ (left.positive attempts) (fun value => (right value).positive attempts)
  law attempts := by
    rw [chargedBind_law]
    exact (left.law attempts).bind (fun value => (right value).law attempts)
  cost attempts Seed random seed := chargedBind_cost _ _ l r random
    (left.cost attempts Seed random) (fun value => (right value).cost attempts Seed random) seed
  bits attempts Seed random seed := by
    rw [Nat.add_mul]
    exact chargedBind_bits _ _ _ _ random (left.bits attempts Seed random)
      (fun value => (right value).bits attempts Seed random) seed

def cast {A : Type} {first second limit : Nat} {reference : Code A first}
    (same : first = second) (recipe : FiniteRecipe reference limit) :
    FiniteRecipe (reference.cast same) limit := by cases same; exact recipe

def map {A B : Type} {draws limit : Nat} {reference : Code A draws}
    (recipe : FiniteRecipe reference limit) (f : A → B) (charge : Nat) :
    FiniteRecipe (reference.map f) (limit + charge) :=
  cast (Nat.add_zero draws) (bind recipe fun value => pure (f value) charge)

def pair {A B : Type} {first second l r : Nat} {left : Code A first} {right : Code B second}
    (a : FiniteRecipe left l) (b : FiniteRecipe right r) :
    FiniteRecipe (left.pair right) (r + (l + 2)) :=
  bind b fun right => map a (fun left => (left, right)) 2

def vector {A : Type} {draws limit : Nat} {reference : Code A draws}
    (recipe : FiniteRecipe reference limit) :
    (count : Nat) → FiniteRecipe (reference.vector count) (count * (limit + 3))
  | 0 => by simpa only [Nat.zero_mul] using cast (Nat.zero_mul draws).symm (pure #v[] 0)
  | count + 1 => by
    have result := cast (Nat.succ_mul count draws).symm
      (map (pair recipe (vector recipe count)) (vectorPushEquiv A count) 1)
    convert result using 1
    ring

/-- The integer primitive charges one result construction only after success. -/
def draw (size : Nat) (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    FiniteRecipe (Code.draw size positive) 1 where
  run attempts := mapBits (fun value => (value, if value.isSome then 1 else 0))
    ((Code.draw size positive).cutoff attempts)
  positive attempts := mapBits_positive _ _ (code_cutoff_positive _ attempts)
  law attempts := by
    rw [mapBits_law, PMF.map_comp]
    change CutoffLaw attempts 1 _ (PMF.map id _)
    rw [PMF.map_id]
    exact CutoffLaw.code attempts (Code.draw size positive)
  cost attempts Seed random seed := by
    rw [mapBits_run]
    split <;> simp
  bits attempts Seed random seed := by
    rw [mapBits_run]
    simpa only [Nat.one_mul] using
      (Code.draw size positive).cutoff_bit_bound random attempts bounded seed

/-- This map uses the local counter produced by the concrete callback. -/
def mapWork {A B : Type} {draws limit extra : Nat} {reference : Code A draws}
    (recipe : FiniteRecipe reference limit) (f : A → B × Nat)
    (bounded : ∀ value, (f value).2 ≤ extra) :
    FiniteRecipe (reference.map fun value => (f value).1) (limit + extra) where
  run attempts := chargedBind (recipe.run attempts) fun value => .pure (some (f value).1, (f value).2)
  positive attempts := chargedBind_positive _ _ (recipe.positive attempts) (fun _ => trivial)
  law attempts := by
    rw [chargedBind_law]
    have law := (recipe.law attempts).bind (fun value => (pure (f value).1 (f value).2).law attempts)
    simpa only [Code.map_law, Code.law, PMF.pure_map, BitCode.law,
      Nat.add_zero, PMF.map] using law
  cost attempts Seed random seed :=
    chargedBind_cost (recipe.run attempts)
      (fun value => BitCode.pure (some (f value).1, (f value).2)) limit extra random
      (recipe.cost attempts Seed random)
      (fun value _ => bounded value) seed
  bits attempts Seed random seed := by
    have bound := chargedBind_bits (recipe.run attempts)
      (fun value => BitCode.pure (some (f value).1, (f value).2)) (draws * (257 * attempts)) 0 random
      (recipe.bits attempts Seed random) (fun _ _ => Nat.le_refl 0) seed
    simpa only [Nat.add_zero] using bound

/-- Equal reference laws use the same executable sampler and cost proof. -/
def relabel {A : Type} {draws limit : Nat} {reference other : Code A draws}
    (recipe : FiniteRecipe reference limit) (same : reference.law = other.law) :
    FiniteRecipe other limit where
  run := recipe.run
  positive := recipe.positive
  law attempts := by rw [← same]; exact recipe.law attempts
  cost := recipe.cost
  bits := recipe.bits

end FiniteRecipe

private def finiteField : FiniteRecipe field 2 :=
  (FiniteRecipe.draw baseFieldModulus (by decide) (by decide)).map baseFieldFinEquiv 1

private def finiteBits (width : Nat) (bounded : width ≤ 256) : FiniteRecipe (bits width) 2 :=
  (FiniteRecipe.draw (2 ^ width) (Nat.two_pow_pos width)
    (Nat.pow_le_pow_right (by decide) bounded)).map BitVec.equivFin.symm.toEquiv 1

set_option exponentiation.threshold 400 in
private def finiteQuotient : FiniteRecipe quotient 1 :=
  FiniteRecipe.draw hashLiftQuotientCount (by decide) (by decide)

private def finiteTable : FiniteRecipe table 3 := (finiteBits 256 (by decide)).map tableEquiv 1

private def finiteGate (coefficients gates : Nat) :
    FiniteRecipe (gateArrays coefficients gates)
      (5 * coefficients + gates * (15 * coordinateBitCount + 9) + 6) := by
  have result := FiniteRecipe.cast (second := coefficients + 3 * gates * coordinateBitCount) (by ring)
    ((finiteField.vector coefficients).pair
      (((finiteTable.vector coordinateBitCount).vector gates).pair
        (((finiteQuotient.vector coordinateBitCount).vector gates).pair
          ((finiteField.vector coordinateBitCount).vector gates))))
  convert result using 1
  ring

private def finiteKey : FiniteRecipe key 7 :=
  ((finiteBits 128 (by decide)).pair (finiteBits 128 (by decide))).map keyEquiv 1

private def finiteInputKey : FiniteRecipe inputKey 5083 :=
  ((finiteKey.vector coordinateBitCount).pair (finiteKey.vector coordinateBitCount)).map inputKeyEquiv 1

private def finiteRow : FiniteRecipe rowArrays 49739 :=
  (finiteGate 5 4).pair ((finiteGate 4 4).pair (finiteGate 5 5))

private def finitePublic : FiniteRecipe publicArrays 4545640 :=
  (finiteGate 3 5).pair (finiteRow.vector FieldMacToECMac.outputMacCount)

/-- This actual finite sampler retains the work counter on every failed prefix. -/
def offlineFinite : FiniteRecipe offlineArrays 4550729 :=
  finitePublic.pair (finiteInputKey.pair finiteField)

private def finiteScalar : FiniteRecipe scalar 2 :=
  (FiniteRecipe.draw scalarFieldModulus (by decide) (by decide)).map scalarEquiv 1

/-- The callback executes the 254-round point algorithm once.
Its counter adds the actual group additions to the scalar and loop charge. -/
private def finitePoint [FieldCertificate] : FiniteRecipe point 2035 := by
  let callback (value : ScalarField) : Point × Nat :=
    let result := binaryPointMulWithCost 254 value.val standardGenerator
    (result.1, result.2 + 6 * 254 + 1)
  have bound (value : ScalarField) : (callback value).2 ≤ 2033 := by
    have bounded := (samplePoint_groupAdditions value).2
    dsimp only [callback]
    omega
  exact (finiteScalar.mapWork callback bound).relabel (by
    simp only [Code.map_law, point]
    congr 1
    funext value
    exact (samplePoint_groupAdditions value).1)

private def finiteScale : FiniteRecipe scale 4 :=
  (FiniteRecipe.draw (baseFieldModulus - 1) (by decide) (by decide)).map nonzeroEquiv 3

private def finiteArrayFunction {A : Type} {draws limit : Nat} {reference : Code A draws}
    (recipe : FiniteRecipe reference limit) (count : Nat) :
    FiniteRecipe (reference.arrayFunction count) (count * (limit + 3) + 1) :=
  (recipe.vector count).map vectorFunctionEquiv.symm 1

/-- This online sampler retains the scalar and array work on every failed prefix. -/
def onlineFinite [FieldCertificate] : FiniteRecipe online 184061 :=
  (finiteArrayFunction finitePoint 90).pair
    (finiteArrayFunction finiteScale FieldMacToECMac.outputMacCount)


/-- This projection removes only the accounting value. -/
def eraseCost {A : Type} (code : BitCode (Option A × Nat)) : BitCode (Option A) :=
  mapBits Prod.fst code

theorem eraseCost_law {A : Type} (code : BitCode (Option A × Nat)) :
    (eraseCost code).law = code.law.map Prod.fst := mapBits_law _ _

theorem eraseCost_positive {A : Type} (code : BitCode (Option A × Nat))
    (positive : PositiveWidths code) : PositiveWidths (eraseCost code) :=
  mapBits_positive _ _ positive

theorem eraseCost_run {A Seed : Type} (code : BitCode (Option A × Nat))
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (seed : Seed) :
    (eraseCost code).run random seed =
      (((code.run random seed).1.1.1, (code.run random seed).1.2), (code.run random seed).2) :=
  mapBits_run _ _ _ _

/-- Removing the accounting value consumes no additional fair bits. -/
theorem eraseCost_bits {A Seed : Type} (code : BitCode (Option A × Nat))
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (seed : Seed) :
    ((eraseCost code).run random seed).2 = (code.run random seed).2 := by
  rw [eraseCost, mapBits_run]

end Kriterion.ArgoMAC.Security.SimulatorSamplingCost
