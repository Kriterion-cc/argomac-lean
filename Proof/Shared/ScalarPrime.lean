import BN254
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic

namespace Kriterion.BN254

/-- This function computes a modular power with an accumulator. -/
def modularPower (modulus : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, accumulator => accumulator % modulus
  | fuel + 1, base, exponent, accumulator =>
    modularPower modulus fuel (base * base % modulus) (exponent / 2)
      (accumulator * (if exponent % 2 = 0 then 1 else base) % modulus)

/-- Enough exponent bits make the modular-power result exact. -/
theorem modularPower_correct (modulus fuel base exponent accumulator : Nat)
    (bound : exponent < 2 ^ fuel) :
    (modularPower modulus fuel base exponent accumulator : ZMod modulus) =
      (accumulator : ZMod modulus) * (base : ZMod modulus) ^ exponent := by
  induction fuel generalizing base exponent accumulator with
  | zero =>
    have zero : exponent = 0 := by simpa using bound
    simp [zero, modularPower]
  | succ fuel inductionHypothesis =>
    have halfBound : exponent / 2 < 2 ^ fuel := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [pow_succ] using bound
    rw [modularPower, inductionHypothesis _ _ _ halfBound]
    simp only [ZMod.natCast_mod, Nat.cast_mul, mul_pow]
    have decomposition : exponent = exponent / 2 + exponent / 2 + exponent % 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one exponent with even | odd
    · rw [even, if_pos rfl, Nat.cast_one, mul_one]
      conv_rhs => rw [decomposition, even, Nat.add_zero, pow_add]
    · rw [odd, if_neg (by decide)]
      conv_rhs => rw [decomposition, odd, pow_add, pow_add, pow_one]
      ring

/-- A complete factor list and modular witnesses prove primality. -/
theorem prime_of_modular_certificate (modulus base fuel : Nat) (factors : List Nat)
    (size : 1 < modulus) (bound : modulus ≤ 2 ^ fuel)
    (factorization : factors.prod = modulus - 1)
    (factorPrimes : ∀ factor ∈ factors, Nat.Prime factor)
    (fermat : modularPower modulus fuel base (modulus - 1) 1 % modulus = 1)
    (witnesses : ∀ factor ∈ factors,
      modularPower modulus fuel base ((modulus - 1) / factor) 1 % modulus ≠ 1) :
    Nat.Prime modulus := by
  haveI : NeZero modulus := ⟨by omega⟩
  have power (exponent : Nat) (bound : exponent < 2 ^ fuel) :
      (modularPower modulus fuel base exponent 1 : ZMod modulus) =
        (base : ZMod modulus) ^ exponent := by
    simpa only [Nat.cast_one, one_mul] using modularPower_correct modulus fuel base exponent 1 bound
  have powerBound : modulus - 1 < 2 ^ fuel := by omega
  apply lucas_primality modulus (base : ZMod modulus)
  · rw [← power _ powerBound]
    have h := (ZMod.natCast_eq_natCast_iff
      (modularPower modulus fuel base (modulus - 1) 1) 1 modulus).mpr
      (by simpa only [Nat.ModEq, Nat.mod_eq_of_lt size] using fermat)
    simpa only [Nat.cast_one] using h
  · intro prime primeProof divides
    rw [← factorization] at divides
    obtain ⟨factor, member, dividesFactor⟩ := primeProof.prime.dvd_prod_iff.mp divides
    have equal : prime = factor :=
      ((Nat.dvd_prime (factorPrimes factor member)).mp dividesFactor).resolve_left primeProof.ne_one
    subst factor
    rw [← power _ ((Nat.div_le_self _ _).trans_lt powerBound)]
    intro equal
    apply witnesses prime member
    have h := (ZMod.natCast_eq_natCast_iff
      (modularPower modulus fuel base ((modulus - 1) / prime) 1) 1 modulus).mp
      (by simpa only [Nat.cast_one] using equal)
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt size] using h

private theorem scalarPrime_aux_1637 : Nat.Prime 1637 := by
  apply prime_of_modular_certificate 1637 2 11
    [2, 2, 409] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals first | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_3691 : Nat.Prime 3691 := by
  apply prime_of_modular_certificate 3691 2 12
    [2, 3, 3, 5, 41] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals first | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_4999 : Nat.Prime 4999 := by
  apply prime_of_modular_certificate 4999 3 13
    [2, 3, 7, 7, 17] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals first | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_5501 : Nat.Prime 5501 := by
  apply prime_of_modular_certificate 5501 2 13
    [2, 2, 5, 5, 5, 11] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_11003 : Nat.Prime 11003 := by
  apply prime_of_modular_certificate 11003 2 14
    [2, 5501] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    all_goals first | exact scalarPrime_aux_5501 | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_20963 : Nat.Prime 20963 := by
  apply prime_of_modular_certificate 20963 2 15
    [2, 47, 223] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals first | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_41927 : Nat.Prime 41927 := by
  apply prime_of_modular_certificate 41927 5 16
    [2, 20963] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    all_goals first | exact scalarPrime_aux_20963 | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_93001 : Nat.Prime 93001 := by
  apply prime_of_modular_certificate 93001 14 17
    [2, 2, 2, 3, 5, 5, 5, 31] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_237073 : Nat.Prime 237073 := by
  apply prime_of_modular_certificate 237073 15 18
    [2, 2, 2, 2, 3, 11, 449] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_1593227 : Nat.Prime 1593227 := by
  apply prime_of_modular_certificate 1593227 2 21
    [2, 19, 41927] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals first | exact scalarPrime_aux_41927 | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_405928799 : Nat.Prime 405928799 := by
  apply prime_of_modular_certificate 405928799 22 29
    [2, 11, 4999, 3691] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals first | exact scalarPrime_aux_4999 | exact scalarPrime_aux_3691 | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_639533339 : Nat.Prime 639533339 := by
  apply prime_of_modular_certificate 639533339 2 30
    [2, 229, 853, 1637] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals first | exact scalarPrime_aux_1637 | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_12048837557 : Nat.Prime 12048837557 := by
  apply prime_of_modular_certificate 12048837557 2 34
    [2, 2, 7, 7, 661, 93001] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact scalarPrime_aux_93001 | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_5156902474397 : Nat.Prime 5156902474397 := by
  apply prime_of_modular_certificate 5156902474397 2 43
    [2, 2, 107, 12048837557] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals first | exact scalarPrime_aux_12048837557 | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_1670836401704629 : Nat.Prime 1670836401704629 := by
  apply prime_of_modular_certificate 1670836401704629 2 51
    [2, 2, 3, 3, 3, 3, 5156902474397] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact scalarPrime_aux_5156902474397 | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_65865678001877903 : Nat.Prime 65865678001877903 := by
  apply prime_of_modular_certificate 65865678001877903 5 56
    [2, 83, 379, 1637, 639533339] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact scalarPrime_aux_1637 | exact scalarPrime_aux_639533339 | norm_num
  · decide +kernel
  · decide +kernel

private theorem scalarPrime_aux_13818364434197438864469338081 : Nat.Prime 13818364434197438864469338081 := by
  apply prime_of_modular_certificate 13818364434197438864469338081 3 94
    [2, 2, 2, 2, 2, 5, 823, 1593227, 65865678001877903] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact scalarPrime_aux_1593227 | exact scalarPrime_aux_65865678001877903 | norm_num
  · decide +kernel
  · decide +kernel

theorem scalarFieldPrime : Nat.Prime scalarFieldModulus := by
  apply prime_of_modular_certificate 21888242871839275222246405745257275088548364400416034343698204186575808495617 5 254
    [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 13, 29, 983, 237073, 11003, 405928799, 1670836401704629, 13818364434197438864469338081] (by decide) (by decide) (by decide)
  · intro factor member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact scalarPrime_aux_237073 | exact scalarPrime_aux_11003 | exact scalarPrime_aux_405928799 | exact scalarPrime_aux_1670836401704629 | exact scalarPrime_aux_13818364434197438864469338081 | norm_num
  · decide +kernel
  · decide +kernel

end Kriterion.BN254
