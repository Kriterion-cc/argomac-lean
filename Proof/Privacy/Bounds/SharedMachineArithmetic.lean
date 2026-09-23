import Proof.Privacy.Bounds.SharedAdaptiveArithmetic
import Architect

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions

/-- The sampler allowance counts the private draws, all internal operations, and all public queries. -/
noncomputable def sharedMachineCutoffAllowance (queries : Nat) : ℝ :=
  ((2138378 + queries : Nat) : ℝ) / (2 : ℝ) ^ 256

/-- The joint arithmetic envelope leaves room for all bounded sampler cutoffs. -/
theorem sharedAdaptiveAndCutoff_has100Bits (queries : Nat) :
    WorkPerAdvantage 100 (queries + 1)
      (adaptiveErrorEnvelope queries + sharedMachineCutoffAllowance queries) := by
  change ((((251850146 + 833 * queries : Nat) : ℝ) / (2 : ℝ) ^ 128 +
      ((2138378 + queries : Nat) : ℝ) / (2 : ℝ) ^ 256) * (2 : ℝ) ^ 100) ≤ ((queries + 1 : Nat) : ℝ)
  push_cast
  norm_num
  linarith [Nat.cast_nonneg (α := ℝ) queries]

/-- The actual privacy and implementation errors satisfy the combined work property. -/
@[blueprint "Security.sharedErrors_has100Bits"
  (statement := /-- Security level (Lemma~14). If the privacy error is at most $\varepsilon_3(q)$ and the
    implementation error is at most the cutoff allowance of $q$, then $(q + 1) / (\text{privacy
    error} + \text{implementation error}) \geq 2^{100}$. -/)
  (title := /-- BABE Lemma~14 -/)]
theorem sharedErrors_has100Bits (queries : Nat) (privacyError implementationError : ℝ)
    (privacyBound : privacyError ≤ adaptiveErrorEnvelope queries)
    (implementationBound : implementationError ≤ sharedMachineCutoffAllowance queries) :
    WorkPerAdvantage 100 (queries + 1) (privacyError + implementationError) := by
  /-- Add the two bounds. Multiply by $2^{100}$. The envelope $\varepsilon_3$ plus the cutoff
    allowance has $100$ bits of work. -/
  apply (mul_le_mul_of_nonneg_right (add_le_add privacyBound implementationBound)
    (by positivity : 0 ≤ (2 : ℝ) ^ 100)).trans
  exact sharedAdaptiveAndCutoff_has100Bits queries

/-- Large query budgets cover the sum of both unit-bounded decision advantages. -/
@[blueprint "Security.sharedLargeBudget_has100Bits"
  (statement := /-- Large budgets. When $q \geq 2^{101}$, the sum of two advantages, each at most $1$, satisfies $(q
    + 1) / (\delta + \delta') \geq 2^{100}$. -/)
  (title := /-- BABE Lemma~14 -/)]
theorem sharedLargeBudget_has100Bits (real ideal bounded : PMF Bool) (queries : Nat)
    (large : 2 ^ 101 ≤ queries) :
    WorkPerAdvantage 100 (queries + 1) (advantage real ideal + advantage ideal bounded) := by
  /-- Each advantage is at most one, so the sum is at most two. Multiply by $2^{100}$. The budget plus
    one is at least $2^{101}$, which dominates. -/
  unfold WorkPerAdvantage
  have errors : advantage real ideal + advantage ideal bounded ≤ 2 := by
    linarith [decisionAdvantage_le_one real ideal, decisionAdvantage_le_one ideal bounded]
  apply (mul_le_mul_of_nonneg_right errors (by positivity : 0 ≤ (2 : ℝ) ^ 100)).trans
  have enough : ((2 ^ 101 : Nat) : ℝ) ≤ ((queries + 1 : Nat) : ℝ) := by
    exact_mod_cast large.trans (Nat.le_succ queries)
  norm_num at enough ⊢
  exact enough

end Kriterion.ArgoMAC.Security
