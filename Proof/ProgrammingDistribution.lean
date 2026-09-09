import Proof.PermutationCounting

namespace Kriterion.ArgoMAC.Security

noncomputable section

private theorem uniformOfFintype_map_fst_equiv
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C] (e : A ≃ B × C) :
    (PMF.uniformOfFintype A).map (fun a => (e a).1) = PMF.uniformOfFintype B := by
  classical
  apply PMF.ext
  intro b
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply]
  rw [e.tsum_eq (fun pair => if b = pair.1 then (Fintype.card A : ENNReal)⁻¹ else 0),
    ENNReal.tsum_prod']
  rw [ENNReal.tsum_comm]
  simp_rw [@eq_comm B b]
  simp only [tsum_ite_eq]
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _)), mul_comm, mul_assoc,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), mul_one]

variable {α : Type*} [Fintype α] [DecidableEq α]
  (s t : Set α) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
  (e : s ≃ t) (x : α) (freshInput : x ∉ s) (y : α) (freshOutput : y ∉ t)

/-- This map programs a fresh point and preserves the earlier assignment. -/
def programCompatiblePermutation
    (π : {π : Equiv.Perm α // ∀ a : s, π a = e a}) :
    {π : Equiv.Perm α // (∀ a : s, π a = e a) ∧ π x = y} := by
  refine ⟨π.1.trans (Equiv.swap (π.1 x) y), ?_, ?_⟩
  · intro a
    rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne]
    · exact π.2 a
    · intro same
      exact freshInput (π.1.injective same ▸ a.2)
    · intro same
      exact freshOutput (same ▸ (π.2 a ▸ (e a).2))
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]

/-- The old output supplies the exact information that programming removes. -/
def programCompatiblePermutationEquiv :
    {π : Equiv.Perm α // ∀ a : s, π a = e a} ≃
      {π : Equiv.Perm α // (∀ a : s, π a = e a) ∧ π x = y} × (tᶜ : Set α) where
  toFun π := ⟨programCompatiblePermutation s t e x freshInput y freshOutput π,
    ⟨π.1 x, by
      intro member
      obtain ⟨a, same⟩ := e.surjective ⟨π.1 x, member⟩
      have hit : π.1 a = π.1 x := (π.2 a).trans (congrArg Subtype.val same)
      exact freshInput (π.1.injective hit ▸ a.2)⟩⟩
  invFun pair :=
    ⟨(programCompatiblePermutation s t e x freshInput pair.2 pair.2.2
      ⟨pair.1.1, pair.1.2.1⟩).1,
      (programCompatiblePermutation s t e x freshInput pair.2 pair.2.2
        ⟨pair.1.1, pair.1.2.1⟩).2.1⟩
  left_inv π := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    simp only [programCompatiblePermutation, Equiv.trans_apply, Equiv.swap_apply_left]
    rw [Equiv.swap_comm y (π.1 x), Equiv.swap_apply_self]
  right_inv pair := by
    apply Prod.ext
    · apply Subtype.ext
      apply Equiv.ext
      intro a
      simp only [programCompatiblePermutation, Equiv.trans_apply, pair.1.2.2,
        Equiv.swap_apply_left]
      rw [Equiv.swap_comm (pair.2 : α) y, Equiv.swap_apply_self]
    · apply Subtype.ext
      simp only [programCompatiblePermutation, Equiv.trans_apply, pair.1.2.2,
        Equiv.swap_apply_left]

local instance compatiblePermutationNonempty :
    Nonempty {π : Equiv.Perm α // ∀ a : s, π a = e a} :=
  ⟨⟨e.extendSubtype, fun a => e.extendSubtype_apply_of_mem a a.2⟩⟩

/-- Fresh-point programming gives the uniform extended assignment. -/
theorem programCompatiblePermutation_uniform
    : letI : Nonempty {π : Equiv.Perm α // (∀ a : s, π a = e a) ∧ π x = y} :=
        ⟨programCompatiblePermutation s t e x freshInput y freshOutput
          (Classical.choice (compatiblePermutationNonempty s t e))⟩
    (PMF.uniformOfFintype {π : Equiv.Perm α // ∀ a : s, π a = e a}).map
        (programCompatiblePermutation s t e x freshInput y freshOutput) =
      PMF.uniformOfFintype {π : Equiv.Perm α // (∀ a : s, π a = e a) ∧ π x = y} := by
  letI : Nonempty {π : Equiv.Perm α // (∀ a : s, π a = e a) ∧ π x = y} :=
    ⟨programCompatiblePermutation s t e x freshInput y freshOutput
      (Classical.choice (compatiblePermutationNonempty s t e))⟩
  letI : Nonempty (tᶜ : Set α) := ⟨⟨y, freshOutput⟩⟩
  exact uniformOfFintype_map_fst_equiv
    (programCompatiblePermutationEquiv s t e x freshInput y freshOutput)

end

end Kriterion.ArgoMAC.Security
