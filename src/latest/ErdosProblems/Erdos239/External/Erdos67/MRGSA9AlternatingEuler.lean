import ErdosProblems.Erdos239.External.Erdos67.MRGSA9FiniteEuler

/-!
# Alternating Euler products in the two-block A.9 argument

The four low-prime deletion series factor exactly into the product over the
primes outside both blocks and one `EulerProduct - 1` factor for each block.
This is the exact finite algebra behind the first two lines of (A.11).
-/

open scoped BigOperators LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Inclusion--exclusion for products over two disjoint subfamilies. -/
theorem alternating_filtered_products_eq
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (Q R : ι → Prop) [DecidablePred Q] [DecidablePred R]
    (hdisj : ∀ x ∈ S, Q x → R x → False) (a : ι → ℂ) :
    (∏ x ∈ S, a x) - (∏ x ∈ S with ¬ Q x, a x) -
        (∏ x ∈ S with ¬ R x, a x) +
        (∏ x ∈ S with ¬ (Q x ∨ R x), a x) =
      (∏ x ∈ S with ¬ Q x ∧ ¬ R x, a x) *
        ((∏ x ∈ S with Q x, a x) - 1) *
        ((∏ x ∈ S with R x, a x) - 1) := by
  let A := S.filter Q
  let B := S.filter R
  let O := S.filter (fun x ↦ ¬ Q x ∧ ¬ R x)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact hdisj x (Finset.mem_filter.mp hxA).1
      (Finset.mem_filter.mp hxA).2 (Finset.mem_filter.mp hxB).2
  have hAO : Disjoint A O := by
    rw [Finset.disjoint_left]
    intro x hxA hxO
    exact (Finset.mem_filter.mp hxO).2.1 (Finset.mem_filter.mp hxA).2
  have hBO : Disjoint B O := by
    rw [Finset.disjoint_left]
    intro x hxB hxO
    exact (Finset.mem_filter.mp hxO).2.2 (Finset.mem_filter.mp hxB).2
  have hA_BO : Disjoint A (B ∪ O) := by
    rw [Finset.disjoint_left]
    intro x hxA hxBO
    rw [Finset.mem_union] at hxBO
    exact hxBO.elim (fun hxB ↦ Finset.disjoint_left.mp hAB hxA hxB)
      (fun hxO ↦ Finset.disjoint_left.mp hAO hxA hxO)
  have hpartition : A ∪ (B ∪ O) = S := by
    ext x
    simp only [A, B, O, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩ | ⟨hx, _⟩)
      all_goals exact hx
    · intro hx
      by_cases hQ : Q x
      · exact Or.inl ⟨hx, hQ⟩
      · by_cases hR : R x
        · exact Or.inr (Or.inl ⟨hx, hR⟩)
        · exact Or.inr (Or.inr ⟨hx, hQ, hR⟩)
  have hnotQ : S.filter (fun x ↦ ¬ Q x) = B ∪ O := by
    ext x
    simp only [B, O, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx, hnQ⟩
      by_cases hR : R x
      · exact Or.inl ⟨hx, hR⟩
      · exact Or.inr ⟨hx, hnQ, hR⟩
    · rintro (⟨hx, hR⟩ | ⟨hx, hnQ, _⟩)
      · exact ⟨hx, fun hQ ↦ hdisj x hx hQ hR⟩
      · exact ⟨hx, hnQ⟩
  have hnotR : S.filter (fun x ↦ ¬ R x) = A ∪ O := by
    ext x
    simp only [A, O, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx, hnR⟩
      by_cases hQ : Q x
      · exact Or.inl ⟨hx, hQ⟩
      · exact Or.inr ⟨hx, hQ, hnR⟩
    · rintro (⟨hx, hQ⟩ | ⟨hx, _, hnR⟩)
      · exact ⟨hx, fun hR ↦ hdisj x hx hQ hR⟩
      · exact ⟨hx, hnR⟩
  have hneither :
      S.filter (fun x ↦ ¬ (Q x ∨ R x)) = O := by
    ext x
    simp only [O, Finset.mem_filter]
    tauto
  have hSprod :
      (∏ x ∈ S, a x) =
        (∏ x ∈ A, a x) * ((∏ x ∈ B, a x) * ∏ x ∈ O, a x) := by
    rw [← Finset.prod_union hBO, ← Finset.prod_union hA_BO]
    rw [hpartition]
  have hnotQprod :
      (∏ x ∈ S with ¬ Q x, a x) =
        (∏ x ∈ B, a x) * ∏ x ∈ O, a x := by
    rw [hnotQ, Finset.prod_union hBO]
  have hnotRprod :
      (∏ x ∈ S with ¬ R x, a x) =
        (∏ x ∈ A, a x) * ∏ x ∈ O, a x := by
    rw [hnotR, Finset.prod_union hAO]
  have hneitherprod :
      (∏ x ∈ S with ¬ (Q x ∨ R x), a x) = ∏ x ∈ O, a x := by
    rw [hneither]
  rw [hSprod, hnotQprod, hnotRprod, hneitherprod]
  change _ = (∏ x ∈ O, a x) * ((∏ x ∈ A, a x) - 1) *
    ((∏ x ∈ B, a x) - 1)
  ring

/-- Exact A.11 factorization for the two complementary predicates used by
`finiteHalaszTypicalCoefficient`. -/
theorem twoBlock_alternatingLow_LSeries_eq_EulerFactors
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (gsA9Low f y) s -
          LSeries (gsA9LowDeletion f (fun p ↦ ¬ P₁ p ∧ P₂ p) y) s -
          LSeries (gsA9LowDeletion f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) y) s +
          LSeries (gsA9LowDeletion f
            (fun p ↦ (¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p)) y) s =
      (∏ p ∈ primesUpTo y with
          ¬ (¬ P₁ p ∧ P₂ p) ∧ ¬ (¬ P₁ p ∧ ¬ P₂ p),
            gsA9LocalEulerFactor f s p) *
        ((∏ p ∈ primesUpTo y with ¬ P₁ p ∧ P₂ p,
            gsA9LocalEulerFactor f s p) - 1) *
        ((∏ p ∈ primesUpTo y with ¬ P₁ p ∧ ¬ P₂ p,
            gsA9LocalEulerFactor f s p) - 1) := by
  rw [LSeries_gsA9Low_eq_finiteEulerProduct hmul hbound y hs,
    LSeries_gsA9LowDeletion_eq_finiteEulerProduct hmul hbound
      (fun p ↦ ¬ P₁ p ∧ P₂ p) y hs,
    LSeries_gsA9LowDeletion_eq_finiteEulerProduct hmul hbound
      (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) y hs,
    LSeries_gsA9LowDeletion_eq_finiteEulerProduct hmul hbound
      (fun p ↦ (¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p)) y hs]
  exact alternating_filtered_products_eq (primesUpTo y)
    (fun p ↦ ¬ P₁ p ∧ P₂ p) (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)
    (fun _ _ h₂ h₃ ↦ h₃.2 h₂.2)
    (gsA9LocalEulerFactor f s)

end

end Erdos67.MRHalaszBands
