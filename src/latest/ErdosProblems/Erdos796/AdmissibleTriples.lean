import ErdosProblems.Erdos796.CompleteBoxBound
import ErdosProblems.Erdos796.PairwiseOverlap

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Admissibility excludes complete tripartite boxes

This module supplies the bridge used in the structural argument: an
injectively parametrized set of triple products lying in an admissible set
cannot contain a nondegenerate `2 × 2 × 2` box.  The four complementary
pairs of cube vertices give four genuinely distinct strict product
representations of one integer.
-/

namespace Erdos796

namespace AdmissibleTriples

/-- Product of the three coordinates of a tripartite parameter. -/
def tripleProduct (p : ℕ × ℕ × ℕ) : ℕ :=
  p.1 * p.2.1 * p.2.2

/-- The triple-product parametrization is injective on `H`. -/
def TripleProductInjective (H : Finset (ℕ × ℕ × ℕ)) : Prop :=
  Set.InjOn tripleProduct (H : Set (ℕ × ℕ × ℕ))

/-- Every displayed triple product belongs to `A`. -/
def TripleProductsIn (H : Finset (ℕ × ℕ × ℕ))
    (A : Finset ℕ) : Prop :=
  ∀ p ∈ H, tripleProduct p ∈ A

/-- Zero coordinates cannot occur: this follows from membership in the
positive ambient interval of an admissible set. -/
theorem coordinates_pos_of_mem
    {n : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    {H : Finset (ℕ × ℕ × ℕ)} (hproducts : TripleProductsIn H A)
    {p : ℕ × ℕ × ℕ} (hp : p ∈ H) :
    0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 := by
  have hmem := hproducts p hp
  have hpos : 0 < tripleProduct p :=
    (mem_positiveIcc.mp (hA.1 hmem)).1
  have hpair : 0 < p.1 * p.2.1 :=
    pos_of_mul_pos_left hpos (Nat.zero_le _)
  exact ⟨pos_of_mul_pos_left hpair (Nat.zero_le _),
    pos_of_mul_pos_right hpair (Nat.zero_le _),
    pos_of_mul_pos_right hpos (Nat.zero_le _)⟩

/-- Injectivity turns distinct cube vertices into distinct elements of the
admissible set. -/
theorem tripleProduct_ne_of_ne
    {H : Finset (ℕ × ℕ × ℕ)}
    (hinj : TripleProductInjective H)
    {p q : ℕ × ℕ × ℕ} (hp : p ∈ H) (hq : q ∈ H)
    (hpq : p ≠ q) : tripleProduct p ≠ tripleProduct q := by
  intro heq
  exact hpq (hinj hp hq heq)

/-- A nondegenerate cube yields four distinct strict representations of the
product of all six coordinate labels. -/
theorem four_le_count_of_cube
    {A : Finset ℕ} {H : Finset (ℕ × ℕ × ℕ)}
    (hinj : TripleProductInjective H) (hproducts : TripleProductsIn H A)
    {x₁ x₂ y₁ y₂ z₁ z₂ : ℕ}
    (h₁₁₁ : (x₁, y₁, z₁) ∈ H)
    (h₁₁₂ : (x₁, y₁, z₂) ∈ H)
    (h₁₂₁ : (x₁, y₂, z₁) ∈ H)
    (h₁₂₂ : (x₁, y₂, z₂) ∈ H)
    (h₂₁₁ : (x₂, y₁, z₁) ∈ H)
    (h₂₁₂ : (x₂, y₁, z₂) ∈ H)
    (h₂₂₁ : (x₂, y₂, z₁) ∈ H)
    (h₂₂₂ : (x₂, y₂, z₂) ∈ H)
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂) (hz : z₁ ≠ z₂) :
    4 ≤ strictProductRepCount A (x₁ * x₂ * y₁ * y₂ * z₁ * z₂) := by
  let a₁ := tripleProduct (x₁, y₁, z₁)
  let b₁ := tripleProduct (x₂, y₂, z₂)
  let a₂ := tripleProduct (x₁, y₁, z₂)
  let b₂ := tripleProduct (x₂, y₂, z₁)
  let a₃ := tripleProduct (x₁, y₂, z₁)
  let b₃ := tripleProduct (x₂, y₁, z₂)
  let a₄ := tripleProduct (x₁, y₂, z₂)
  let b₄ := tripleProduct (x₂, y₁, z₁)
  let r₁ := PairwiseOverlap.strictOrder a₁ b₁
  let r₂ := PairwiseOverlap.strictOrder a₂ b₂
  let r₃ := PairwiseOverlap.strictOrder a₃ b₃
  let r₄ := PairwiseOverlap.strictOrder a₄ b₄
  have ha₁ : a₁ ∈ A := hproducts _ h₁₁₁
  have hb₁ : b₁ ∈ A := hproducts _ h₂₂₂
  have ha₂ : a₂ ∈ A := hproducts _ h₁₁₂
  have hb₂ : b₂ ∈ A := hproducts _ h₂₂₁
  have ha₃ : a₃ ∈ A := hproducts _ h₁₂₁
  have hb₃ : b₃ ∈ A := hproducts _ h₂₁₂
  have ha₄ : a₄ ∈ A := hproducts _ h₁₂₂
  have hb₄ : b₄ ∈ A := hproducts _ h₂₁₁
  have hne₁ : a₁ ≠ b₁ := tripleProduct_ne_of_ne hinj h₁₁₁ h₂₂₂ (by
    simp [hx])
  have hne₂ : a₂ ≠ b₂ := tripleProduct_ne_of_ne hinj h₁₁₂ h₂₂₁ (by
    simp [hx])
  have hne₃ : a₃ ≠ b₃ := tripleProduct_ne_of_ne hinj h₁₂₁ h₂₁₂ (by
    simp [hx])
  have hne₄ : a₄ ≠ b₄ := tripleProduct_ne_of_ne hinj h₁₂₂ h₂₁₁ (by
    simp [hx])
  have hr₁ : r₁.1 ∈ A ∧ r₁.2 ∈ A ∧ r₁.1 < r₁.2 ∧
      r₁.1 * r₁.2 = x₁ * x₂ * y₁ * y₂ * z₁ * z₂ := by
    refine ⟨(PairwiseOverlap.strictOrder_members ha₁ hb₁).1,
      (PairwiseOverlap.strictOrder_members ha₁ hb₁).2,
      PairwiseOverlap.strictOrder_fst_lt_snd hne₁, ?_⟩
    rw [PairwiseOverlap.strictOrder_product]
    simp only [a₁, b₁, tripleProduct]
    ring
  have hr₂ : r₂.1 ∈ A ∧ r₂.2 ∈ A ∧ r₂.1 < r₂.2 ∧
      r₂.1 * r₂.2 = x₁ * x₂ * y₁ * y₂ * z₁ * z₂ := by
    refine ⟨(PairwiseOverlap.strictOrder_members ha₂ hb₂).1,
      (PairwiseOverlap.strictOrder_members ha₂ hb₂).2,
      PairwiseOverlap.strictOrder_fst_lt_snd hne₂, ?_⟩
    rw [PairwiseOverlap.strictOrder_product]
    simp only [a₂, b₂, tripleProduct]
    ring
  have hr₃ : r₃.1 ∈ A ∧ r₃.2 ∈ A ∧ r₃.1 < r₃.2 ∧
      r₃.1 * r₃.2 = x₁ * x₂ * y₁ * y₂ * z₁ * z₂ := by
    refine ⟨(PairwiseOverlap.strictOrder_members ha₃ hb₃).1,
      (PairwiseOverlap.strictOrder_members ha₃ hb₃).2,
      PairwiseOverlap.strictOrder_fst_lt_snd hne₃, ?_⟩
    rw [PairwiseOverlap.strictOrder_product]
    simp only [a₃, b₃, tripleProduct]
    ring
  have hr₄ : r₄.1 ∈ A ∧ r₄.2 ∈ A ∧ r₄.1 < r₄.2 ∧
      r₄.1 * r₄.2 = x₁ * x₂ * y₁ * y₂ * z₁ * z₂ := by
    refine ⟨(PairwiseOverlap.strictOrder_members ha₄ hb₄).1,
      (PairwiseOverlap.strictOrder_members ha₄ hb₄).2,
      PairwiseOverlap.strictOrder_fst_lt_snd hne₄, ?_⟩
    rw [PairwiseOverlap.strictOrder_product]
    simp only [a₄, b₄, tripleProduct]
    ring
  have hval {p q : ℕ × ℕ × ℕ} (hp : p ∈ H) (hq : q ∈ H)
      (hpq : p ≠ q) : tripleProduct p ≠ tripleProduct q :=
    tripleProduct_ne_of_ne hinj hp hq hpq
  have hr₁₂ : r₁ ≠ r₂ := PairwiseOverlap.strictOrder_ne_of_cross_ne
    (hval h₁₁₁ h₁₁₂ (by simp [hz]))
    (hval h₁₁₁ h₂₂₁ (by simp [hx, hy]))
  have hr₁₃ : r₁ ≠ r₃ := PairwiseOverlap.strictOrder_ne_of_cross_ne
    (hval h₁₁₁ h₁₂₁ (by simp [hy]))
    (hval h₁₁₁ h₂₁₂ (by simp [hx, hz]))
  have hr₁₄ : r₁ ≠ r₄ := PairwiseOverlap.strictOrder_ne_of_cross_ne
    (hval h₁₁₁ h₁₂₂ (by simp [hy, hz]))
    (hval h₁₁₁ h₂₁₁ (by simp [hx]))
  have hr₂₃ : r₂ ≠ r₃ := PairwiseOverlap.strictOrder_ne_of_cross_ne
    (hval h₁₁₂ h₁₂₁ (by simp [hy]))
    (hval h₁₁₂ h₂₁₂ (by simp [hx]))
  have hr₂₄ : r₂ ≠ r₄ := PairwiseOverlap.strictOrder_ne_of_cross_ne
    (hval h₁₁₂ h₁₂₂ (by simp [hy]))
    (hval h₁₁₂ h₂₁₁ (by simp [hx]))
  have hr₃₄ : r₃ ≠ r₄ := PairwiseOverlap.strictOrder_ne_of_cross_ne
    (hval h₁₂₁ h₁₂₂ (by simp [hz]))
    (hval h₁₂₁ h₂₁₁ (by simp [hx]))
  exact PairwiseOverlap.four_strict_solutions_le_count
    hr₁ hr₂ hr₃ hr₄ hr₁₂ hr₁₃ hr₁₄ hr₂₃ hr₂₄ hr₃₄

/-- An injective triple-product hypergraph supported in an admissible set is
free of nondegenerate `2 × 2 × 2` boxes. -/
theorem k222Free_of_admissible
    {n : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    {H : Finset (ℕ × ℕ × ℕ)}
    (hinj : TripleProductInjective H) (hproducts : TripleProductsIn H A) :
    Tripartite.K222Free H := by
  intro x₁ x₂ y₁ y₂ z₁ z₂ h₁₁₁ h₁₁₂ h₁₂₁ h₁₂₂
    h₂₁₁ h₂₁₂ h₂₂₁ h₂₂₂
  by_cases hx : x₁ = x₂
  · exact Or.inl hx
  by_cases hy : y₁ = y₂
  · exact Or.inr (Or.inl hy)
  by_cases hz : z₁ = z₂
  · exact Or.inr (Or.inr hz)
  exfalso
  have hlower := four_le_count_of_cube hinj hproducts
    h₁₁₁ h₁₁₂ h₁₂₁ h₁₂₂
    h₂₁₁ h₂₁₂ h₂₂₁ h₂₂₂ hx hy hz
  have hupper := hA.2 (x₁ * x₂ * y₁ * y₂ * z₁ * z₂)
  omega

/-- Complete-box cardinality bound for an injective triple-product family
inside an admissible set. -/
theorem card_le_completeBox
    {n : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    {H : Finset (ℕ × ℕ × ℕ)}
    (hinj : TripleProductInjective H) (hproducts : TripleProductsIn H A)
    (L M R : Finset ℕ) (hsub : H ⊆ L ×ˢ (M ×ˢ R))
    (hL : 0 < L.card) (hM : 0 < M.card) (hR : 0 < R.card) :
    (H.card : ℝ) ≤
      (4 * (L.card : ℝ) * (M.card : ℝ) * (R.card : ℝ)) /
        Tripartite.realFourthRoot
          (Nat.min L.card (Nat.min M.card R.card) : ℝ) :=
  Tripartite.card_le_four_mul_div_fourthRoot_min
    (k222Free_of_admissible hA hinj hproducts) L M R hsub hL hM hR

end AdmissibleTriples

end Erdos796
