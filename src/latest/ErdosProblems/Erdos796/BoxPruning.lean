import ErdosProblems.Erdos796.AdmissibleTriples

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Summing complete-box estimates over a finite partition

The first pruning step partitions chosen triple factorizations into dyadic
boxes.  This module packages the purely finite operation of applying the
complete-box theorem in every box and summing the resulting bounds.
-/

namespace Erdos796

open scoped BigOperators

namespace BoxPruning

open AdmissibleTriples

theorem card_biUnion_le_sum_completeBox
    {ι : Type*} [DecidableEq ι]
    {n : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (I : Finset ι)
    (H : ι → Finset (ℕ × ℕ × ℕ))
    (L M R : ι → Finset ℕ)
    (hinj : ∀ i ∈ I, TripleProductInjective (H i))
    (hproducts : ∀ i ∈ I, TripleProductsIn (H i) A)
    (hsub : ∀ i ∈ I, H i ⊆ L i ×ˢ (M i ×ˢ R i))
    (hL : ∀ i ∈ I, 0 < (L i).card)
    (hM : ∀ i ∈ I, 0 < (M i).card)
    (hR : ∀ i ∈ I, 0 < (R i).card) :
    (((I.biUnion H).card : ℕ) : ℝ) ≤
      ∑ i ∈ I,
        (4 * ((L i).card : ℝ) * ((M i).card : ℝ) * ((R i).card : ℝ)) /
          Tripartite.realFourthRoot
            (Nat.min (L i).card (Nat.min (M i).card (R i).card) : ℝ) := by
  have hunionNat : (I.biUnion H).card ≤ ∑ i ∈ I, (H i).card :=
    Finset.card_biUnion_le
  have hunionReal : ((I.biUnion H).card : ℝ) ≤
      ∑ i ∈ I, ((H i).card : ℝ) := by
    exact_mod_cast hunionNat
  calc
    ((I.biUnion H).card : ℝ) ≤ ∑ i ∈ I, ((H i).card : ℝ) := hunionReal
    _ ≤ ∑ i ∈ I,
        (4 * ((L i).card : ℝ) * ((M i).card : ℝ) * ((R i).card : ℝ)) /
          Tripartite.realFourthRoot
            (Nat.min (L i).card (Nat.min (M i).card (R i).card) : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact card_le_completeBox hA (hinj i hi) (hproducts i hi)
        (L i) (M i) (R i) (hsub i hi) (hL i hi) (hM i hi) (hR i hi)

/-- A uniform per-box estimate gives the expected number-of-boxes factor. -/
theorem card_biUnion_le_card_mul_of_uniform
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (H : ι → Finset α) (C : ℝ)
    (hC : ∀ i ∈ I, ((H i).card : ℝ) ≤ C) :
    ((I.biUnion H).card : ℝ) ≤ (I.card : ℝ) * C := by
  have hunionNat : (I.biUnion H).card ≤ ∑ i ∈ I, (H i).card :=
    Finset.card_biUnion_le
  have hunionReal : ((I.biUnion H).card : ℝ) ≤
      ∑ i ∈ I, ((H i).card : ℝ) := by
    exact_mod_cast hunionNat
  calc
    ((I.biUnion H).card : ℝ) ≤ ∑ i ∈ I, ((H i).card : ℝ) := hunionReal
    _ ≤ ∑ _i ∈ I, C := by
      apply Finset.sum_le_sum
      intro i hi
      exact hC i hi
    _ = (I.card : ℝ) * C := by simp

end BoxPruning

end Erdos796
