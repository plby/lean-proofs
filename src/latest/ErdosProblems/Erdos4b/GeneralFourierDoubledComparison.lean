/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierComparison
import ErdosProblems.Erdos4b.GeneralFourierPolynomial

/-!
# Uniform comparison for the actual doubled local polynomial

Both families use the same prime, but may use different logarithmic scales
in their Fourier powers.  The exceptional cost vanishes exactly when the
companion slope is invertible and there are no cross-family collisions.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem doubledFourierExceptionalCount_le_double_card
    {ι : Type*} (s : Finset ι) (edges : Finset (ι × ι)) (companion : Bool)
    (hedges : edges.card ≤ s.card) :
    doubledFourierExceptionalCount s edges companion ≤ (s.disjSum s).card := by
  rw [Finset.card_disjSum]
  cases companion <;> simp only [doubledFourierExceptionalCount,
    Bool.false_eq_true, ↓reduceIte] <;> omega

theorem norm_doubledFourierLocalPolynomial_div_reference_sub_singular_le
    {ι : Type*} (s : Finset ι) (edges : Finset (ι × ι)) (companion : Bool)
    (U V : Sum ι ι → ℂ) {p δ : ℝ} (hp : 2 ≤ p)
    (hcard : 7 * ((s.disjSum s).card : ℝ) ≤ p)
    (hU : ∀ i ∈ s.disjSum s, ‖U i‖ ≤ 1)
    (hV : ∀ i ∈ s.disjSum s, ‖V i‖ ≤ 1)
    (hAe : ∀ i ∈ s, ‖selbergPairPolynomial (U (.inl i)) (V (.inl i)) + 1‖ ≤ δ)
    (hBe : ∀ i ∈ s, ‖selbergPairPolynomial (U (.inr i)) (V (.inr i)) + 1‖ ≤ δ)
    (hedges : ∀ ij ∈ edges, ij.1 ∈ s ∧ ij.2 ∈ s)
    (hedgeCard : edges.card ≤ s.card) :
    ‖doubledFourierLocalPolynomial s edges companion p
        (fun i ↦ selbergPairPolynomial (U (.inl i)) (V (.inl i)))
        (fun i ↦ selbergPairPolynomial (U (.inr i)) (V (.inr i))) /
        (∏ i ∈ s.disjSum s, selbergPairZetaFactor p (U i) (V i)) -
        (1 - (((s.disjSum s).card : ℂ) -
          doubledFourierExceptionalCount s edges companion) / p) /
          (1 - 1 / (p : ℂ)) ^ (s.disjSum s).card‖ ≤
      (12 : ℝ) ^ (s.disjSum s).card *
        ((4 * ((s.disjSum s).card : ℝ) *
            (pairProductErrorConstant (s.disjSum s).card + (s.disjSum s).card) +
            6 * pairProductErrorConstant (s.disjSum s).card) / p ^ 2 +
          ((if companion then 0 else (s.card : ℝ)) + 4 * edges.card) * δ / p) := by
  let A : ι → ℂ := fun i ↦ selbergPairPolynomial (U (.inl i)) (V (.inl i))
  let B : ι → ℂ := fun i ↦ selbergPairPolynomial (U (.inr i)) (V (.inr i))
  let E := doubledFourierExceptionalTerm s edges companion A B
  let D : ℂ := doubledFourierExceptionalCount s edges companion
  have hD : ‖D‖ ≤ ((s.disjSum s).card : ℝ) := by
    dsimp [D]
    simp only [Complex.norm_natCast]
    exact_mod_cast doubledFourierExceptionalCount_le_double_card s edges companion hedgeCard
  have hA : ∀ i ∈ s, ‖A i‖ ≤ 3 := by
    intro i hi
    exact norm_selbergPairPolynomial_le_three
      (hU (.inl i) (by simpa)) (hV (.inl i) (by simpa))
  have herror : ‖E - D‖ ≤
      ((if companion then 0 else (s.card : ℝ)) + 4 * edges.card) * δ :=
    norm_doubledFourierExceptionalTerm_sub_count_le s edges companion A B
      hA hAe hBe hedges
  have hsum : (∑ i ∈ s.disjSum s, selbergPairPolynomial (U i) (V i)) =
      (∑ i ∈ s, A i) + ∑ i ∈ s, B i := by
    rw [Finset.sum_disjSum]
  have hk : doubledFourierLocalPolynomial s edges companion p A B =
      1 + ((∑ i ∈ s.disjSum s, selbergPairPolynomial (U i) (V i)) + E) / p := by
    rw [doubledFourierLocalPolynomial_eq_generic_add_exceptional, hsum]
    dsimp [E]
    ring
  change ‖doubledFourierLocalPolynomial s edges companion p A B / _ - _‖ ≤ _
  rw [hk]
  apply (norm_pairProduct_quotient_sub_singular_le (s.disjSum s) U V hp hcard hU hV
    E D hD).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl (div_le_div_of_nonneg_right herror (by linarith : 0 ≤ p))

end

end Erdos4b
