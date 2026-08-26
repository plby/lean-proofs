import ErdosProblems.Erdos67b.MRCofactorAmbientPrefixes

/-!
# Uniform smallness of the finite dyadic cofactor polynomial

An ambient nonpretentiousness threshold is transferred to every cofactor
prefix in the dyadic interval. The exact coefficient identity and finite
Abel transform then give the polynomial estimate, without an L-series tail.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrExists_uniform_small_dyadic_cofactor_polynomial
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ M₀ Y₀ : ℕ, 0 < M₀ ∧ 2 ≤ Y₀ ∧
      ∀ {M X Y : ℕ}, M₀ ≤ M → Y₀ ≤ Y → 2 * Y ≤ X →
        Real.log (X : ℝ) ≤ 2 * Real.log (Y : ℝ) →
      ∀ (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
      ∀ (J : Finset ℕ) (B : ℕ → Finset ℕ),
        (∀ j ∈ J, 1 ≤ j) → (∀ j ∈ J, B j ⊆ primesUpTo Y) →
        Set.PairwiseDisjoint (↑J : Set ℕ) B →
        (∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (Y : ℝ) / 16) →
        (∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ)) →
        (∀ p ∈ A, p ≤ mrCofactorPowerCutoff delta Y) →
        (∀ j ∈ J, ∀ p ∈ B j, p ≤ mrCofactorPowerCutoff delta Y) →
        (∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| + (2 * Y : ℕ) ≤ X →
        ‖dyadicVerticalDirichletPolynomial (Finset.Ioc Y (2 * Y))
          (mrIndexedTypicalCofactorCoefficient A J B f) Y t‖ ≤ epsilon := by
  obtain ⟨delta, hdelta, hdeltaOne, M₀, Y₀, hM₀, hY₀, hprefix⟩ :=
    mrExists_uniform_small_ambient_cofactor_prefixes (show 0 < epsilon / 3 by positivity)
  refine ⟨delta, hdelta, hdeltaOne, M₀, Y₀, hM₀, hY₀, ?_⟩
  intro M X Y hM hY hYX hlogXY A hA J B hJ hB hdisj hsmall hmass hAy hBy hlarge
    f hmul hbound hnonpret t hwindow
  have hYpos : 0 < Y := by have := hY₀.trans hY; omega
  have hp := hprefix hM hY (show Y ≤ 2 * Y by omega) hYX hlogXY
    A hA J B hJ hB hdisj hsmall hmass hAy hBy hlarge hmul hbound hnonpret t hwindow
  have hpoly := mrNorm_cofactor_dyadicPolynomial_le_of_untwisted_prefixes
    A J B f hYpos t (show 0 ≤ epsilon / 3 by positivity) hp
  linarith

end

end Erdos67b
