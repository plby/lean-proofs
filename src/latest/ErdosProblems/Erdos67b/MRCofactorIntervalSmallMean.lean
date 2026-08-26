import ErdosProblems.Erdos67b.MRCofactorAmbientPrefixes
import ErdosProblems.Erdos67b.MRCofactorIntervalAbel

/-! # Uniform smallness of finite cofactor polynomials on bounded-ratio intervals -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrExists_uniform_small_interval_cofactor_polynomial (r : ℕ) (_hr : 1 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ M₀ Y₀ : ℕ, 0 < M₀ ∧ 2 ≤ Y₀ ∧
      ∀ {M X Y U : ℕ}, M₀ ≤ M → Y₀ ≤ Y → Y ≤ U → U ≤ r * Y → U ≤ X →
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
      ∀ t : ℝ, |t| + (U : ℝ) ≤ X →
        ‖logarithmicDirichletPolynomial (Finset.Ioc Y U)
          (fun n ↦ mrIndexedTypicalCofactorCoefficient A J B f n / (n : ℂ)) (-t)‖ ≤ epsilon := by
  have hrpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  obtain ⟨delta, hdelta, hdeltaOne, M₀, Y₀, hM₀, hY₀, hprefix⟩ :=
    mrExists_uniform_small_ambient_cofactor_prefixes (div_pos hepsilon hrpos)
  refine ⟨delta, hdelta, hdeltaOne, M₀, Y₀, hM₀, hY₀, ?_⟩
  intro M X Y U hM hY hYU hratio hUX hlogXY A hA J B hJ hB hdisj hsmall hmass hAy hBy hlarge
    f hmul hbound hnonpret t hwindow
  have hYpos : 0 < Y := by have := hY₀.trans hY; omega
  have hp := hprefix hM hY hYU hUX hlogXY
    A hA J B hJ hB hdisj hsmall hmass hAy hBy hlarge hmul hbound hnonpret t hwindow
  have hpoly := mrNorm_cofactor_intervalPolynomial_le_of_untwistedPrefixes
    A J B f hYpos hYU hratio t (div_nonneg hepsilon.le hrpos.le) hp
  exact hpoly.trans_eq (by field_simp)

end

end Erdos67b
