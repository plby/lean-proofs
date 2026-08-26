import ErdosProblems.Erdos67b.MRSelectedLargeSamples
import ErdosProblems.Erdos67b.MRSelectedPaidSampleSmall
import ErdosProblems.Erdos67b.MRExceptionalSmallPrimeEnergy

/-! # The actual large selected-prime exceptional integral -/

open Filter MeasureTheory
open scoped BigOperators Interval

namespace Erdos67b

noncomputable section

theorem mrExists_selected_large_prime_energy_small
    {r xi thetaMax : ℝ} (hr : 0 < r) (hrOne : r ≤ 1)
    (hxi : 0 < xi) (hthetaMax : 0 < thetaMax) :
    ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧ theta ≤ 1 ∧
      ∀ a : ℝ, 0 ≤ a → ∃ M₀ X₀ : ℕ, 0 < M₀ ∧ 1 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∀ {eta p₁ q₁ : ℝ}, eta ≤ 1 / 12 → 2 ≤ p₁ → 1 ≤ q₁ →
        2 * p₁ ≤ q₁ → 1 ≤ Real.log q₁ →
        4096 * Real.log q₁ ≤ eta * p₁ →
        Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁ →
      ∀ J : ℕ, mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) →
      ∀ (I : ℕ × ℕ) (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
        (∀ p ∈ A, r * (theta * Real.log (X : ℝ)) ≤ Real.log (p : ℝ)) →
        (∀ p ∈ A, Real.log (p : ℝ) ≤ theta * Real.log (X : ℝ)) →
      ∀ {H : ℝ}, 2 ≤ H → ∀ s : ℕ,
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ E : Set ℝ, MeasurableSet E →
        (Real.log (X : ℝ)) ^ 2 *
          (∫ t in -((X : ℝ) / 2)..((X : ℝ) / 2),
            (mrLargePrimeFrequencySet E (mrPrimeSubblock H A s) f
              (Real.exp (-a * Real.log (Real.log (X : ℝ))))).indicator
            (fun t ↦ ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A s)
                (mrFinitePrimeLineCoefficient f) t *
              logarithmicDirichletPolynomial
                (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I
                  (mrNarrowPrimeInterval H s) X) (mrFiniteCofactorLineCoefficient A f) t‖ ^ 2) t) ≤
          xi := by
  obtain ⟨theta, htheta, hthetaMax', hsample⟩ :=
    mrExists_selected_paid_sample_energy_small hr hrOne (half_pos hxi)
      (lt_min hthetaMax (by norm_num : (0 : ℝ) < 1))
  have hthetaOne : theta ≤ 1 := hthetaMax'.trans (min_le_right _ _)
  refine ⟨theta, htheta, hthetaMax'.trans (min_le_left _ _), hthetaOne, ?_⟩
  intro a ha
  obtain ⟨M₀, X₁, hM₀, hX₁, hsmall⟩ := hsample mrLargePrimeCountConstant
    mrLargePrimeCountConstant_pos.le (mrSelectedLargeSampleOrder r theta a)
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1 (mrEventually_selected_large_sample_scale hr htheta)
  refine ⟨M₀, max X₁ X₂, hM₀, hX₁.trans (le_max_left _ _), ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hsourceBudget hmertens J hupper
    I A hA hlower hAupper H hH s f hmul hbound hnonpret E hE
  have hscale := hX₂ X ((le_max_right _ _).trans hX)
  have hXone : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  let g : ℝ → ℝ := fun t ↦
    ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A s)
        (mrFinitePrimeLineCoefficient f) t *
      logarithmicDirichletPolynomial
        (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I
          (mrNarrowPrimeInterval H s) X) (mrFiniteCofactorLineCoefficient A f) t‖ ^ 2
  have hg : Continuous g := ((continuous_logarithmicDirichletPolynomial _ _).mul
    (continuous_logarithmicDirichletPolynomial _ _)).norm.pow 2
  obtain ⟨S, hS, hsep, hint⟩ := mrExists_separated_samples_ge_integral
    (measurableSet_mrLargePrimeFrequencySet hE (mrPrimeSubblock H A s) f
      (Real.exp (-a * Real.log (Real.log (X : ℝ))))) hg
    (fun t ↦ sq_nonneg _) (by positivity : 0 ≤ (X : ℝ) / 2)
  have hcount := mrSelectedSubblock_large_values_card_le hr htheta hthetaOne hXone
    hscale.2.1 hscale.2.2.1 ha hH hscale.2.2.2 hA hlower hAupper s hbound S
    (fun t ht ↦ (hS t ht).2) hsep (fun t ht ↦ (hS t ht).1.2.le)
  have henergy := hsmall hM ((le_max_left _ _).trans hX) heta hp hq hpq hlogq
    hsourceBudget hmertens J hupper I A hA hlower hAupper hH s hmul hbound hnonpret
    S hsep (fun t ht ↦ (hS t ht).2) hcount
  have hscaled := mul_le_mul_of_nonneg_left hint (sq_nonneg (Real.log (X : ℝ)))
  change (Real.log (X : ℝ)) ^ 2 * (∑ t ∈ S, g t) ≤ xi / 2 at henergy
  change (Real.log (X : ℝ)) ^ 2 * _ ≤ xi
  nlinarith

end

end Erdos67b
