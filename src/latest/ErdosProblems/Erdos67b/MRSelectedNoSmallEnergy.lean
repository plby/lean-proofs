import ErdosProblems.Erdos67b.MRSelectedLargePrimeEnergy
import ErdosProblems.Erdos67b.MRSelectedSmallPrimeEnergy

/-! # Actual selected-product energy on the no-small-original-block class -/

open Filter MeasureTheory
open scoped BigOperators Interval

namespace Erdos67b

noncomputable section

theorem mrExists_selected_noSmall_product_energy_small
    {eta p₁ q₁ r xi thetaMax : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : 2 * p₁ ≤ q₁)
    (hlogq : 1 ≤ Real.log q₁) (hsourceBudget : 4096 * Real.log q₁ ≤ eta * p₁)
    (hmertens : Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁)
    (hr : 0 < r) (hrOne : r ≤ 1) (hxi : 0 < xi) (hthetaMax : 0 < thetaMax) :
    ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧ theta ≤ eta / 8 ∧
      ∃ M₀ X₀ : ℕ, 0 < M₀ ∧ 2 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∃ J : ℕ, 1 ≤ J ∧ mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) ∧
        Real.sqrt (Real.log (X : ℝ)) < mrLogScheduleUpper q₁ (J + 1) ∧
      ∀ I : ℕ × ℕ,
        (∀ p ∈ primesInBlock I, r * (theta * Real.log (X : ℝ)) ≤ Real.log (p : ℝ)) →
        (∀ p ∈ primesInBlock I, Real.log (p : ℝ) ≤ theta * Real.log (X : ℝ)) →
      ∀ {H : ℝ}, 2 ≤ H → ∀ s : ℕ,
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
        (Real.log (X : ℝ)) ^ 2 *
          (∫ t in -((X : ℝ) / 2)..((X : ℝ) / 2),
            (mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J).indicator
            (fun t ↦ ‖logarithmicDirichletPolynomial (mrPrimeSubblock H (primesInBlock I) s)
                (mrFinitePrimeLineCoefficient f) t *
              logarithmicDirichletPolynomial
                (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I
                  (mrNarrowPrimeInterval H s) X)
                (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t‖ ^ 2) t) ≤ xi := by
  obtain ⟨theta, htheta, hthetaMax', _, hlarge⟩ :=
    mrExists_selected_large_prime_energy_small hr hrOne (half_pos hxi)
      (lt_min hthetaMax (by positivity : 0 < eta / 8))
  have hthetaEta : theta ≤ eta / 8 := hthetaMax'.trans (min_le_right _ _)
  obtain ⟨M₀, X₁, hM₀, _, hlarge⟩ := hlarge 4 (by norm_num)
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually
      (eventually_ge_atTop (max (mrExceptionalLogScaleThreshold eta q₁)
        (4 * mrSmallPrimeLogConstant / xi))))
  refine ⟨theta, htheta, hthetaMax'.trans (min_le_left _ _), hthetaEta,
    M₀, max X₁ (max X₂ 2), hM₀, (le_max_right _ _).trans (le_max_right _ _), ?_⟩
  intro M X hM hX
  have hXtwo : 2 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hlogs := hX₂ X (((le_max_left _ _).trans (le_max_right _ _)).trans hX)
  have hscale := (le_max_left _ _).trans hlogs
  have hpaid := (le_max_right _ _).trans hlogs
  obtain ⟨_, hqScale, _⟩ := mrExceptionalLogScaleThreshold_spec heta0 hq hscale
  obtain ⟨J, hJ, hupper, hnext⟩ := mrLogSchedule_exists_last_block hq hqScale
  refine ⟨J, hJ, hupper, hnext, ?_⟩
  intro I hlower hIupper H hH s f hmul hbound hnonpret
  let E := mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J
  let g : ℝ → ℝ := fun t ↦
    ‖logarithmicDirichletPolynomial (mrPrimeSubblock H (primesInBlock I) s)
        (mrFinitePrimeLineCoefficient f) t *
      logarithmicDirichletPolynomial
        (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I
          (mrNarrowPrimeInterval H s) X)
        (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t‖ ^ 2
  have hE : MeasurableSet E := measurableSet_mrArithmeticNoSmall eta p₁ q₁ f J
  have hg : Continuous g := ((continuous_logarithmicDirichletPolynomial _ _).mul
    (continuous_logarithmicDirichletPolynomial _ _)).norm.pow 2
  have hlarge' := hlarge hM ((le_max_left _ _).trans hX) heta1 hp hq hpq hlogq
    hsourceBudget hmertens J hupper I (primesInBlock I)
    (fun p hp ↦ (mem_primesInBlock.mp hp).1) hlower hIupper hH s hmul hbound hnonpret E hE
  have hsmall := mrSelected_noSmall_smallPrime_integral_small heta0 heta1 hp hq
    (by linarith : p₁ ≤ q₁) hlogq hsourceBudget hthetaEta hxi hXtwo hJ hscale hpaid
    hupper hnext.le I hIupper hH s hbound
  have hsplit := mrPrimeThreshold_integral_split hE (mrPrimeSubblock H (primesInBlock I) s)
    f (Real.exp (-4 * Real.log (Real.log (X : ℝ)))) hg (-((X : ℝ) / 2)) ((X : ℝ) / 2)
  change (Real.log (X : ℝ)) ^ 2 * (∫ t in -((X : ℝ) / 2)..((X : ℝ) / 2), E.indicator g t) ≤ xi
  rw [hsplit, mul_add]
  exact (add_le_add hsmall hlarge').trans (by linarith)

end

end Erdos67b
