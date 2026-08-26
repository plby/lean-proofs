import ErdosProblems.Erdos67b.MRCofactorSelectedCutoffPayment
import ErdosProblems.Erdos67b.MRCofactorSelectedSmallMean

/-! # The paid cutoff estimate on every actual narrow prime-cofactor product -/

open Filter

namespace Erdos67b

noncomputable section

theorem mrExists_selected_cutoff_paid_product
    {r E thetaMax : ℝ} (hr : 0 < r) (hrOne : r ≤ 1)
    (hE : 0 < E) (hthetaMax : 0 < thetaMax) :
    ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧ ∃ M₀ X₀ : ℕ,
      0 < M₀ ∧ 1 ≤ X₀ ∧
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
      ∀ t : ℝ, |t| ≤ (X : ℝ) / 2 →
        (mrPrimeSieveExponent (mrSelectedPowerOrder r theta))⁻¹ * theta⁻¹ ^ 2 *
          ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A s)
              (mrFinitePrimeLineCoefficient f) t *
            logarithmicDirichletPolynomial
              (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I
                (mrNarrowPrimeInterval H s) X) (mrFiniteCofactorLineCoefficient A f) t‖ ^ 2 ≤
          E * ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A s)
            (mrFinitePrimeLineCoefficient f) t‖ ^ 2 := by
  classical
  obtain ⟨theta, htheta, hthetaMax', M₀, X₁, hM₀, hX₁, hrectangle⟩ :=
    mrExists_selected_cutoff_paid_rectangle hr hrOne hE hthetaMax
  have hrt : 0 < r * theta := mul_pos hr htheta
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop (4 / (r * theta))))
  refine ⟨theta, htheta, hthetaMax', M₀, max X₁ X₂, hM₀,
    hX₁.trans (le_max_left _ _), ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hbudget hmertens J hupper
    I A hA hlower hAupper H hH s f hmul hbound hnonpret t ht
  by_cases hempty : mrPrimeSubblock H A s = ∅
  · simp [hempty, logarithmicDirichletPolynomial]
  have hnonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  have ha : 4 ≤ r * (theta * Real.log (X : ℝ)) := by
    have hh := (div_le_iff₀ hrt).1 (hX₂ X ((le_max_right _ _).trans hX))
    nlinarith
  obtain ⟨hsLower, hsUpper⟩ := mrPrimeSubblock_log_parameter_bounds hH hA
    (fun p hpA ↦ ha.trans (hlower p hpA)) hAupper hnonempty
  have hP := mrNarrowPrimeInterval_lower_ge_four hsLower
  have hPQ := mrNarrowPrimeInterval_order_of_nonempty (by linarith : 0 < H) hA hnonempty
  have hQP := mrNarrowPrimeInterval_dyadic_width hH s
  have hQ : ((mrNarrowPrimeInterval H s).2 : ℝ) ≤
      Real.exp (theta * Real.log (X : ℝ) + 1) :=
    (mrNarrowPrimeInterval_upper_le_exp_shift (by linarith : 1 ≤ H) s).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hh := hrectangle hM ((le_max_left _ _).trans hX) heta hp hq hpq hlogq hbudget
    hmertens J hupper I A hA hlower hAupper hP hPQ hQP hQ hmul hbound hnonpret
    (-t) (by simpa only [abs_neg] using ht)
  simp only [neg_neg] at hh
  rw [norm_mul, mul_pow]
  have hmul := mul_le_mul_of_nonneg_right hh
    (sq_nonneg ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A s)
      (mrFinitePrimeLineCoefficient f) t‖)
  nlinarith only [hmul]

end

end Erdos67b
