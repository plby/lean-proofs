import ErdosProblems.Erdos67b.MRCofactorSelectedScheduledRectangle
import ErdosProblems.Erdos67b.MRSelectedShiftedParameters

/-! # Payment of the actual cofactor rectangle's prime-cutoff cost -/

namespace Erdos67b

noncomputable section

theorem mrExists_selected_cutoff_paid_rectangle
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
      ∀ {P Q : ℕ}, 4 ≤ P → P ≤ Q → Q ≤ 2 * P →
        (Q : ℝ) ≤ Real.exp (theta * Real.log (X : ℝ) + 1) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| ≤ (X : ℝ) / 2 →
        (mrPrimeSieveExponent (mrSelectedPowerOrder r theta))⁻¹ * theta⁻¹ ^ 2 *
          ‖logarithmicDirichletPolynomial
            (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I (P, Q) X)
            (mrFiniteCofactorLineCoefficient A f) (-t)‖ ^ 2 ≤ E := by
  let C := 9 * mrSelectedPrimeShiftedRatioCost r (mrSelectedPowerShift r)
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos (by norm_num) (mrSelectedPrimeShiftedRatioCost_pos _ _)
  obtain ⟨tau, htau, theta, htheta, hthetaMax', _, hproduct, epsilon, hepsilon, hbudget⟩ :=
    mrExists_selected_shifted_cutoff_budget hr (sq_nonneg C) hE hthetaMax
  obtain ⟨M₀, X₀, hM₀, hX₀, hrectangle⟩ :=
    mrExists_selected_scheduled_cofactor_rectangle_shifted hr hrOne
      (mrSelectedPowerShift_pos hr).le htau htheta (by linarith) hepsilon
  refine ⟨theta, htheta, hthetaMax', M₀, X₀, hM₀, hX₀, ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hsourceBudget hmertens J hupper
    I A hA hlower hAupper P Q hP hPQ hQP hQ f hmul hbound hnonpret t ht
  have hh := hrectangle hM hX heta hp hq hpq hlogq hsourceBudget hmertens J hupper
    I A hA hlower hAupper hP hPQ hQP hQ hmul hbound hnonpret t ht
  have hweight : 0 ≤ (mrPrimeSieveExponent (mrSelectedPowerOrder r theta))⁻¹ * theta⁻¹ ^ 2 := by
    have := mrPrimeSieveExponent_pos (mrSelectedPowerOrder r theta)
    positivity
  calc
    _ ≤ (mrPrimeSieveExponent (mrSelectedPowerOrder r theta))⁻¹ * theta⁻¹ ^ 2 *
        (C * (epsilon + Real.exp (-mrSelectedPowerShift r * tau))) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) hweight
    _ = C ^ 2 * (mrPrimeSieveExponent (mrSelectedPowerOrder r theta))⁻¹ * theta⁻¹ ^ 2 *
        (epsilon + Real.exp (-mrSelectedPowerShift r * tau)) ^ 2 := by ring
    _ ≤ E := hbudget

end

end Erdos67b
