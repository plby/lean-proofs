import ErdosProblems.Erdos67b.MRSelectedPaidSampleEnergy
import ErdosProblems.Erdos67b.MRSelectedPaidErrorScale

/-! # Uniform small sampled energy of the actual selected products -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrExists_selected_paid_sample_energy_small
    {r xi thetaMax : ℝ} (hr : 0 < r) (hrOne : r ≤ 1)
    (hxi : 0 < xi) (hthetaMax : 0 < thetaMax) :
    ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧
      ∀ B : ℝ, 0 ≤ B → ∀ k : ℕ, ∃ M₀ X₀ : ℕ,
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
      ∀ S : Finset ℝ,
        (∀ u ∈ S, ∀ t ∈ S, u ≠ t → 1 ≤ |u - t|) →
        (∀ t ∈ S, |t| ≤ (X : ℝ) / 2) →
        (S.card : ℝ) ≤ B * (Real.log (X : ℝ)) ^ k →
        (Real.log (X : ℝ)) ^ 2 * (∑ t ∈ S, ‖logarithmicDirichletPolynomial (mrPrimeSubblock H A s)
            (mrFinitePrimeLineCoefficient f) t *
          logarithmicDirichletPolynomial
            (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I
              (mrNarrowPrimeInterval H s) X) (mrFiniteCofactorLineCoefficient A f) t‖ ^ 2) ≤
          xi := by
  let E := xi * r ^ 2 / (160000 * mrPrimeBlockMassConstant)
  have hmass := mrPrimeBlockMassConstant_pos
  have hE : 0 < E := by dsimp [E]; positivity
  obtain ⟨theta, htheta, hthetaMax', M₀, X₁, hM₀, hX₁, hsample⟩ :=
    mrExists_selected_paid_sample_energy hr hrOne hE hthetaMax
  refine ⟨theta, htheta, hthetaMax', ?_⟩
  intro B hB k
  obtain ⟨X₂, hX₂two, hX₂⟩ :=
    mrExists_selectedPaid_budget_polylog_threshold hr htheta hE.le hB (half_pos hxi) k
  refine ⟨M₀, max X₁ X₂, hM₀, hX₁.trans (le_max_left _ _), ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hsourceBudget hmertens J hupper
    I A hA hlower hAupper H hH s f hmul hbound hnonpret S hsep hwindow hcount
  have hh := hsample hM ((le_max_left _ _).trans hX) heta hp hq hpq hlogq hsourceBudget
    hmertens J hupper I A hA hlower hAupper hH s hmul hbound hnonpret S hsep hwindow
  have hscaled := mul_le_mul_of_nonneg_left hh (sq_nonneg (Real.log (X : ℝ)))
  have hbudget := hX₂ X ((le_max_right _ _).trans hX) S.card hcount
  apply (hscaled.trans hbudget).trans
  apply le_of_eq
  dsimp [E]
  field_simp
  ring

end

end Erdos67b
