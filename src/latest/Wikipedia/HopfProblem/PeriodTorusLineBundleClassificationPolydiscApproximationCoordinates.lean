import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximationError
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticCoordinates

/-! # Entire polynomial approximation on the original covering space -/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximation

open PeriodTorusLineBundleClassificationPolydiscAnalytic

/-- The original supremum-norm closed ball is exactly the closed bidisc
in the two actual coordinate projections. -/
theorem mem_closedBall_complexPlane₂_iff (z : ComplexPlane₂) (R : ℝ) :
    z ∈ closedBall 0 R ↔ ‖z 0‖ ≤ R ∧ ‖z 1‖ ≤ R := by
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonempty]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h₀, h₁⟩ i
    fin_cases i
    · exact h₀
    · exact h₁

theorem complexPairEquiv_mem_closedBidisc_iff (z : ComplexPlane₂) (R : ℝ) :
    complexPairEquiv z ∈ closedBall (0 : ℂ) R ×ˢ closedBall 0 R ↔
      z ∈ closedBall 0 R := by
  change (dist (z 0) 0 ≤ R ∧ dist (z 1) 0 ≤ R) ↔ _
  simp only [dist_zero_right]
  exact (mem_closedBall_complexPlane₂_iff z R).symm

theorem complexPairEquiv_symm_mem_closedBall_iff (z : ℂ × ℂ) (R : ℝ) :
    complexPairEquiv.symm z ∈ closedBall 0 R ↔
      z ∈ closedBall (0 : ℂ) R ×ˢ closedBall 0 R := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (complexPairEquiv_mem_closedBidisc_iff (complexPairEquiv.symm z) R).symm

/-- Entire finite coordinate polynomials approximate every function
analytic near a closed ball of the actual `ComplexPlane₂`, uniformly on
every strictly smaller closed ball. -/
theorem exists_entire_polynomial_approximation_complexPlane₂
    {f : ComplexPlane₂ → ℂ} {r R ε : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hε : 0 < ε)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    ∃ (N : ℕ) (a : ℕ → ℕ → ℂ) (P : ComplexPlane₂ → ℂ),
      (∀ z, P z = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, a i j * (z 0) ^ i * (z 1) ^ j) ∧
      ContDiff ℂ ω P ∧ ∀ z ∈ closedBall (0 : ComplexPlane₂) r, ‖P z - f z‖ < ε := by
  have hfp : AnalyticOnNhd ℂ (f ∘ complexPairEquiv.symm)
      (closedBall 0 R ×ˢ closedBall 0 R) := by
    intro z hz
    exact (hf (complexPairEquiv.symm z)
      ((complexPairEquiv_symm_mem_closedBall_iff z R).mpr hz)).comp
        (complexPairEquiv.symm.toContinuousLinearMap.analyticAt z)
  obtain ⟨N, a, P, hP, hPa, hPe⟩ := exists_entire_polynomial_approximation hr hrR hε hfp
  refine ⟨N, a, P ∘ complexPairEquiv, ?_,
    hPa.comp complexPairEquiv.toContinuousLinearMap.contDiff, ?_⟩
  · intro z
    exact hP (complexPairEquiv z)
  · intro z hz
    have h := hPe (complexPairEquiv z) ((complexPairEquiv_mem_closedBidisc_iff z r).mpr hz)
    simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using h

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximation
