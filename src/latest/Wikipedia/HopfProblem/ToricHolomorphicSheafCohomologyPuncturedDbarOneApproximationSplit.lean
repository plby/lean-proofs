import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneDomains
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneApproximationContours

/-!
# Actual local Laurent splitting into two bidisc functions

The two actual boundary circles split data near a closed disc–annulus
region into functions holomorphic on a finite bidisc in the ordinary and
reciprocal coordinates. Only that original local analytic domain is used.
-/

noncomputable section

open Complex Set Metric

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne

open HolomorphicCousin Laurent

theorem inverse_radius_lt {R : ℝ} (hR : 1 < R) : R⁻¹ < R := by
  have hp : 0 < R := zero_lt_one.trans hR
  have hi : R⁻¹ < 1 := by
    simpa only [inv_one] using (inv_lt_inv₀ hp zero_lt_one).mpr hR
  exact hi.trans hR

theorem outerCircle_subset_annularClosed {R : ℝ} (hR : 1 < R) :
    closedBall (0 : ℂ) R ×ˢ sphere 0 R ⊆ annularClosed R := by
  intro q hq
  have hn : ‖q.2‖ = R := by simpa only [mem_sphere, dist_zero_right] using hq.2
  refine ⟨hq.1, sphere_subset_closedBall hq.2, ?_⟩
  simpa only [mem_ball, dist_zero_right, hn, not_lt] using (inverse_radius_lt hR).le

theorem innerCircle_subset_annularClosed {R : ℝ} (hR : 1 < R) :
    closedBall (0 : ℂ) R ×ˢ sphere 0 R⁻¹ ⊆ annularClosed R := by
  intro q hq
  have hn : ‖q.2‖ = R⁻¹ := by simpa only [mem_sphere, dist_zero_right] using hq.2
  refine ⟨hq.1, ?_, ?_⟩
  · simpa only [mem_closedBall, dist_zero_right, hn] using (inverse_radius_lt hR).le
  · simp only [mem_ball, dist_zero_right, hn, lt_self_iff_false, not_false_eq_true]

theorem exists_local_annular_splitting {f : ℂ × ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : AnalyticOnNhd ℂ f (annularClosed R)) :
    ∃ p m : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ p (ball 0 R ×ˢ ball 0 R) ∧
      AnalyticOnNhd ℂ m (ball 0 R ×ˢ ball 0 R) ∧
      ∀ q ∈ annularOpen R, p q + m (q.1, q.2⁻¹) = f q := by
  have hp : 0 < R := zero_lt_one.trans hR
  have hi : 0 < R⁻¹ := inv_pos.mpr hp
  refine ⟨positiveContour f R, fun q => -reciprocalContour f R⁻¹ q,
    positiveContour_local_analytic hp hp (hf.mono (outerCircle_subset_annularClosed hR)), ?_, ?_⟩
  · intro q hq
    have hq' : q ∈ ball (0 : ℂ) R ×ˢ ball 0 (R⁻¹)⁻¹ := by
      simpa only [inv_inv] using hq
    exact (reciprocalContour_local_analytic hp hi
      (hf.mono (innerCircle_subset_annularClosed hR)) q hq').neg
  · intro q hq
    have hq0 : q.2 ≠ 0 := norm_pos_iff.mp (hi.trans hq.2.1)
    have hs : AnalyticOnNhd ℂ (fun w => f (q.1, w))
        (closedBall (0 : ℂ) R \ ball 0 R⁻¹) := by
      intro w hw
      exact (hf (q.1, w) ⟨ball_subset_closedBall hq.1, hw⟩).curry_right
    change cauchyTransform (fun w => f (q.1, w)) R q.2 +
      -infinityKernel (fun w => f (q.1, w)) R⁻¹ q.2⁻¹ = f q
    rw [infinityKernel_inv _ _ hq0]
    exact normalized_circleIntegral_sub hi (inverse_radius_lt hR) hs hq.2

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne
