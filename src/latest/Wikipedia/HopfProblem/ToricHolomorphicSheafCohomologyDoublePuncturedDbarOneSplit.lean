import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOneContours
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneApproximationSplit

/-!
# Actual Laurent splitting from a double annulus to disc–annulus pieces

The first-coordinate positive and negative Cauchy contours are jointly
analytic on a disc times the second annulus, including when the first
ordinary or reciprocal coordinate is zero.
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne

open HolomorphicCousin Laurent

theorem outerCircle_subset_closedAnnulus {R : ℝ} (hR : 1 < R) :
    sphere (0 : ℂ) R ⊆ closedAnnulus R := by
  intro z hz
  have hn : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
  refine ⟨sphere_subset_closedBall hz, ?_⟩
  simpa only [mem_ball, dist_zero_right, hn, not_lt] using
    (PuncturedDbarOne.inverse_radius_lt hR).le

theorem innerCircle_subset_closedAnnulus {R : ℝ} (hR : 1 < R) :
    sphere (0 : ℂ) R⁻¹ ⊆ closedAnnulus R := by
  intro z hz
  have hn : ‖z‖ = R⁻¹ := by simpa only [mem_sphere, dist_zero_right] using hz
  refine ⟨?_, ?_⟩
  · simpa only [mem_closedBall, dist_zero_right, hn] using
      (PuncturedDbarOne.inverse_radius_lt hR).le
  · simp only [mem_ball, dist_zero_right, hn, lt_self_iff_false, not_false_eq_true]

theorem exists_local_first_splitting {f : ℂ × ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : AnalyticOnNhd ℂ f (annularClosed R)) :
    ∃ p m : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ p (PuncturedDbarOne.annularOpen R) ∧
      AnalyticOnNhd ℂ m (PuncturedDbarOne.annularOpen R) ∧
      ∀ q ∈ annularOpen R, p q + m (q.1⁻¹, q.2) = f q := by
  have hp : 0 < R := zero_lt_one.trans hR
  have hi : 0 < R⁻¹ := inv_pos.mpr hp
  have houter : AnalyticOnNhd ℂ f
      (sphere (0 : ℂ) R ×ˢ annulus R⁻¹ R) :=
    hf.mono (prod_mono (outerCircle_subset_closedAnnulus hR) (annulus_subset_closedAnnulus R))
  have hinner : AnalyticOnNhd ℂ f
      (sphere (0 : ℂ) R⁻¹ ×ˢ annulus R⁻¹ R) :=
    hf.mono (prod_mono (innerCircle_subset_closedAnnulus hR) (annulus_subset_closedAnnulus R))
  refine ⟨firstPositiveContour f R, fun q => -firstReciprocalContour f R⁻¹ q,
    firstPositiveContour_analytic hp (isOpen_annulus R⁻¹ R) houter, ?_, ?_⟩
  · intro q hq
    have hq' : q ∈ ball (0 : ℂ) (R⁻¹)⁻¹ ×ˢ annulus R⁻¹ R := by
      simpa only [PuncturedDbarOne.annularOpen, inv_inv] using hq
    exact (firstReciprocalContour_analytic hi (isOpen_annulus R⁻¹ R) hinner q hq').neg
  · intro q hq
    have hq0 : q.1 ≠ 0 := norm_pos_iff.mp (hi.trans hq.1.1)
    have hs : AnalyticOnNhd ℂ (fun z => f (z, q.2)) (closedAnnulus R) := by
      intro z hz
      exact (hf (z, q.2) ⟨hz, annulus_subset_closedAnnulus R hq.2⟩).curry_left
    change cauchyTransform (fun z => f (z, q.2)) R q.1 +
      -infinityKernel (fun z => f (z, q.2)) R⁻¹ q.1⁻¹ = f q
    rw [infinityKernel_inv _ _ hq0]
    exact normalized_circleIntegral_sub hi (PuncturedDbarOne.inverse_radius_lt hR) hs hq.1

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne
