import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Compactly supported polar integrals

A continuous integrand supported in a bounded radial range is integrable on the
polar-coordinate target.  Its integral is an iterated integral over a finite
rectangle, in either order.  Continuity is only required on the closed rectangle;
the integrand may be arbitrary outside it, except for radial vanishing.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval Real

namespace Wikipedia.HopfProblem.HolomorphicCousin

private theorem integrableOn_polarRectangle {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hG : ContinuousOn G (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi)) :
    IntegrableOn G (Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi) := by
  apply (hG.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
  rintro ⟨r, θ⟩ ⟨hr, hθ⟩
  exact ⟨⟨hr.1.le, hr.2⟩, ⟨hθ.1.le, hθ.2.le⟩⟩

/-- Bounded radial support and continuity on the closed polar rectangle imply
integrability on the full polar-coordinate target. -/
theorem integrableOn_polarTarget_of_radial_support {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hG : ContinuousOn G (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi))
    (hzero : ∀ p, R < p.1 → G p = 0) :
    IntegrableOn G polarCoord.target := by
  apply (integrableOn_polarRectangle hG).of_forall_sdiff_eq_zero
    polarCoord.open_target.measurableSet
  rintro ⟨r, θ⟩ ⟨hp, hnot⟩
  apply hzero
  by_contra hr
  exact hnot ⟨⟨hp.1, le_of_not_gt hr⟩, hp.2⟩

/-- Radial vanishing reduces the polar integral to a finite rectangle. -/
theorem integral_polarTarget_eq_rectangle {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hzero : ∀ p, R < p.1 → G p = 0) :
    (∫ p in polarCoord.target, G p) =
      ∫ p in Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi, G p := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    polarCoord.open_target.measurableSet
  · rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    exact ⟨hr.1, hθ⟩
  · rintro ⟨r, θ⟩ ⟨hp, hnot⟩
    apply hzero
    by_contra hr
    exact hnot ⟨⟨hp.1, le_of_not_gt hr⟩, hp.2⟩

/-- The polar integral, with the radial integral outside the angular integral. -/
theorem integral_polarTarget_eq_radius_angle {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hR : 0 ≤ R)
    (hG : ContinuousOn G (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi))
    (hzero : ∀ p, R < p.1 → G p = 0) :
    (∫ p in polarCoord.target, G p) =
      ∫ r in 0..R, ∫ θ in (-Real.pi)..Real.pi, G (r, θ) := by
  rw [integral_polarTarget_eq_rectangle hzero]
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod G (by
    simpa only [Measure.volume_eq_prod] using integrableOn_polarRectangle hG)]
  simp_rw [intervalIntegral.integral_of_le hR,
    intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    integral_Ioc_eq_integral_Ioo]

/-- The polar integral, with the angular integral outside the radial integral. -/
theorem integral_polarTarget_eq_angle_radius {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hR : 0 ≤ R)
    (hG : ContinuousOn G (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi))
    (hzero : ∀ p, R < p.1 → G p = 0) :
    (∫ p in polarCoord.target, G p) =
      ∫ θ in (-Real.pi)..Real.pi, ∫ r in 0..R, G (r, θ) := by
  rw [integral_polarTarget_eq_rectangle hzero, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  rw [integral_prod_symm G (by
    simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod]
      using integrableOn_polarRectangle hG)]
  simp_rw [intervalIntegral.integral_of_le hR,
    intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    integral_Ioc_eq_integral_Ioo]

end Wikipedia.HopfProblem.HolomorphicCousin
