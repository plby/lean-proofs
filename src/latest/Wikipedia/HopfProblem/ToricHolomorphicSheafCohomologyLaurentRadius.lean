import Wikipedia.HopfProblem.HolomorphicCousinAnnulus
import Wikipedia.HopfProblem.HolomorphicCousinTransform

/-!
# Radius independence for the actual Laurent contour projections

For data holomorphic on the punctured plane, the interior Cauchy integral
is independent of every circle outside its pole. The reciprocal-coordinate
integral is independent of every sufficiently small positive circle.
-/

noncomputable section

open Complex Set Metric

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Laurent

open HolomorphicCousin

theorem closedAnnulus_subset_punctured {a b : ℝ} (ha : 0 < a) :
    closedBall (0 : ℂ) b \ ball 0 a ⊆ {z : ℂ | z ≠ 0} := by
  intro z hz he
  subst z
  exact hz.2 (mem_ball_self ha)

theorem continuousOn_sphere_of_punctured {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h {z | z ≠ 0}) {R : ℝ} (hR : 0 < R) :
    ContinuousOn h (sphere 0 R) := by
  apply hh.continuousOn.mono
  intro z hz he
  subst z
  have heq : (0 : ℝ) = R := by simpa only [mem_sphere, dist_self] using hz
  exact hR.ne' heq.symm

theorem cauchyTransform_radius_eq_of_inside {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h {z | z ≠ 0}) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z : ℂ} (hza : ‖z‖ < a) (hzb : ‖z‖ < b) :
    cauchyTransform h a z = cauchyTransform h b z := by
  unfold cauchyTransform
  congr 1
  rcases le_total a b with hab | hba
  · exact (circleIntegral_cauchy_radius_eq ha hab
      (hh.mono (closedAnnulus_subset_punctured ha)) (Or.inl hza)).symm
  · exact circleIntegral_cauchy_radius_eq hb hba
      (hh.mono (closedAnnulus_subset_punctured hb)) (Or.inl hzb)

theorem cauchyTransform_radius_eq_of_outside {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h {z | z ≠ 0}) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z : ℂ} (hza : a < ‖z‖) (hzb : b < ‖z‖) :
    cauchyTransform h a z = cauchyTransform h b z := by
  unfold cauchyTransform
  congr 1
  rcases le_total a b with hab | hba
  · exact (circleIntegral_cauchy_radius_eq ha hab
      (hh.mono (closedAnnulus_subset_punctured ha)) (Or.inr hzb)).symm
  · exact circleIntegral_cauchy_radius_eq hb hba
      (hh.mono (closedAnnulus_subset_punctured hb)) (Or.inr hza)

theorem infinityKernel_radius_eq {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h {z | z ≠ 0}) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u : ℂ} (hua : ‖u‖ < a⁻¹) (hub : ‖u‖ < b⁻¹) :
    infinityKernel h a u = infinityKernel h b u := by
  by_cases hu : u = 0
  · simp only [hu, infinityKernel_zero]
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hau : a < ‖u⁻¹‖ := by
    rw [norm_inv]
    exact (lt_inv_comm₀ ha hpos).mpr hua
  have hbu : b < ‖u⁻¹‖ := by
    rw [norm_inv]
    exact (lt_inv_comm₀ hb hpos).mpr hub
  have hia := infinityKernel_inv h a (inv_ne_zero hu)
  have hib := infinityKernel_inv h b (inv_ne_zero hu)
  simp only [inv_inv] at hia hib
  rw [hia, hib]
  exact cauchyTransform_radius_eq_of_outside hh ha hb hau hbu

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Laurent
