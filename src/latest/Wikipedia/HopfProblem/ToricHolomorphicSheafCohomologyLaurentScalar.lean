import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLaurentRadius

/-!
# The actual entire positive and negative Laurent parts

Each value is computed by a convergent circle integral with an admissible
radius. Radius independence gives agreement with a fixed contour throughout
each sufficiently small neighborhood, and therefore proves analyticity.
No Laurent expansion is assumed or used as a definition of holomorphy.
-/

noncomputable section

open Complex Set Metric Filter
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Laurent

open HolomorphicCousin

/-- The entire nonnegative Laurent part, defined by an actual outer circle. -/
def positivePart (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  cauchyTransform h (‖z‖ + 1) z

/-- The negative Laurent part in the reciprocal coordinate, defined by an
actual inner circle. -/
def negativePart (h : ℂ → ℂ) (u : ℂ) : ℂ :=
  -infinityKernel h (‖u‖ + 1)⁻¹ u

theorem positivePart_eq_contour {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h {z | z ≠ 0}) {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : ‖z‖ < R) : positivePart h z = cauchyTransform h R z := by
  exact cauchyTransform_radius_eq_of_inside hh (by positivity) hR (lt_add_one _) hz

theorem negativePart_eq_contour {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h {z | z ≠ 0}) {R : ℝ} (hR : 0 < R)
    {u : ℂ} (hu : ‖u‖ < R⁻¹) : negativePart h u = -infinityKernel h R u := by
  apply congrArg Neg.neg
  apply infinityKernel_radius_eq hh (by positivity) hR _ hu
  simp only [inv_inv]
  exact lt_add_one _

@[simp] theorem negativePart_zero (h : ℂ → ℂ) : negativePart h 0 = 0 := by
  simp only [negativePart, infinityKernel_zero, neg_zero]

theorem positivePart_analytic {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h {z | z ≠ 0}) :
    AnalyticOnNhd ℂ (positivePart h) univ := by
  intro z _
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hz : z ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right] using lt_add_one ‖z‖
  have ha := cauchyTransform_analyticOnNhd_interior hR
    ((continuousOn_sphere_of_punctured hh hR).circleIntegrable hR.le)
  apply (ha z hz).congr
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact (positivePart_eq_contour hh hR
    (by simpa only [mem_ball, dist_zero_right] using hw : ‖w‖ < R)).symm

theorem negativePart_analytic {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h {z | z ≠ 0}) :
    AnalyticOnNhd ℂ (negativePart h) univ := by
  intro u _
  let R : ℝ := (‖u‖ + 1)⁻¹
  have hR : 0 < R := by dsimp only [R]; positivity
  have hu : u ∈ ball (0 : ℂ) R⁻¹ := by
    simpa only [mem_ball, dist_zero_right, R, inv_inv] using lt_add_one ‖u‖
  have ha := (analyticOnNhd_infinityKernel hR
    (continuousOn_sphere_of_punctured hh hR)).neg
  apply (ha u hu).congr
  filter_upwards [isOpen_ball.mem_nhds hu] with w hw
  exact (negativePart_eq_contour hh hR
    (by simpa only [mem_ball, dist_zero_right] using hw : ‖w‖ < R⁻¹)).symm

/-- The annular Cauchy formula gives the literal Laurent splitting on the
whole punctured plane. -/
theorem positivePart_add_negativePart_inv {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h {z | z ≠ 0}) {z : ℂ} (hz : z ≠ 0) :
    positivePart h z + negativePart h z⁻¹ = h z := by
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let a : ℝ := ‖z‖ / 2
  let b : ℝ := ‖z‖ + 1
  have ha : 0 < a := half_pos hp
  have haz : a < ‖z‖ := half_lt_self hp
  have hzb : ‖z‖ < b := lt_add_one _
  have hb : 0 < b := hp.trans hzb
  have hzi : ‖z⁻¹‖ < a⁻¹ := by
    rw [norm_inv]
    exact (inv_lt_inv₀ hp ha).mpr haz
  rw [positivePart_eq_contour hh hb hzb, negativePart_eq_contour hh ha hzi,
    infinityKernel_inv h a hz]
  exact normalized_circleIntegral_sub ha (haz.trans hzb)
    (hh.mono (closedAnnulus_subset_punctured ha)) ⟨haz, hzb⟩

theorem exists_entire_scalar_splitting {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h {z | z ≠ 0}) :
    ∃ p m : ℂ → ℂ, AnalyticOnNhd ℂ p univ ∧ AnalyticOnNhd ℂ m univ ∧
      m 0 = 0 ∧ ∀ z, z ≠ 0 → h z = p z + m z⁻¹ := by
  exact ⟨positivePart h, negativePart h, positivePart_analytic hh,
    negativePart_analytic hh, negativePart_zero h,
    fun _ hz => (positivePart_add_negativePart_inv hh hz).symm⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Laurent
