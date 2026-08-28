import Wikipedia.HopfProblem.TriangleRiemannNormalizedCusp
import Wikipedia.HopfProblem.TriangleRiemannNormalizedCuspCoordinate

/-!
# The normalized cusp germ in the original periodic parameter

The fixed phase change puts the constructed reciprocal-normalized germ
in the actual cusp coordinate of the triangle quotient. Its simple zero,
analytic local inverse, and exact high-triangle formula are consequences
of the actual Riemann map and the actual exponential coordinate.
-/

noncomputable section

open Complex Filter Function Metric Set
open scoped Topology OnePoint

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle RiemannSphere.MobiusCircle

/-- The reciprocal-normalized cusp germ in the source's original
periodic parameter `exp (2 * π * I * z / width)`. -/
def triangleReciprocalNormalizedCuspQ (q : ℂ) : ℂ :=
  triangleReciprocalNormalizedCusp (triangleCuspPhase * q)

@[simp] theorem triangleReciprocalNormalizedCuspQ_zero :
    triangleReciprocalNormalizedCuspQ 0 = 0 := by
  simp [triangleReciprocalNormalizedCuspQ]

theorem triangleReciprocalNormalizedCuspQ_analyticAt_zero :
    AnalyticAt ℂ triangleReciprocalNormalizedCuspQ 0 := by
  have houter : AnalyticAt ℂ triangleReciprocalNormalizedCusp (triangleCuspPhase * 0) := by
    simpa only [mul_zero] using triangleReciprocalNormalizedCusp_analyticAt_zero
  exact houter.comp (analyticAt_const.mul analyticAt_id)

theorem triangleReciprocalNormalizedCuspQ_hasStrictDerivAt_zero :
    HasStrictDerivAt triangleReciprocalNormalizedCuspQ
      (deriv triangleReciprocalNormalizedCusp 0 * triangleCuspPhase) 0 := by
  have houter : HasStrictDerivAt triangleReciprocalNormalizedCusp
      (deriv triangleReciprocalNormalizedCusp 0) (triangleCuspPhase * 0) := by
    simpa only [mul_zero] using triangleReciprocalNormalizedCusp_analyticAt_zero.hasStrictDerivAt
  have hinner : HasStrictDerivAt (fun q : ℂ => triangleCuspPhase * q) triangleCuspPhase 0 := by
    simpa only [id_eq, mul_one] using! (hasStrictDerivAt_id (0 : ℂ)).const_mul triangleCuspPhase
  exact houter.comp 0 hinner

theorem triangleReciprocalNormalizedCuspQ_deriv_ne_zero :
    deriv triangleReciprocalNormalizedCuspQ 0 ≠ 0 := by
  rw [triangleReciprocalNormalizedCuspQ_hasStrictDerivAt_zero.hasDerivAt.deriv]
  exact mul_ne_zero triangleReciprocalNormalizedCusp_deriv_ne_zero triangleCuspPhase_ne_zero

/-- The source quotient cusp coordinate sees a simple zero, and hence
the required normalized function has a simple pole at the filled cusp. -/
theorem triangleReciprocalNormalizedCuspQ_order_zero :
    analyticOrderAt triangleReciprocalNormalizedCuspQ 0 = 1 :=
  triangleReciprocalNormalizedCuspQ_analyticAt_zero.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    triangleReciprocalNormalizedCuspQ_zero triangleReciprocalNormalizedCuspQ_deriv_ne_zero

theorem exists_triangleReciprocalNormalizedCuspQ_coordinate :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      0 ∈ e.source ∧ (∀ q, e q = triangleReciprocalNormalizedCuspQ q) ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target :=
  SpecialPeriods.exists_analytic_openPartialHomeomorph
    triangleReciprocalNormalizedCuspQ_analyticAt_zero
    triangleReciprocalNormalizedCuspQ_deriv_ne_zero

theorem triangleReciprocalNormalizedCuspQ_qParam (z : ℂ) :
    triangleReciprocalNormalizedCuspQ (Periodic.qParam width z) =
      triangleReciprocalNormalizedCusp (triangleCuspExp z) := by
  rw [triangleReciprocalNormalizedCuspQ, triangleCuspExp_eq_phase_mul_qParam]

theorem triangleReciprocalNormalizedCuspQ_cuspQ (z : UpperHalfPlane) :
    triangleReciprocalNormalizedCuspQ (cuspQ z) =
      triangleReciprocalNormalizedCusp (triangleCuspExp z) :=
  triangleReciprocalNormalizedCuspQ_qParam z

/-- The exact formula in the quotient's exponential coordinate on every
triangle point whose parameter lies in the chosen ideal disk. -/
theorem triangleReciprocalNormalizedCuspQ_eq_triangleMap_inv
    {z : ℂ} (hz : z ∈ triangleInterior)
    (hq : Periodic.qParam width z ∈ ball (0 : ℂ) triangleIdealGerm.radius) :
    triangleReciprocalNormalizedCuspQ (Periodic.qParam width z) =
      (crossRatio (triangleCornerThreeGerm.function 0) (triangleCornerFourGerm.function 0)
        (triangleIdealGerm.function 0) (triangleMap z))⁻¹ := by
  rw [triangleReciprocalNormalizedCuspQ_qParam]
  apply triangleReciprocalNormalizedCusp_eq_triangleMap_inv hz
  simpa only [mem_ball, dist_zero_right, norm_triangleCuspExp_eq_norm_qParam] using hq

/-- A uniform high-triangle neighborhood, expressed in the original
periodic parameter, satisfies the actual normalized cusp formula. -/
theorem exists_triangleReciprocalNormalizedCuspQ_high_formula :
    ∃ Y : ℝ, ∀ z : ℂ, z ∈ triangleInterior → Y < z.im →
      triangleReciprocalNormalizedCuspQ (Periodic.qParam width z) =
        (crossRatio (triangleCornerThreeGerm.function 0) (triangleCornerFourGerm.function 0)
          (triangleIdealGerm.function 0) (triangleMap z))⁻¹ := by
  obtain ⟨Y, hY⟩ := exists_triangleCuspExp_mem_ball_of_height triangleIdealGerm.radius_pos
  refine ⟨Y, fun z hz hzi => ?_⟩
  rw [triangleReciprocalNormalizedCuspQ_qParam]
  exact triangleReciprocalNormalizedCusp_eq_triangleMap_inv hz (hY z hzi)

/-- The same uniform formula uses the exact cusp function appearing in
the actual upper-half-plane quotient charts. -/
theorem exists_triangleReciprocalNormalizedCuspQ_high_cuspQ_formula :
    ∃ Y : ℝ, ∀ z : UpperHalfPlane, (z : ℂ) ∈ triangleInterior → Y < z.im →
      triangleReciprocalNormalizedCuspQ (cuspQ z) =
        (crossRatio (triangleCornerThreeGerm.function 0) (triangleCornerFourGerm.function 0)
          (triangleIdealGerm.function 0) (triangleMap z))⁻¹ := by
  obtain ⟨Y, hY⟩ := exists_triangleReciprocalNormalizedCuspQ_high_formula
  exact ⟨Y, fun z hz hzi => hY z hz hzi⟩

theorem triangleReciprocalNormalizedCuspQ_eventually_eq_triangleMap_inv :
    (fun z => triangleReciprocalNormalizedCuspQ (Periodic.qParam width z))
      =ᶠ[triangleInfinityFilter]
        (fun z =>
          (crossRatio (triangleCornerThreeGerm.function 0) (triangleCornerFourGerm.function 0)
            (triangleIdealGerm.function 0) (triangleMap z))⁻¹) := by
  filter_upwards [triangleReciprocalNormalizedCusp_eventually_eq_triangleMap_inv] with z hz
  rw [triangleReciprocalNormalizedCuspQ_qParam]
  exact hz

/-- The local periodic formula represents the actual sphere
normalization in its infinity chart, without replacing the sphere atlas. -/
theorem triangleReciprocalNormalizedCuspQ_triangleMap_sphere
    {z : ℂ} (hz : z ∈ triangleInterior)
    (hq : Periodic.qParam width z ∈ ball (0 : ℂ) triangleIdealGerm.radius) :
    RiemannSphere.threePointBiholomorph
        (triangleCornerThreeGerm.function 0) (triangleCornerFourGerm.function 0)
        (triangleIdealGerm.function 0) triangleCorner_boundary_values_ne
        triangleCornerThree_boundary_value_ne_ideal triangleCornerFour_boundary_value_ne_ideal
        (triangleMap z : RiemannSphere) =
      RiemannSphere.infinityParametrization
        (triangleReciprocalNormalizedCuspQ (Periodic.qParam width z)) := by
  have hza : triangleMap z ≠ triangleCornerThreeGerm.function 0 := by
    intro he
    have hn := triangleMap_norm_lt_one hz
    rw [he, triangleCornerThreeGerm.unit] at hn
    exact (lt_irrefl 1) hn
  rw [triangleReciprocalNormalizedCuspQ_eq_triangleMap_inv hz hq,
    ← crossRatio_swap_first_third]
  exact RiemannSphere.threePointBiholomorph_eq_infinityParametrization
    triangleCorner_boundary_values_ne triangleCornerThree_boundary_value_ne_ideal
    triangleCornerFour_boundary_value_ne_ideal hza

end Wikipedia.HopfProblem.RiemannMapping
