import Wikipedia.HopfProblem.TriangleRiemannBoundary
import Wikipedia.HopfProblem.TriangleCornerParameters
import Wikipedia.HopfProblem.RiemannBoundaryConformal
import Wikipedia.HopfProblem.RiemannBoundaryInjectivity

/-!
# The actual Riemann map at the two elliptic triangle vertices

The proved cubic and quartic half-parameters give noncritical analytic
boundary germs for the actual Riemann map.  Their inverse-disc limits are
the original geometric vertices, so their unit-circle values are distinct.
No continuous extension of the original Riemann map is assumed.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle RiemannBoundary

/-- A constructed analytic germ in a verified upper-half boundary parameter. -/
structure TriangleBoundaryGerm (φ : ℂ → ℂ) where
  function : ℂ → ℂ
  radius : ℝ
  radius_pos : 0 < radius
  analytic : AnalyticOnNhd ℂ function (ball 0 radius)
  agrees : EqOn function (triangleMap ∘ φ) (ball 0 radius ∩ {z | 0 < z.im})
  unit : ‖function 0‖ = 1
  strictDeriv : HasStrictDerivAt function (deriv function 0) 0
  deriv_ne_zero : deriv function 0 ≠ 0
  sourceCorrespondence : ∀ᶠ z in 𝓝 (0 : ℂ),
    ‖function z‖ < 1 → φ z ∈ triangleInterior ∧ triangleMap (φ z) = function z

theorem exists_triangleBoundaryGerm {φ : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hφ : AnalyticOnNhd ℂ φ (ball 0 δ ∩ {z | 0 < z.im}))
    (hφc : ContinuousOn φ (ball 0 δ ∩ {z | 0 ≤ z.im}))
    (hside : MapsTo φ (ball 0 δ ∩ {z | 0 < z.im}) triangleInterior)
    (hout : ∀ t : ℝ, (t : ℂ) ∈ ball 0 δ → φ (t : ℂ) ∉ triangleInterior) :
    Nonempty (TriangleBoundaryGerm φ) := by
  obtain ⟨r, hr, H, hHa, hHe, _, hHc, hHd, hHn, hHside⟩ :=
    exists_conformal_extension_discHomeomorph_in_half_chart
      triangleBiholomorph.toHomeomorph triangleMap_biholomorph isOpen_ball
      triangleMap_differentiable hφ.differentiableOn hφc hside hout
      (show ((0 : ℝ) : ℂ) ∈ ball (0 : ℂ) δ from mem_ball_self hδ)
  refine ⟨{
    function := H
    radius := r
    radius_pos := hr
    analytic := hHa
    agrees := hHe
    unit := hHc 0 (mem_ball_self hr)
    strictDeriv := hHd
    deriv_ne_zero := hHn
    sourceCorrespondence := ?_ }⟩
  filter_upwards [hHside, ball_mem_nhds (0 : ℂ) hr, ball_mem_nhds (0 : ℂ) hδ]
    with z hz hrz hδz hn
  have hi := hz.mp hn
  exact ⟨hside ⟨hδz, hi⟩, (hHe ⟨hrz, hi⟩).symm⟩

theorem exists_triangleCornerThreeGerm : Nonempty (TriangleBoundaryGerm cornerParameterThree) := by
  obtain ⟨δ, hδ, hφ, hφc, hside, hout, _, _⟩ := exists_cornerParameterThree_neighborhood
  exact exists_triangleBoundaryGerm hδ hφ hφc hside hout

theorem exists_triangleCornerFourGerm : Nonempty (TriangleBoundaryGerm cornerParameterFour) := by
  obtain ⟨δ, hδ, hφ, hφc, hside, hout, _, _⟩ := exists_cornerParameterFour_neighborhood
  exact exists_triangleBoundaryGerm hδ hφ hφc hside hout

def triangleCornerThreeGerm : TriangleBoundaryGerm cornerParameterThree :=
  Classical.choice exists_triangleCornerThreeGerm

def triangleCornerFourGerm : TriangleBoundaryGerm cornerParameterFour :=
  Classical.choice exists_triangleCornerFourGerm

theorem triangleCornerThree_inverse_limit :
    Tendsto (discHomeomorphInverse triangleBiholomorph.toHomeomorph)
      (𝓝[ball (0 : ℂ) 1] (triangleCornerThreeGerm.function 0)) (𝓝 (centerOne : ℂ)) := by
  simpa only [cornerParameterThree_zero] using
    tendsto_discHomeomorphInverse_of_boundary_chart triangleBiholomorph.toHomeomorph
      triangleMap_biholomorph continuousAt_cornerParameterThree_zero
      triangleCornerThreeGerm.strictDeriv triangleCornerThreeGerm.deriv_ne_zero
      triangleCornerThreeGerm.sourceCorrespondence

theorem triangleCornerFour_inverse_limit :
    Tendsto (discHomeomorphInverse triangleBiholomorph.toHomeomorph)
      (𝓝[ball (0 : ℂ) 1] (triangleCornerFourGerm.function 0)) (𝓝 (centerTwo : ℂ)) := by
  simpa only [cornerParameterFour_zero] using
    tendsto_discHomeomorphInverse_of_boundary_chart triangleBiholomorph.toHomeomorph
      triangleMap_biholomorph continuousAt_cornerParameterFour_zero
      triangleCornerFourGerm.strictDeriv triangleCornerFourGerm.deriv_ne_zero
      triangleCornerFourGerm.sourceCorrespondence

/-- The two actual geometric corners are distinct. -/
theorem triangle_centers_complex_ne : (centerOne : ℂ) ≠ (centerTwo : ℂ) := by
  intro h
  have hr := congrArg Complex.re h
  change centerOne.re = centerTwo.re at hr
  rw [centerTwo_re] at hr
  have hleft : centerOne.re = -1 / 2 := by
    change (SpecialPeriods.rho - 1).re = -1 / 2
    simp only [sub_re, SpecialPeriods.rho_re, one_re]
    norm_num
  rw [hleft] at hr
  linarith [width_pos]

/-- The actual Riemann map assigns distinct unit-circle values to the
two elliptic vertices; this is derived from its inverse, not imposed by
normalization. -/
theorem triangleCorner_boundary_values_ne :
    triangleCornerThreeGerm.function 0 ≠ triangleCornerFourGerm.function 0 := by
  intro h
  have hp := boundary_points_eq_of_equal_disc_values triangleBiholomorph.toHomeomorph
    triangleMap_biholomorph continuousAt_cornerParameterThree_zero
    continuousAt_cornerParameterFour_zero
    triangleCornerThreeGerm.strictDeriv triangleCornerThreeGerm.deriv_ne_zero
    triangleCornerFourGerm.strictDeriv triangleCornerFourGerm.deriv_ne_zero
    triangleCornerThreeGerm.sourceCorrespondence triangleCornerFourGerm.sourceCorrespondence
    triangleCornerThreeGerm.unit h
  exact triangle_centers_complex_ne (by simpa only [cornerParameterThree_zero,
    cornerParameterFour_zero] using hp)

end Wikipedia.HopfProblem.RiemannMapping
