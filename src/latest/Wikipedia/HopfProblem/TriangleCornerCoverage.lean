import Wikipedia.HopfProblem.TriangleCornerNeighborhoods
import Wikipedia.HopfProblem.TriangleCornerSectorArguments
import Mathlib.Analysis.Analytic.Order

/-!
# Complete coverage of the actual triangle corners by their parameters

Every triangle point sufficiently close to either actual vertex is in the
image of its upper-half-plane corner parameter.  Its inverse is the
literal cubic or oriented quartic Cayley coordinate.  Thus the corner
parameters describe full one-sided neighborhoods, not just selected
approaches to the vertex.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

open RiemannBoundary

theorem cornerCoordinate_hasStrictDerivAt_self (a : UpperHalfPlane) :
    HasStrictDerivAt (cornerCoordinate a)
      (1 / ((a : ℂ) - conj (a : ℂ))) (a : ℂ) := by
  have hn : HasStrictDerivAt (fun z : ℂ => z - (a : ℂ)) 1 (a : ℂ) :=
    (hasStrictDerivAt_id (a : ℂ)).sub_const (a : ℂ)
  have hd : HasStrictDerivAt (fun z : ℂ => z - conj (a : ℂ)) 1 (a : ℂ) :=
    (hasStrictDerivAt_id (a : ℂ)).sub_const (conj (a : ℂ))
  have hden := sub_conj_ne_zero a a
  convert hn.div hd hden using 1
  all_goals first | rfl | (field_simp [hden]; ring)

theorem cornerCoordinate_order_self (a : UpperHalfPlane) :
    analyticOrderAt (cornerCoordinate a) (a : ℂ) = 1 := by
  apply (cornerCoordinate_analyticAt_self a).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · exact cornerCoordinate_self a
  · rw [(cornerCoordinate_hasStrictDerivAt_self a).hasDerivAt.deriv]
    exact one_div_ne_zero (sub_conj_ne_zero a a)

theorem cornerPowerThree_order_center :
    analyticOrderAt cornerPowerThree (centerOne : ℂ) = 3 := by
  change analyticOrderAt ((cornerCoordinate centerOne) ^ 3) (centerOne : ℂ) = _
  rw [analyticOrderAt_pow (cornerCoordinate_analyticAt_self centerOne),
    cornerCoordinate_order_self]
  norm_num

theorem cornerPowerFour_order_center :
    analyticOrderAt cornerPowerFour (centerTwo : ℂ) = 4 := by
  change analyticOrderAt (-((cornerCoordinate centerTwo) ^ 4)) (centerTwo : ℂ) = _
  rw [analyticOrderAt_neg, analyticOrderAt_pow (cornerCoordinate_analyticAt_self centerTwo),
    cornerCoordinate_order_self]
  norm_num

theorem cornerParameterThree_cornerPower {z : ℂ} (hzi : 0 < z.im)
    (hz : cornerCoordinate centerOne z ∈ cornerSectorThree) :
    cornerParameterThree (cornerPowerThree z) = z := by
  change cayley centerOne (principalRoot 3 (cornerCoordinate centerOne z ^ 3)) = z
  rw [cornerSectorThree_root_pow hz, cayley_cornerCoordinate centerOne hzi]

theorem cornerParameterFour_cornerPower {z : ℂ} (hzi : 0 < z.im)
    (hz : cornerCoordinate centerTwo z ∈ cornerSectorFour) :
    cornerParameterFour (cornerPowerFour z) = z := by
  change cayley centerTwo
    (rotatedPrincipalRootFour (-(cornerCoordinate centerTwo z ^ 4))) = z
  rw [cornerSectorFour_root_pow hz, cayley_cornerCoordinate centerTwo hzi]

/-- Every point of the triangle in a sufficiently small full neighborhood
of the first vertex is covered by the cubic upper-half parameter.  The
inverse parameter can be required to lie in any prescribed positive ball. -/
theorem exists_cornerParameterThree_coverage {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ ball (centerOne : ℂ) ε,
      z ∈ triangleInterior →
        cornerPowerThree z ∈ ball 0 δ ∩ {w : ℂ | 0 < w.im} ∧
        cornerParameterThree (cornerPowerThree z) = z := by
  obtain ⟨r, hr, hgeom⟩ := exists_cornerThree_neighborhood
  have hp : ∀ᶠ z : ℂ in 𝓝 (centerOne : ℂ), ‖cornerPowerThree z‖ < δ :=
    cornerPowerThree_analyticAt_center.continuousAt.norm.eventually_lt
      continuousAt_const (by simpa only [cornerPowerThree_center, norm_zero] using hδ)
  have hb : ∀ᶠ z : ℂ in 𝓝 (centerOne : ℂ), z ∈ ball (centerOne : ℂ) r :=
    ball_mem_nhds (centerOne : ℂ) hr
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hb.and hp)
  refine ⟨ε, hε, ?_⟩
  intro z hz hT
  have hnear := hball hz
  have h := hgeom z hnear.1
  have hs := h.2.mp hT
  refine ⟨⟨by simpa only [mem_ball, dist_zero_right] using hnear.2, ?_⟩,
    cornerParameterThree_cornerPower h.1 hs⟩
  exact cornerSectorThree_pow_im_pos hs

/-- The complete inverse-parameter statement at the actual order-four
vertex, using `-ζ⁴` to orient the upper half-plane correctly. -/
theorem exists_cornerParameterFour_coverage {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ ball (centerTwo : ℂ) ε,
      z ∈ triangleInterior →
        cornerPowerFour z ∈ ball 0 δ ∩ {w : ℂ | 0 < w.im} ∧
        cornerParameterFour (cornerPowerFour z) = z := by
  obtain ⟨r, hr, hgeom⟩ := exists_cornerFour_neighborhood
  have hp : ∀ᶠ z : ℂ in 𝓝 (centerTwo : ℂ), ‖cornerPowerFour z‖ < δ :=
    cornerPowerFour_analyticAt_center.continuousAt.norm.eventually_lt
      continuousAt_const (by simpa only [cornerPowerFour_center, norm_zero] using hδ)
  have hb : ∀ᶠ z : ℂ in 𝓝 (centerTwo : ℂ), z ∈ ball (centerTwo : ℂ) r :=
    ball_mem_nhds (centerTwo : ℂ) hr
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hb.and hp)
  refine ⟨ε, hε, ?_⟩
  intro z hz hT
  have hnear := hball hz
  have h := hgeom z hnear.1
  have hs := h.2.mp hT
  refine ⟨⟨by simpa only [mem_ball, dist_zero_right] using hnear.2, ?_⟩,
    cornerParameterFour_cornerPower h.1 hs⟩
  exact cornerSectorFour_pow_im_pos hs

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
