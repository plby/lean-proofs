import Wikipedia.HopfProblem.TriangleClosedDomainBoundary
import Wikipedia.HopfProblem.TriangleClosedDomainLimits
import Wikipedia.HopfProblem.TriangleRiemannSideLimits
import Wikipedia.HopfProblem.TriangleRiemannCornerPatches
import Wikipedia.HopfProblem.TriangleRiemannIdealLimits

/-!
# The actual closed triangle is homeomorphic to the closed disc

The Riemann map on the original open triangle extends to its literal
closure in the one-point plane. The three side charts, two corner charts,
and logarithmic cusp chart supply all forward and inverse boundary limits.
Consequently the extension is a homeomorphism, without a Jordan-domain or
boundary-extension assumption. Its three vertex values are the previously
constructed, pairwise distinct analytic-germ values.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology OnePoint

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle RiemannBoundary

theorem triangleClosed_finite_forward_limit (x : TriangleClosedDomain)
    {a w : ℂ} (hxa : x.val = (a : OnePoint ℂ))
    (hf : Tendsto triangleMap (𝓝[triangleInterior] a) (𝓝 w)) :
    Tendsto (fun z : triangleClosedInterior =>
      (triangleClosedInteriorDiscHomeomorph z : ℂ))
      (comap (Subtype.val : triangleClosedInterior → TriangleClosedDomain) (𝓝 x))
      (𝓝 w) := by
  apply (triangleClosedInterior_forward_representative_tendsto_iff x).mpr
  rw [hxa]
  exact triangleOnePointRepresentative_finite_tendsto_iff.mpr hf

theorem triangleClosed_finite_inverse_limit (x : TriangleClosedDomain)
    {a w : ℂ} (hxa : x.val = (a : OnePoint ℂ))
    (hi : Tendsto (discHomeomorphInverse triangleBiholomorph.toHomeomorph)
      (𝓝[ball (0 : ℂ) 1] w) (𝓝 a)) :
    Tendsto (discHomeomorphInverse triangleClosedInteriorDiscHomeomorph)
      (𝓝[ball (0 : ℂ) 1] w) (𝓝 x) := by
  apply (triangleClosedInterior_inverse_tendsto_iff x).mpr
  rw [hxa]
  exact triangleDiscOnOnePointDomain_finite_inverse_tendsto_iff.mpr hi

/-- All boundary-limit data are proved on the actual compact source. -/
theorem triangleClosedDiscBoundaryLimits :
    DiscBoundaryLimits triangleClosedInteriorDiscHomeomorph := by
  intro x hx
  rcases triangleClosedBoundary_cases x hx with rfl | ⟨a, ha, hxa⟩ |
      ⟨a, ha, hxa⟩ | ⟨a, ha, hxa⟩ | rfl | rfl
  · exact ⟨triangleIdealGerm.function 0, triangleIdealGerm.unit,
      (triangleClosedInterior_forward_representative_tendsto_iff _).mpr
        triangleIdeal_forward_limit_onePoint,
      (triangleClosedInterior_inverse_tendsto_iff _).mpr triangleIdeal_inverse_limit⟩
  · obtain ⟨w, hw, hf, hi⟩ := exists_triangleMap_left_side_limits ha.1 ha.2.1 ha.2.2
    exact ⟨w, hw, triangleClosed_finite_forward_limit x hxa hf,
      triangleClosed_finite_inverse_limit x hxa hi⟩
  · obtain ⟨w, hw, hf, hi⟩ := exists_triangleMap_right_side_limits ha.1 ha.2.1 ha.2.2
    exact ⟨w, hw, triangleClosed_finite_forward_limit x hxa hf,
      triangleClosed_finite_inverse_limit x hxa hi⟩
  · obtain ⟨w, hw, hf, hi⟩ := exists_triangleMap_circle_side_limits
      ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
    exact ⟨w, hw, triangleClosed_finite_forward_limit x hxa hf,
      triangleClosed_finite_inverse_limit x hxa hi⟩
  · exact ⟨triangleCornerThreeGerm.function 0, triangleCornerThreeGerm.unit,
      triangleClosed_finite_forward_limit _ rfl triangleCornerThree_forward_limit,
      triangleClosed_finite_inverse_limit _ rfl triangleCornerThree_inverse_limit⟩
  · exact ⟨triangleCornerFourGerm.function 0, triangleCornerFourGerm.unit,
      triangleClosed_finite_forward_limit _ rfl triangleCornerFour_forward_limit,
      triangleClosed_finite_inverse_limit _ rfl triangleCornerFour_inverse_limit⟩

/-- The actual compactified triangle, with its inherited topology, is a
closed disc by extension of its original holomorphic Riemann map. -/
def triangleClosedDiscHomeomorph :
    TriangleClosedDomain ≃ₜ closedBall (0 : ℂ) 1 :=
  closedDiscHomeomorph triangleClosedInterior_dense
    triangleClosedInteriorDiscHomeomorph triangleClosedDiscBoundaryLimits

theorem triangleClosedDiscHomeomorph_interior (z : triangleClosedInterior) :
    (triangleClosedDiscHomeomorph z : ℂ) =
      (triangleClosedInteriorDiscHomeomorph z : ℂ) :=
  closedDiscHomeomorph_coe triangleClosedInterior_dense
    triangleClosedInteriorDiscHomeomorph triangleClosedDiscBoundaryLimits z

/-- No change is made to the original analytic map in the interior. -/
theorem triangleClosedDiscHomeomorph_triangle (z : triangleDomain) :
    (triangleClosedDiscHomeomorph (triangleClosedInclusion z) : ℂ) = triangleMap z := by
  rw [triangleMap_biholomorph z]
  exact (triangleClosedDiscHomeomorph_interior (triangleClosedInteriorHomeomorph z)).trans
    (congrArg (fun w : ball (0 : ℂ) 1 => (w : ℂ))
      (triangleClosedInteriorDiscHomeomorph_apply z))

theorem triangleClosedDiscHomeomorph_boundary {x : TriangleClosedDomain}
    (hx : x ∉ triangleClosedInterior) : ‖(triangleClosedDiscHomeomorph x : ℂ)‖ = 1 :=
  (discCompactificationMap_boundary triangleClosedInterior_dense
    triangleClosedInteriorDiscHomeomorph triangleClosedDiscBoundaryLimits hx).1

/-- The closed-disc interior corresponds exactly to the original open triangle. -/
theorem triangleClosedDiscHomeomorph_norm_lt_iff (x : TriangleClosedDomain) :
    ‖(triangleClosedDiscHomeomorph x : ℂ)‖ < 1 ↔ x ∈ triangleClosedInterior := by
  constructor
  · intro h
    by_contra hx
    rw [triangleClosedDiscHomeomorph_boundary hx] at h
    exact lt_irrefl _ h
  · intro hx
    rw [triangleClosedDiscHomeomorph_interior (⟨x, hx⟩ : triangleClosedInterior)]
    simpa only [mem_ball, dist_zero_right] using
      (triangleClosedInteriorDiscHomeomorph ⟨x, hx⟩).property

@[simp] theorem triangleClosedDiscHomeomorph_centerOne :
    (triangleClosedDiscHomeomorph triangleClosedCenterOne : ℂ) =
      triangleCornerThreeGerm.function 0 := by
  change discCompactificationMap triangleClosedInterior_dense
    triangleClosedInteriorDiscHomeomorph triangleClosedCenterOne = _
  exact triangleClosedInterior_dense.extend_eq_of_tendsto
    (triangleClosed_finite_forward_limit _ rfl triangleCornerThree_forward_limit)

@[simp] theorem triangleClosedDiscHomeomorph_centerTwo :
    (triangleClosedDiscHomeomorph triangleClosedCenterTwo : ℂ) =
      triangleCornerFourGerm.function 0 := by
  change discCompactificationMap triangleClosedInterior_dense
    triangleClosedInteriorDiscHomeomorph triangleClosedCenterTwo = _
  exact triangleClosedInterior_dense.extend_eq_of_tendsto
    (triangleClosed_finite_forward_limit _ rfl triangleCornerFour_forward_limit)

@[simp] theorem triangleClosedDiscHomeomorph_infty :
    (triangleClosedDiscHomeomorph triangleClosedInfinity : ℂ) =
      triangleIdealGerm.function 0 := by
  change discCompactificationMap triangleClosedInterior_dense
    triangleClosedInteriorDiscHomeomorph triangleClosedInfinity = _
  exact triangleClosedInterior_dense.extend_eq_of_tendsto
    ((triangleClosedInterior_forward_representative_tendsto_iff _).mpr
      triangleIdeal_forward_limit_onePoint)

end Wikipedia.HopfProblem.RiemannMapping
