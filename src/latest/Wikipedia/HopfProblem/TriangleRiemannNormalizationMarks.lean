import Wikipedia.HopfProblem.TriangleRiemannCompactification

/-!
# The actual marked boundary values used for triangle normalization

These are the values of the constructed closed-disc homeomorphism at the
two elliptic vertices and the ideal vertex. Their unit norms follow from
the proved analytic boundary germs, not from additional normalization data.
-/

noncomputable section

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle

theorem triangleClosedDiscHomeomorph_norm_centerOne :
    ‖(triangleClosedDiscHomeomorph triangleClosedCenterOne : ℂ)‖ = 1 := by
  rw [triangleClosedDiscHomeomorph_centerOne]
  exact triangleCornerThreeGerm.unit

theorem triangleClosedDiscHomeomorph_norm_centerTwo :
    ‖(triangleClosedDiscHomeomorph triangleClosedCenterTwo : ℂ)‖ = 1 := by
  rw [triangleClosedDiscHomeomorph_centerTwo]
  exact triangleCornerFourGerm.unit

theorem triangleClosedDiscHomeomorph_norm_infty :
    ‖(triangleClosedDiscHomeomorph triangleClosedInfinity : ℂ)‖ = 1 := by
  rw [triangleClosedDiscHomeomorph_infty]
  exact triangleIdealGerm.unit

end Wikipedia.HopfProblem.RiemannMapping
