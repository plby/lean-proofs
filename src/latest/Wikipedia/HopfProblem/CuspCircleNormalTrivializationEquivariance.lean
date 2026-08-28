import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRadius

/-!
# Exact circle equivariance of the original normal coordinates

These identities use the actual diagonal maps of the original cusp
coordinate domain. They do not differentiate the action or replace it
by a tangent representation. Opposite weights become ordinary unit
complex scalar multiplication in the constructed real normal coordinates.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open ToricCharts
open SpecialPeriods.Threefold.VerticalAction

theorem fibreEquiv_oppositeWeights (b : Bool) (a u : ℂ) (hu : ‖u‖ = 1) (p : Fibre) :
    fibreEquiv b a (u⁻¹ * p.1, u * p.2) = u • fibreEquiv b a p := by
  cases b
  · exact lowerMap_oppositeWeights_of_norm_eq_one a u hu p
  · exact upperMap_oppositeWeights_of_norm_eq_one a u hu p

/-- The actual full coordinate action is scalar multiplication in the new normal factor. -/
theorem chartCoordinates_diagonal (b : Bool) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (z : CoordinateSpace 3) :
    chartCoordinates b (FixedCoordinates.diagonal u z) =
      (z 1, (u : ℂ) • (chartCoordinates b z).2) := by
  rw [FixedCoordinates.diagonal_apply]
  apply Prod.ext
  · rfl
  · exact fibreEquiv_oppositeWeights b (z 1) (u : ℂ) hu (z 0, z 2)

/-- Equivariance of the genuine inverse coordinates, in the original toric coordinate space. -/
theorem diagonal_chartCoordinates_symm (b : Bool) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (a : ℂ) (v : Fibre) :
    FixedCoordinates.diagonal u ((chartCoordinates b).symm (a, v)) =
      (chartCoordinates b).symm (a, (u : ℂ) • v) := by
  apply (chartCoordinates b).injective
  change chartCoordinates b (FixedCoordinates.diagonal u ((chartCoordinates b).symm (a, v))) =
    chartCoordinates b ((chartCoordinates b).symm (a, (u : ℂ) • v))
  rw [chartCoordinates_diagonal b u hu, (chartCoordinates b).apply_symm_apply,
    (chartCoordinates b).apply_symm_apply]
  rfl

theorem radiusSq_unit_smul (u : ℂ) (hu : ‖u‖ = 1) (v : Fibre) :
    radiusSq (u • v) = radiusSq v := by
  rw [radiusSq_smul, Complex.normSq_eq_norm_sq, hu]
  norm_num

theorem norm_unit_smul (u : ℂ) (hu : ‖u‖ = 1) (v : Fibre) : ‖u • v‖ = ‖v‖ := by
  rw [norm_smul, hu, one_mul]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
