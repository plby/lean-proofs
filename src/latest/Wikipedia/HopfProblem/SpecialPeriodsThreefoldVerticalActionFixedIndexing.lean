import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedLocus
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedToricIndexing

/-!
# The source and native indices of the actual named fixed curve

The source's zero-based third unoriented curve is native double-curve
index one. The two vertical hexagon rays have native indices one and
four, and both actual normalization-boundary images give `D₀`.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction

local notation "CD" => CuspGeometry.data

/-- Exact source ordering, expressed using the existing source-index map. -/
theorem D₀_eq_source_curve_two :
    D₀ = CuspGeometry.doubleCurve (CuspQuotient.NormalizationCurves.sourceEdgeIndex 2) := rfl

/-- The actual image of the positive vertical normalization boundary. -/
theorem D₀_eq_positive_vertical_boundary_image :
    D₀ = CuspGeometry.inclusion ''
      (CuspQuotient.componentProjection (CD).correction (CD).radius (CD).radius_pos ''
        CuspQuotient.componentBoundary (ToricComponent.hexagonRay 1)) := rfl

/-- Its opposite boundary has the very same actual global image. -/
theorem D₀_eq_negative_vertical_boundary_image :
    D₀ = CuspGeometry.inclusion ''
      (CuspQuotient.componentProjection (CD).correction (CD).radius (CD).radius_pos ''
        CuspQuotient.componentBoundary (ToricComponent.hexagonRay 4)) := by
  have h : (CuspQuotient.componentProjection (CD).correction (CD).radius (CD).radius_pos ''
      CuspQuotient.componentBoundary (ToricComponent.hexagonRay 4) : Set CuspGeometry.LocalSpace) =
      CuspQuotient.doubleCurve (CD).correction (CD).radius (CD).radius_pos 1 :=
    FixedToric.componentProjection_hexagon_four_image
      (CD).correction (CD).radius (CD).radius_pos
  exact congrArg (fun S : Set CuspGeometry.LocalSpace => CuspGeometry.inclusion '' S) h.symm

/-- The source-oriented representative of the third double curve gives
the same literal fixed-curve subset of the actual glued threefold. -/
theorem D₀_eq_source_direction_two_boundary_image :
    D₀ = CuspGeometry.inclusion ''
      (CuspQuotient.componentProjection (CD).correction (CD).radius (CD).radius_pos ''
        CuspQuotient.componentBoundary (CuspQuotient.NormalizationCurves.sourceDirection 2)) := by
  have h : (CuspQuotient.componentProjection (CD).correction (CD).radius (CD).radius_pos ''
      CuspQuotient.componentBoundary (CuspQuotient.NormalizationCurves.sourceDirection 2) :
        Set CuspGeometry.LocalSpace) =
      CuspQuotient.doubleCurve (CD).correction (CD).radius (CD).radius_pos 1 :=
    FixedToric.componentProjection_sourceDirection_two_image
      (CD).correction (CD).radius (CD).radius_pos
  exact congrArg (fun S : Set CuspGeometry.LocalSpace => CuspGeometry.inclusion '' S) h.symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction
