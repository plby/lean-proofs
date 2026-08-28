import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedToricLocus
import Wikipedia.HopfProblem.CuspNormalizationSheafCurvesOrientation

/-!
# Native ray indices for the vertical toric fixed curves

The vertical direction is edge index one and hexagon ray one; its opposite
is hexagon ray four. In the already defined clockwise source ordering,
the third unoriented curve (zero-based source index two) has edge index
one. The statements below identify actual boundary subsets and their
existing quotient images without introducing a new curve-label convention.
-/

noncomputable section

open Set
open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedToric

open ToricFan ToricSpace ToricComponent CuspQuotient

@[simp] theorem edgeDirection_one_eq_hexagonRay_one :
    edgeDirection (1 : Fin 3) = hexagonRay (1 : Fin 6) := rfl

@[simp] theorem neg_edgeDirection_one_eq_hexagonRay_four :
    -edgeDirection (1 : Fin 3) = hexagonRay (4 : Fin 6) := by decide

theorem componentBoundary_vertical_eq_hexagon_one :
    componentBoundary (edgeDirection 1) = componentBoundary (hexagonRay 1) := rfl

theorem componentBoundary_neg_vertical_eq_hexagon_four :
    componentBoundary (-edgeDirection 1) = componentBoundary (hexagonRay 4) := by
  rw [neg_edgeDirection_one_eq_hexagonRay_four]

@[simp] theorem sourceEdgeIndex_two : NormalizationCurves.sourceEdgeIndex 2 = 1 := rfl

@[simp] theorem sourceDirection_two_eq_neg_vertical :
    NormalizationCurves.sourceDirection 2 = -edgeDirection 1 := by decide

@[simp] theorem sourceRay_five_eq_vertical :
    NormalizationCurves.sourceRay 5 = edgeDirection 1 := rfl

@[simp] theorem sourceRay_two_eq_neg_vertical :
    NormalizationCurves.sourceRay 2 = -edgeDirection 1 := by decide

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The image of the positive vertical boundary is literally the existing
unoriented double curve with native index one. -/
theorem componentProjection_hexagon_one_image :
    componentProjection C ε hε '' componentBoundary (hexagonRay 1) =
      doubleCurve C ε hε 1 := rfl

/-- The opposite vertical boundary has the very same actual quotient image. -/
theorem componentProjection_hexagon_four_image :
    componentProjection C ε hε '' componentBoundary (hexagonRay 4) =
      doubleCurve C ε hε 1 := by
  rw [← neg_edgeDirection_one_eq_hexagonRay_four]
  exact (componentProjection_oppositeBoundary_image C ε hε (edgeDirection 1)).symm

/-- The zero-based third source edge maps to native double-curve index one. -/
theorem doubleCurve_source_two :
    doubleCurve C ε hε (NormalizationCurves.sourceEdgeIndex 2) =
      doubleCurve C ε hε 1 := rfl

/-- The source's negative vertical boundary gives that same actual curve. -/
theorem componentProjection_sourceDirection_two_image :
    componentProjection C ε hε '' componentBoundary (NormalizationCurves.sourceDirection 2) =
      doubleCurve C ε hε 1 := by
  rw [sourceDirection_two_eq_neg_vertical, neg_edgeDirection_one_eq_hexagonRay_four]
  exact componentProjection_hexagon_four_image C ε hε

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedToric
