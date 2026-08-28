import Wikipedia.HopfProblem.PeriodTorusExponentialChernLocalPrimitives
import Wikipedia.HopfProblem.PeriodTorusExponentialChernWindingCoefficient
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalPatchBasic

/-!
# The original winding cochain has the actual local logarithmic primitives

The winding cochain retains its original native boundary-section definition.
The independently constructed local logarithmic cochains are actual primitives
of its original exponential-coefficient image on the original chart cover.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern

open ConstantSheafSingularComparison PeriodTorusAppellHumbert

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The literal coefficient image of the original winding cochain is
the actual differential of the original logarithmic local cochain. -/
theorem localPrimitive_winding (i : p.Torus) :
    (singularCochainComplex (chartCover p i) (AddCommGrpCat.of ℂ)).d 1 2
        (localPrimitive F i) =
      restrictGlobalCochain (X := TopCat.of p.Torus) (AddCommGrpCat.of ℂ) 2
        (windingComplexCochain F) (chartCover p i) := by
  rw [windingComplexCochain_eq_neg_periodTwoCochain]
  exact localPrimitive_d F i

end Wikipedia.HopfProblem.PeriodTorusExponentialChern
