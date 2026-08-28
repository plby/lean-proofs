import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationCuspNaturality
import Wikipedia.HopfProblem.CuspNegationBoundary

/-!
# The actual cusp involution in the original regular and Wang maps

These comparisons apply to the constructed native involution, with no
map or equivariance supplied as a hypothesis. Both the original regular
coefficient and the actual Wang boundary use the unchanged real period
coordinate and the original positive-circle convention.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open ThreefoldOverlapMappingTorus MappingTorusHomology

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The actual original cusp-to-regular square, with both involutions constructed. -/
theorem cuspBoundaryNeg_regular_comp :
    (familyNegation Dsp).comp (boundaryToRegularFamily none) =
      (boundaryToRegularFamily none).comp CuspNegation.boundaryNeg :=
  cuspNegation_regular_comp CuspNegation.boundaryNeg CuspNegation.boundaryNeg_mk

/-- The same genuine square on original singular homology in every degree. -/
theorem cuspBoundaryNeg_regular_homology (n : ℕ)
    (a : SingularHomology (Boundary none) n) :
    singularHomologyMap (familyNegation Dsp) n (boundaryRegularHomologyMap none n a) =
      boundaryRegularHomologyMap none n (singularHomologyMap CuspNegation.boundaryNeg n a) := by
  let N : C(Boundary none, Boundary none) := CuspNegation.boundaryNeg
  have h := congrArg (fun f : C(Boundary none, (Dsp).Space) => singularHomologyMap f n)
    cuspBoundaryNeg_regular_comp
  change singularHomologyMap ((familyNegation Dsp).comp (boundaryToRegularFamily none)) n =
    singularHomologyMap ((boundaryToRegularFamily none).comp N) n at h
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

/-- The actual Wang map commutes with the actual cusp involution. -/
theorem cuspBoundaryNeg_wang (n : ℕ) (a : SingularHomology (Boundary none) (n + 1)) :
    wangBoundary (monodromy none) n (singularHomologyMap CuspNegation.boundaryNeg (n + 1) a) =
      singularHomologyMap flatNegation n (wangBoundary (monodromy none) n a) :=
  cuspNegation_wang CuspNegation.boundaryNeg CuspNegation.boundaryNeg_mk n a

/-- Every actual degree-two Wang value is fixed by the native involution. -/
theorem cuspBoundaryNeg_wang_two (a : SingularHomology (Boundary none) 3) :
    wangBoundary (monodromy none) 2 (singularHomologyMap CuspNegation.boundaryNeg 3 a) =
      wangBoundary (monodromy none) 2 a := by
  rw [cuspBoundaryNeg_wang, flatNegation_homology_two]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
