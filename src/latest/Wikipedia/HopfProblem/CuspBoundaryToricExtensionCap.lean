import Wikipedia.HopfProblem.CuspBoundaryToricExtensionComparison
import Wikipedia.HopfProblem.CuspBoundaryToricExtensionHomotopy
import Wikipedia.HopfProblem.CuspBoundaryToricExtensionMarking
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusHomology

/-!
# The actual swept toric classes vanish in the original cusp cap

The genuine disc-product extension contracts only the base coordinate,
leaving both compact period phases unchanged.  The actual positive
circle cross product therefore has zero image in every degree.  The
degree-two classes below are the literal swept classes already carrying
their proved positive native Wang marking.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspBoundaryToricExtension

open SpecialPeriods.CuspFamily SingularMayerVietoris PeriodTorusHigherHomology
open ThreefoldOverlapMappingTorus.Cusp

/-- Every actual positive-circle cross class vanishes under the extended
toric boundary family at any original allowed height. -/
theorem toricBoundaryToFull_positiveCircleCross_eq_zero
    (D : Data) (h : Height D.radius) (n : ℕ)
    (a : SingularHomology (ProductTorus 2) n) :
    singularHomologyMap (toricBoundaryToFull D h) (n + 1)
      (positiveCircleCross (ProductTorus 2) n a) = 0 := by
  rw [toricBoundaryToFull_eq_extension]
  exact discExtension_positiveCircleCross_eq_zero D.radius D.radius_pos
    (discExtension D.correction D.radius) (circleAtHeight D h) n a

/-- The same vanishing for the two literal maps through the native
cusp boundary, in every integral homology degree. -/
theorem boundaryToFull_positiveCircleCross_eq_zero
    (D : Data) (h : Height D.radius) (n : ℕ)
    (a : SingularHomology (ProductTorus 2) n) :
    singularHomologyMap (boundaryToFull D h) (n + 1)
      (singularHomologyMap boundaryMap (n + 1)
        (positiveCircleCross (ProductTorus 2) n a)) = 0 := by
  have hzero := toricBoundaryToFull_positiveCircleCross_eq_zero D h n a
  change singularHomologyMap ((boundaryToFull D h).comp boundaryMap) (n + 1)
    (positiveCircleCross (ProductTorus 2) n a) = 0 at hzero
  rw [singularHomologyMap_comp boundaryMap (boundaryToFull D h) (n + 1)] at hzero
  exact hzero

/-- The actual original global cusp attachment kills these same
positive-circle cross classes; its radius has not been replaced. -/
theorem boundaryFilling_positiveCircleCross_eq_zero (n : ℕ)
    (a : SingularHomology (ProductTorus 2) n) :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap none (n + 1)
      (singularHomologyMap boundaryMap (n + 1)
        (positiveCircleCross (ProductTorus 2) n a)) = 0 := by
  change singularHomologyMap (ThreefoldOverlapMappingTorus.boundaryToFilling none) (n + 1)
    (singularHomologyMap boundaryMap (n + 1)
      (positiveCircleCross (ProductTorus 2) n a)) = 0
  rw [boundaryToFilling_eq_boundaryToFull]
  exact boundaryToFull_positiveCircleCross_eq_zero specialData specialHeight n a

/-- The prescribed actual degree-two swept toric class has zero image
in the original full cusp cap. -/
theorem boundaryFillingHomologyMap_sweptToricClass_eq_zero
    (a : SingularHomology (ProductTorus 2) 1) :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap none 2 (sweptToricClass a) = 0 :=
  boundaryFilling_positiveCircleCross_eq_zero 1 a

/-- Vanishing of the entire integral linear family of actual swept
two-dimensional boundary classes. -/
theorem boundaryFillingHomologyMap_sweptToricClassMap_eq_zero :
    (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap none 2).comp sweptToricClassMap =
      0 := by
  apply LinearMap.ext
  exact boundaryFillingHomologyMap_sweptToricClass_eq_zero

end Wikipedia.HopfProblem.CuspBoundaryToricExtension
