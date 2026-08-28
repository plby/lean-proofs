import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSplitClasses

/-!
# The genuine degree-three source classes for the elliptic surface cover

The fibre input is the actual positively ordered top class of the split
three-torus.  The two classes in the original flat four-torus are obtained
from the literal zero-circle section and positive-circle cross product
through the original twist-adapted homeomorphism.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open CircleTopology FirstHurewicz
open PeriodTorusHigherHomologyPontryagin

/-- The actual positive top class of the split three-dimensional fibre. -/
def splitFibreInputThree : SingularHomology (ProductTorus 3) 3 :=
  torusH3Coordinates.symm 1

@[simp] theorem splitFibreInputThree_coordinates :
    torusH3Coordinates splitFibreInputThree = 1 :=
  torusH3Coordinates.apply_symm_apply 1

/-- Positivity is fixed by the actual ordered `0, 1, 2` loop product. -/
theorem splitFibreInputThree_product :
    splitFibreInputThree =
      tripleProduct (ProductTorus 3)
        (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 0 1)))
        (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 1 1)))
        (loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 2 1))) :=
  torusH3Coordinates_symm_one

/-- The positive degree-three fibre-section class in the original flat torus. -/
def splitFibreClassThree (j : Kind) : SingularHomology RealTorus₄ 3 :=
  singularHomologyMap ((splitFlatTorusHomeomorph j).symm :
    C(Circle × ProductTorus 3, RealTorus₄)) 3
      (circleSectionHomology (ProductTorus 3) 3 splitFibreInputThree)

/-- The positive circle crossed with the fibre's positive `u ∧ w` class,
transported back to the original flat torus. -/
def splitCircleClassThree (j : Kind) : SingularHomology RealTorus₄ 3 :=
  singularHomologyMap ((splitFlatTorusHomeomorph j).symm :
    C(Circle × ProductTorus 3, RealTorus₄)) 3
      (positiveCircleCross (ProductTorus 3) 2 splitFibreInputTwo)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
