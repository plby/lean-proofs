import Wikipedia.HopfProblem.EllipticHigherHomologyCoordinatesTorus
import Wikipedia.HopfProblem.EllipticHigherHomologyTorus
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProduct

/-!
# Four native homology inputs in the elliptic split torus

These classes are the actual section and positive-circle-cross summands
under the original twist-adapted torus homeomorphism. No quotient lift is
chosen in their definition.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open CircleTopology

/-- The positive `w`-loop in the three-dimensional split fibre. -/
def splitFibreInputOne : SingularHomology (ProductTorus 3) 1 :=
  torusH1Equiv.symm ![0, 1, 0]

/-- The positive `u ∧ w` class in the three-dimensional split fibre. -/
def splitFibreInputTwo : SingularHomology (ProductTorus 3) 2 :=
  torusH2Coordinates.symm ![1, 0, 0]

/-- The degree-one fibre-section class, taken back to the original flat torus. -/
def splitFibreClassOne (j : Kind) : SingularHomology RealTorus₄ 1 :=
  singularHomologyMap ((splitFlatTorusHomeomorph j).symm :
    C(Circle × ProductTorus 3, RealTorus₄)) 1
      (circleSectionHomology (ProductTorus 3) 1 splitFibreInputOne)

/-- The degree-one positive circle class, taken back to the original flat torus. -/
def splitCircleClassOne (j : Kind) : SingularHomology RealTorus₄ 1 :=
  singularHomologyMap ((splitFlatTorusHomeomorph j).symm :
    C(Circle × ProductTorus 3, RealTorus₄)) 1
      (positiveCircleCross (ProductTorus 3) 0 (pointClass (0 : ProductTorus 3)))

/-- The degree-two fibre-section class, taken back to the original flat torus. -/
def splitFibreClassTwo (j : Kind) : SingularHomology RealTorus₄ 2 :=
  singularHomologyMap ((splitFlatTorusHomeomorph j).symm :
    C(Circle × ProductTorus 3, RealTorus₄)) 2
      (circleSectionHomology (ProductTorus 3) 2 splitFibreInputTwo)

/-- The positive circle crossed with the fibre's `w`-loop, in the original flat torus. -/
def splitCircleClassTwo (j : Kind) : SingularHomology RealTorus₄ 2 :=
  singularHomologyMap ((splitFlatTorusHomeomorph j).symm :
    C(Circle × ProductTorus 3, RealTorus₄)) 2
      (positiveCircleCross (ProductTorus 3) 1 splitFibreInputOne)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
