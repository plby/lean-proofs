import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopShearCross
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangShearReal

/-!
# The degree-three cross summand on the original quotient torus

The native flat-torus homeomorphism and actual cross-product naturality
transport the degree-three result to the literal real lattice quotient.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear

open SingularMayerVietoris PeriodTorusHigherHomology
  PeriodTorusHigherHomology.CircleTopology

/-- The original real-torus shear fixes the actual cross product with every third-homology class. -/
theorem realShear_positiveCircleCross_three (χ : C(RealTorus₄, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (a : SingularHomology RealTorus₄ 3) :
    singularHomologyMap (realShear χ) 4 (positiveCircleCross RealTorus₄ 3 a) =
      positiveCircleCross RealTorus₄ 3 a := by
  apply (homeomorphHomologyEquiv realCircleCoordinates 4).injective
  change singularHomologyMap
      (circleProductMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4))) 4
    (singularHomologyMap (realShear χ) 4 (positiveCircleCross RealTorus₄ 3 a)) =
    singularHomologyMap
      (circleProductMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4))) 4
    (positiveCircleCross RealTorus₄ 3 a)
  simp only [realShear_coordinate_homology, positiveCircleCross_naturality]
  exact shear_positiveCircleCross_three (coordinateCharacter χ) (coordinateCharacter_add χ hχ)
    (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 3 a)

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear
