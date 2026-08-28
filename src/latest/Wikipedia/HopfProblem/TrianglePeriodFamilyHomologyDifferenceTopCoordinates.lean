import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTopDegreeRepresentation
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyGeneratorActions
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportTorus
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLatticeEven
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsPeriod

/-!
# Actual fourth-homology coordinates of the source difference map

The geometric flat-to-circle homeomorphism conjugates every actual triangle
action. The proved top-degree identity on the coordinate four-torus therefore
gives the identity on actual fourth homology of the real lattice torus.
Consequently the actual two-generator difference vanishes and agrees with the
literal determinant-lattice difference in the integral top-degree marking.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference

open Elliptic SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open TrianglePeriodFamilyHomologyLattice

/-- Every actual triangle-torus homeomorphism acts identically on its fourth singular homology. -/
theorem triangleHomologyFour_identity (g : TriangleGroup) :
    Homology.triangleHomologyEquiv g 4 =
      LinearEquiv.refl ℤ (SingularHomology RealTorus₄ 4) := by
  apply LinearEquiv.ext
  intro a
  apply (homeomorphHomologyEquiv flatTorusCircleHomeomorph 4).injective
  change singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 4
    (singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 4 a) =
    singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 4 a
  rw [FlatTorus.flatTorusCircleHomology_triangle_apply,
    Homology.triangleDualRepresentation_homologyFour, LinearMap.id_apply]

/-- The literal source difference map on actual fourth singular homology is zero. -/
@[simp] theorem sourceDifference_four : Homology.sourceDifference 4 = 0 := by
  apply LinearMap.ext
  intro x
  change (Homology.triangleHomologyEquiv triangleGenerator₁ 4 x.1 - x.1) +
    (Homology.triangleHomologyEquiv triangleGenerator₂ 4 x.2 - x.2) = 0
  rw [triangleHomologyFour_identity, triangleHomologyFour_identity]
  simp

/-- The actual top-degree source difference is the determinant-lattice difference
in the proved integral marking of actual fourth singular homology. -/
theorem sourceDifferenceFour_coordinates
    (x : SingularHomology RealTorus₄ 4 × SingularHomology RealTorus₄ 4) :
    realTorusH4Equiv (Homology.sourceDifference 4 x) =
      deltaFour (realTorusH4Equiv x.1, realTorusH4Equiv x.2) := by
  rw [sourceDifference_four, deltaFour_eq_zero]
  simp only [LinearMap.zero_apply, map_zero]

end Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference

