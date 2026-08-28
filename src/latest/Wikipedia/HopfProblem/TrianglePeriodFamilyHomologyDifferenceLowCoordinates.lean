import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyGeneratorActions
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransport
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLattice

/-!
# Low-degree coordinates of the actual source difference maps

The degree-one marking is the actual singular first-homology period marking.
The two actual triangle generators act by the source's integral column matrices.
In degree zero the connected torus marking carries the actual zero difference
map to the literal zero lattice difference.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open TrianglePeriodFamilyHomologyLattice

/-- The first actual torus-generator action in the integral period marking. -/
theorem generatorHomologyOne_false_coordinates (a : SingularHomology RealTorus₄ 1) :
    FlatTorus.singularH1Equiv (Homology.generatorHomologyEquiv false 1 a) =
      A₁ *ᵥ FlatTorus.singularH1Equiv a := by
  change FlatTorus.singularH1Equiv
    (FirstHurewicz.inducedHomology
      (triangleTorusHomeomorph triangleGenerator₁ : C(RealTorus₄, RealTorus₄)) a) = _
  rw [FlatTorus.singularH1Equiv_inducedHomology_triangle,
    triangleDualRepresentation_generator₁_matrix]

/-- The second actual torus-generator action in the integral period marking. -/
theorem generatorHomologyOne_true_coordinates (a : SingularHomology RealTorus₄ 1) :
    FlatTorus.singularH1Equiv (Homology.generatorHomologyEquiv true 1 a) =
      A₂ *ᵥ FlatTorus.singularH1Equiv a := by
  change FlatTorus.singularH1Equiv
    (FirstHurewicz.inducedHomology
      (triangleTorusHomeomorph triangleGenerator₂ : C(RealTorus₄, RealTorus₄)) a) = _
  rw [FlatTorus.singularH1Equiv_inducedHomology_triangle,
    triangleDualRepresentation_generator₂_matrix]

/-- The actual degree-one source difference has exactly the two source lattice matrices. -/
theorem sourceDifferenceOne_coordinates
    (x : SingularHomology RealTorus₄ 1 × SingularHomology RealTorus₄ 1) :
    FlatTorus.singularH1Equiv (Homology.sourceDifference 1 x) =
      deltaOne (FlatTorus.singularH1Equiv x.1, FlatTorus.singularH1Equiv x.2) := by
  change FlatTorus.singularH1Equiv
    ((Homology.generatorHomologyEquiv false 1 x.1 - x.1) +
      (Homology.generatorHomologyEquiv true 1 x.2 - x.2)) =
    (A₁ *ᵥ FlatTorus.singularH1Equiv x.1 - FlatTorus.singularH1Equiv x.1) +
      (A₂ *ᵥ FlatTorus.singularH1Equiv x.2 - FlatTorus.singularH1Equiv x.2)
  rw [map_add, map_sub, map_sub, generatorHomologyOne_false_coordinates,
    generatorHomologyOne_true_coordinates]

/-- The actual degree-zero source difference is zero in the connected homology marking. -/
theorem sourceDifferenceZero_coordinates
    (x : SingularHomology RealTorus₄ 0 × SingularHomology RealTorus₄ 0) :
    connectedHomologyZeroEquiv RealTorus₄ (Homology.sourceDifference 0 x) =
      deltaZero (connectedHomologyZeroEquiv RealTorus₄ x.1,
        connectedHomologyZeroEquiv RealTorus₄ x.2) := by
  rw [Homology.sourceDifference_zero, deltaZero_eq_zero]
  simp only [LinearMap.zero_apply, map_zero]

end Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference

