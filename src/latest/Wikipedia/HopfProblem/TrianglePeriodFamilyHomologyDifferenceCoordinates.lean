import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyGeneratorActions
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportTorus
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyLattice

/-!
# Actual higher-homology difference maps in integral coordinates

The previously proved geometric triangle-torus actions identify the actual
singular-homology generators with their exterior-minor matrices. Consequently
the difference maps of actual homology are conjugate to the literal integral
maps whose kernels and cokernels have been computed.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyExterior
open TrianglePeriodFamilyHomologyAlgebra

/-- The actual homology action of either source generator in its ordered minor coordinates. -/
theorem generatorHomologyTwo_coordinates (j : Bool)
    (a : SingularHomology RealTorus₄ 2) :
    FlatTorus.singularH2Coordinates (Homology.generatorHomologyEquiv j 2 a) =
      (if j then squareA₂ else squareA₁) *ᵥ FlatTorus.singularH2Coordinates a := by
  cases j
  · change FlatTorus.singularH2Coordinates
      (singularHomologyMap (triangleTorusHomeomorph triangleGenerator₁ :
        C(RealTorus₄, RealTorus₄)) 2 a) = _
    rw [FlatTorus.singularH2Coordinates_inducedHomology_triangle,
      triangleDualRepresentation_generator₁_matrix]
    rfl
  · change FlatTorus.singularH2Coordinates
      (singularHomologyMap (triangleTorusHomeomorph triangleGenerator₂ :
        C(RealTorus₄, RealTorus₄)) 2 a) = _
    rw [FlatTorus.singularH2Coordinates_inducedHomology_triangle,
      triangleDualRepresentation_generator₂_matrix]
    rfl

/-- The genuine degree-2 difference map has the checked literal integral coordinates. -/
theorem sourceDifferenceTwo_coordinates
    (x : SingularHomology RealTorus₄ 2 × SingularHomology RealTorus₄ 2) :
    FlatTorus.singularH2Coordinates (Homology.sourceDifference 2 x) =
      TrianglePeriodFamilyHomologyLattice.deltaTwo
        (FlatTorus.singularH2Coordinates x.1, FlatTorus.singularH2Coordinates x.2) := by
  change FlatTorus.singularH2Coordinates
    ((Homology.generatorHomologyEquiv false 2 x.1 - x.1) +
      (Homology.generatorHomologyEquiv true 2 x.2 - x.2)) =
    (squareA₁ *ᵥ FlatTorus.singularH2Coordinates x.1 -
      FlatTorus.singularH2Coordinates x.1) +
    (squareA₂ *ᵥ FlatTorus.singularH2Coordinates x.2 -
      FlatTorus.singularH2Coordinates x.2)
  rw [map_add, map_sub, map_sub, generatorHomologyTwo_coordinates,
    generatorHomologyTwo_coordinates]
  rfl

/-- The commuting square is equality of actual integral linear maps. -/
theorem sourceDifferenceTwo_intertwines :
    FlatTorus.singularH2Coordinates.toLinearMap.comp (Homology.sourceDifference 2) =
      TrianglePeriodFamilyHomologyLattice.deltaTwo.comp
        (FlatTorus.singularH2Coordinates.toAddEquiv.prodCongr
          FlatTorus.singularH2Coordinates.toAddEquiv).toIntLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact sourceDifferenceTwo_coordinates x

/-- Conjugation by the genuine marking gives the literal lattice difference map. -/
theorem sourceDifferenceTwo_conjugate :
    FlatTorus.singularH2Coordinates.toLinearMap.comp
      ((Homology.sourceDifference 2).comp
        (FlatTorus.singularH2Coordinates.symm.toAddEquiv.prodCongr
          FlatTorus.singularH2Coordinates.symm.toAddEquiv).toIntLinearEquiv.toLinearMap) =
      TrianglePeriodFamilyHomologyLattice.deltaTwo := by
  apply LinearMap.ext
  intro x
  change FlatTorus.singularH2Coordinates (Homology.sourceDifference 2
    (FlatTorus.singularH2Coordinates.symm x.1,
      FlatTorus.singularH2Coordinates.symm x.2)) = _
  rw [sourceDifferenceTwo_coordinates]
  simp only [LinearEquiv.apply_symm_apply]

/-- The actual homology action of either source generator in its ordered minor coordinates. -/
theorem generatorHomologyThree_coordinates (j : Bool)
    (a : SingularHomology RealTorus₄ 3) :
    FlatTorus.singularH3Coordinates (Homology.generatorHomologyEquiv j 3 a) =
      (if j then cubeA₂ else cubeA₁) *ᵥ FlatTorus.singularH3Coordinates a := by
  cases j
  · change FlatTorus.singularH3Coordinates
      (singularHomologyMap (triangleTorusHomeomorph triangleGenerator₁ :
        C(RealTorus₄, RealTorus₄)) 3 a) = _
    rw [FlatTorus.singularH3Coordinates_inducedHomology_triangle,
      triangleDualRepresentation_generator₁_matrix]
    rfl
  · change FlatTorus.singularH3Coordinates
      (singularHomologyMap (triangleTorusHomeomorph triangleGenerator₂ :
        C(RealTorus₄, RealTorus₄)) 3 a) = _
    rw [FlatTorus.singularH3Coordinates_inducedHomology_triangle,
      triangleDualRepresentation_generator₂_matrix]
    rfl

/-- The genuine degree-3 difference map has the checked literal integral coordinates. -/
theorem sourceDifferenceThree_coordinates
    (x : SingularHomology RealTorus₄ 3 × SingularHomology RealTorus₄ 3) :
    FlatTorus.singularH3Coordinates (Homology.sourceDifference 3 x) =
      TrianglePeriodFamilyHomologyLattice.deltaThree
        (FlatTorus.singularH3Coordinates x.1, FlatTorus.singularH3Coordinates x.2) := by
  change FlatTorus.singularH3Coordinates
    ((Homology.generatorHomologyEquiv false 3 x.1 - x.1) +
      (Homology.generatorHomologyEquiv true 3 x.2 - x.2)) =
    (cubeA₁ *ᵥ FlatTorus.singularH3Coordinates x.1 -
      FlatTorus.singularH3Coordinates x.1) +
    (cubeA₂ *ᵥ FlatTorus.singularH3Coordinates x.2 -
      FlatTorus.singularH3Coordinates x.2)
  rw [map_add, map_sub, map_sub, generatorHomologyThree_coordinates,
    generatorHomologyThree_coordinates]
  rfl

/-- The commuting square is equality of actual integral linear maps. -/
theorem sourceDifferenceThree_intertwines :
    FlatTorus.singularH3Coordinates.toLinearMap.comp (Homology.sourceDifference 3) =
      TrianglePeriodFamilyHomologyLattice.deltaThree.comp
        (FlatTorus.singularH3Coordinates.toAddEquiv.prodCongr
          FlatTorus.singularH3Coordinates.toAddEquiv).toIntLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact sourceDifferenceThree_coordinates x

/-- Conjugation by the genuine marking gives the literal lattice difference map. -/
theorem sourceDifferenceThree_conjugate :
    FlatTorus.singularH3Coordinates.toLinearMap.comp
      ((Homology.sourceDifference 3).comp
        (FlatTorus.singularH3Coordinates.symm.toAddEquiv.prodCongr
          FlatTorus.singularH3Coordinates.symm.toAddEquiv).toIntLinearEquiv.toLinearMap) =
      TrianglePeriodFamilyHomologyLattice.deltaThree := by
  apply LinearMap.ext
  intro x
  change FlatTorus.singularH3Coordinates (Homology.sourceDifference 3
    (FlatTorus.singularH3Coordinates.symm x.1,
      FlatTorus.singularH3Coordinates.symm x.2)) = _
  rw [sourceDifferenceThree_coordinates]
  simp only [LinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference

