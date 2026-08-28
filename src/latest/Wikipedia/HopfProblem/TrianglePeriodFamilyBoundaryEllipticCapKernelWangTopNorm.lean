import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangNormBasic
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorLatticeMatrices

/-!
# The genuine elliptic covering norm on third homology

This is the degree-three counterpart of the lower-degree covering norms.
The map is the norm of the actual original affine monodromy, not an
assigned matrix.  Its matrix is computed in the ordered third exterior
marking `γuw, γuδ, γwδ, uwδ` of the original flat four-torus.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic SpecialPeriods SingularMayerVietoris MappingTorusHomology
open PeriodTorusHigherHomologyExterior

/-- The finite norm of the original third exterior monodromy matrix. -/
def originalNormMatrixThree (j : Kind) : LatticeMatrix :=
  ∑ k ∈ Finset.range j.order, (LocalSystemMatrices.exteriorCube j.matrix) ^ k

/-- The actual original affine action has the original third-minor matrix. -/
theorem originalAffine_h3_coordinates (j : Kind) (a : SingularHomology RealTorus₄ 3) :
    FlatTorus.singularH3Coordinates (monodromyHomologyMap (flatTorusAffine j j.twist) 3 a) =
      LocalSystemMatrices.exteriorCube j.matrix *ᵥ FlatTorus.singularH3Coordinates a := by
  rw [monodromyHomologyMap, flatTorusAffine_homology_triangle]
  change FlatTorus.singularH3Coordinates
    (singularHomologyMap
      (triangleTorusHomeomorph (Triangle.ellipticGenerator j) : C(RealTorus₄, RealTorus₄)) 3 a) = _
  rw [FlatTorus.singularH3Coordinates_inducedHomology_triangle,
    EllipticFilling.ellipticGenerator_dual_matrix]

/-- Powers of the genuine homology action have the corresponding matrix powers. -/
theorem originalAffine_pow_h3_coordinates (j : Kind) (k : ℕ)
    (a : SingularHomology RealTorus₄ 3) :
    FlatTorus.singularH3Coordinates
      ((monodromyHomologyMap (flatTorusAffine j j.twist) 3 ^ k) a) =
        (LocalSystemMatrices.exteriorCube j.matrix) ^ k *ᵥ FlatTorus.singularH3Coordinates a := by
  induction k with
  | zero => simp only [pow_zero, Module.End.one_apply, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, originalAffine_h3_coordinates,
      ih, Matrix.mulVec_mulVec, ← pow_succ']

/-- The actual finite covering norm is the finite third-exterior matrix norm. -/
theorem originalAffineNorm_h3_coordinates (j : Kind) (a : SingularHomology RealTorus₄ 3) :
    FlatTorus.singularH3Coordinates (originalAffineNorm j 3 a) =
      originalNormMatrixThree j *ᵥ FlatTorus.singularH3Coordinates a := by
  rw [originalAffineNorm_sum_powers, LinearMap.sum_apply, map_sum]
  simp only [originalAffine_pow_h3_coordinates]
  exact (Matrix.sum_mulVec _ _ _).symm

/-- Equality of genuine third-homology maps in the original exterior marking. -/
theorem originalAffineNorm_h3_conjugate (j : Kind) :
    FlatTorus.singularH3Coordinates.toLinearMap.comp
      ((originalAffineNorm j 3).comp FlatTorus.singularH3Coordinates.symm.toLinearMap) =
        (originalNormMatrixThree j).mulVecLin := by
  apply LinearMap.ext
  intro v
  change FlatTorus.singularH3Coordinates
    (originalAffineNorm j 3 (FlatTorus.singularH3Coordinates.symm v)) = _
  rw [originalAffineNorm_h3_coordinates, LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem originalNormMatrixThree_three :
    originalNormMatrixThree .three =
      !![3, 0, 0, 0;
         -1, 0, 0, 0;
         2, 0, 0, 0;
         0, -12, -6, 3] := by
  change (∑ k ∈ Finset.range 3, cubeA₁ ^ k) = _
  rw [cubeA₁_eq]
  decide

@[simp] theorem originalNormMatrixThree_four :
    originalNormMatrixThree .four =
      !![4, 0, 0, 0;
         -2, 0, 0, 0;
         2, 0, 0, 0;
         0, -12, -12, 4] := by
  change (∑ k ∈ Finset.range 4, cubeA₂ ^ k) = _
  rw [cubeA₂_eq]
  decide

/-- Explicit entries of the actual order-three covering norm on third homology. -/
theorem originalAffineNorm_h3_three (a : SingularHomology RealTorus₄ 3) :
    FlatTorus.singularH3Coordinates (originalAffineNorm .three 3 a) =
      !![3, 0, 0, 0; -1, 0, 0, 0; 2, 0, 0, 0; 0, -12, -6, 3] *ᵥ
        FlatTorus.singularH3Coordinates a := by
  rw [originalAffineNorm_h3_coordinates, originalNormMatrixThree_three]

/-- Explicit entries of the actual order-four covering norm on third homology. -/
theorem originalAffineNorm_h3_four (a : SingularHomology RealTorus₄ 3) :
    FlatTorus.singularH3Coordinates (originalAffineNorm .four 3 a) =
      !![4, 0, 0, 0; -2, 0, 0, 0; 2, 0, 0, 0; 0, -12, -12, 4] *ᵥ
        FlatTorus.singularH3Coordinates a := by
  rw [originalAffineNorm_h3_coordinates, originalNormMatrixThree_four]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
