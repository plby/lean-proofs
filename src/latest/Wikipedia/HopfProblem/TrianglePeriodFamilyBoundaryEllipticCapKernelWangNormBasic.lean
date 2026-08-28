import Wikipedia.HopfProblem.MappingTorusHomologyCoveringNorm
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticTailHomology
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportTorus
import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingTorus
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticAction

/-!
# The actual finite affine norm in the original torus markings

The covering convention uses the inverse of the original affine monodromy.
Its proved finite order identifies that norm with the positive one. The
native singular-homology action then gives the original integral matrix
and its exterior square in the original degree-one and degree-two markings.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic SpecialPeriods SingularMayerVietoris MappingTorusHomology
open MappingTorusHomology.Covering

/-- The actual norm appearing in the product cover of the original affine mapping torus. -/
def originalAffineNorm (j : Kind) (n : ℕ) :
    SingularHomology RealTorus₄ n →ₗ[ℤ] SingularHomology RealTorus₄ n :=
  homologyNorm j.order (flatTorusAffine j j.twist).symm n

/-- The original affine action has its stated finite order as an actual homeomorphism. -/
theorem originalAffine_pow_order (j : Kind) :
    flatTorusAffine j j.twist ^ j.order = 1 :=
  ThreefoldOverlapMappingTorus.Elliptic.affine_pow_order j j.twist j.matrix_fixes_twist

/-- Summing the inverse powers gives the same actual norm over one complete period. -/
theorem originalAffineNorm_eq_positive (j : Kind) (n : ℕ) :
    originalAffineNorm j n = homologyNorm j.order (flatTorusAffine j j.twist) n :=
  homologyNorm_symm j.order (flatTorusAffine j j.twist) n (originalAffine_pow_order j)

/-- The genuine affine norm is a finite sum of the genuine positive homology action. -/
theorem originalAffineNorm_sum_powers (j : Kind) (n : ℕ) :
    originalAffineNorm j n =
      ∑ k ∈ Finset.range j.order, (monodromyHomologyMap (flatTorusAffine j j.twist) n) ^ k := by
  rw [originalAffineNorm_eq_positive, homologyNorm_eq_sum_powers]

/-- The degree-one norm matrix in the original four lattice coordinates. -/
def originalNormMatrixOne (j : Kind) : LatticeMatrix :=
  ∑ k ∈ Finset.range j.order, j.matrix ^ k

/-- The degree-two norm matrix in the original six ordered exterior coordinates. -/
def originalNormMatrixTwo (j : Kind) : Matrix (Fin 6) (Fin 6) ℤ :=
  ∑ k ∈ Finset.range j.order, (LocalSystemMatrices.exteriorSquare j.matrix) ^ k

/-- The original affine monodromy acts by the original degree-one matrix. -/
theorem originalAffine_h1_coordinates (j : Kind) (a : SingularHomology RealTorus₄ 1) :
    FlatTorus.singularH1Equiv (monodromyHomologyMap (flatTorusAffine j j.twist) 1 a) =
      j.matrix *ᵥ FlatTorus.singularH1Equiv a := by
  rw [monodromyHomologyMap, flatTorusAffine_homology_triangle]
  change FlatTorus.singularH1Equiv
    (FirstHurewicz.inducedHomology
      (triangleTorusHomeomorph (Triangle.ellipticGenerator j) : C(RealTorus₄, RealTorus₄)) a) = _
  rw [FlatTorus.singularH1Equiv_inducedHomology_triangle,
    EllipticFilling.ellipticGenerator_dual_matrix]

/-- The original affine monodromy acts by the original degree-two minors. -/
theorem originalAffine_h2_coordinates (j : Kind) (a : SingularHomology RealTorus₄ 2) :
    FlatTorus.singularH2Coordinates (monodromyHomologyMap (flatTorusAffine j j.twist) 2 a) =
      LocalSystemMatrices.exteriorSquare j.matrix *ᵥ FlatTorus.singularH2Coordinates a := by
  rw [monodromyHomologyMap, flatTorusAffine_homology_triangle]
  change FlatTorus.singularH2Coordinates
    (singularHomologyMap
      (triangleTorusHomeomorph (Triangle.ellipticGenerator j) : C(RealTorus₄, RealTorus₄)) 2 a) = _
  rw [FlatTorus.singularH2Coordinates_inducedHomology_triangle,
    EllipticFilling.ellipticGenerator_dual_matrix]

private theorem marked_endomorphism_pow {M : Type*} [AddCommGroup M] [Module ℤ M]
    {r : ℕ} (e : M ≃ₗ[ℤ] (Fin r → ℤ)) (f : Module.End ℤ M)
    (A : Matrix (Fin r) (Fin r) ℤ) (hf : ∀ a, e (f a) = A *ᵥ e a)
    (k : ℕ) (a : M) : e ((f ^ k) a) = A ^ k *ᵥ e a := by
  induction k with
  | zero => simp only [pow_zero, Module.End.one_apply, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, hf, ih, Matrix.mulVec_mulVec, ← pow_succ']

theorem originalAffine_pow_h1_coordinates (j : Kind) (k : ℕ)
    (a : SingularHomology RealTorus₄ 1) :
    FlatTorus.singularH1Equiv
      ((monodromyHomologyMap (flatTorusAffine j j.twist) 1 ^ k) a) =
        j.matrix ^ k *ᵥ FlatTorus.singularH1Equiv a :=
  marked_endomorphism_pow FlatTorus.singularH1Equiv
    (monodromyHomologyMap (flatTorusAffine j j.twist) 1) j.matrix
    (originalAffine_h1_coordinates j) k a

theorem originalAffine_pow_h2_coordinates (j : Kind) (k : ℕ)
    (a : SingularHomology RealTorus₄ 2) :
    FlatTorus.singularH2Coordinates
      ((monodromyHomologyMap (flatTorusAffine j j.twist) 2 ^ k) a) =
        (LocalSystemMatrices.exteriorSquare j.matrix) ^ k *ᵥ FlatTorus.singularH2Coordinates a :=
  marked_endomorphism_pow FlatTorus.singularH2Coordinates
    (monodromyHomologyMap (flatTorusAffine j j.twist) 2)
    (LocalSystemMatrices.exteriorSquare j.matrix) (originalAffine_h2_coordinates j) k a

/-- The literal covering norm on first homology is the finite original matrix norm. -/
theorem originalAffineNorm_h1_coordinates (j : Kind) (a : SingularHomology RealTorus₄ 1) :
    FlatTorus.singularH1Equiv (originalAffineNorm j 1 a) =
      originalNormMatrixOne j *ᵥ FlatTorus.singularH1Equiv a := by
  rw [originalAffineNorm_sum_powers, LinearMap.sum_apply, map_sum]
  simp only [originalAffine_pow_h1_coordinates]
  exact (Matrix.sum_mulVec _ _ _).symm

/-- The literal covering norm on second homology is the finite original exterior norm. -/
theorem originalAffineNorm_h2_coordinates (j : Kind) (a : SingularHomology RealTorus₄ 2) :
    FlatTorus.singularH2Coordinates (originalAffineNorm j 2 a) =
      originalNormMatrixTwo j *ᵥ FlatTorus.singularH2Coordinates a := by
  rw [originalAffineNorm_sum_powers, LinearMap.sum_apply, map_sum]
  simp only [originalAffine_pow_h2_coordinates]
  exact (Matrix.sum_mulVec _ _ _).symm

/-- Equality of actual degree-one linear maps in the original marking. -/
theorem originalAffineNorm_h1_conjugate (j : Kind) :
    FlatTorus.singularH1Equiv.toLinearMap.comp
      ((originalAffineNorm j 1).comp FlatTorus.singularH1Equiv.symm.toLinearMap) =
        (originalNormMatrixOne j).mulVecLin := by
  apply LinearMap.ext
  intro v
  change FlatTorus.singularH1Equiv (originalAffineNorm j 1 (FlatTorus.singularH1Equiv.symm v)) = _
  rw [originalAffineNorm_h1_coordinates, LinearEquiv.apply_symm_apply]
  rfl

/-- Equality of actual degree-two linear maps in the original marking. -/
theorem originalAffineNorm_h2_conjugate (j : Kind) :
    FlatTorus.singularH2Coordinates.toLinearMap.comp
      ((originalAffineNorm j 2).comp FlatTorus.singularH2Coordinates.symm.toLinearMap) =
        (originalNormMatrixTwo j).mulVecLin := by
  apply LinearMap.ext
  intro v
  change FlatTorus.singularH2Coordinates
    (originalAffineNorm j 2 (FlatTorus.singularH2Coordinates.symm v)) = _
  rw [originalAffineNorm_h2_coordinates, LinearEquiv.apply_symm_apply]
  rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
