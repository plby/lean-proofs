import Wikipedia.HopfProblem.EllipticHigherHomologyTorusExteriorBasis
import Wikipedia.HopfProblem.EllipticHigherHomologyTorusExteriorMatrices

/-!
# Actual rank-three exterior-power actions

In the ordered basis `01, 02, 12`, the actual second exterior power of
an integral matrix has its matrix of two-by-two minors. In the oriented
third exterior power, with generator `012`, it is multiplication by the
determinant. These statements apply to every integral rank-three matrix.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open PeriodTorusHigherHomologyExterior
open scoped Matrix

/-- Mathlib's actual exterior-power map of the integral fibre-lattice map. -/
def torusExteriorMap (n : ℕ) (A : FibreMatrix) : torusExterior n →ₗ[ℤ] torusExterior n :=
  exteriorPower.map n A.mulVecLin

@[simp] theorem torusExteriorMap_one (n : ℕ) :
    torusExteriorMap n 1 = LinearMap.id := by
  simp only [torusExteriorMap, Matrix.mulVecLin_one, exteriorPower.map_id]

theorem torusExteriorMap_mul (n : ℕ) (A B : FibreMatrix) :
    torusExteriorMap n (A * B) = (torusExteriorMap n A).comp (torusExteriorMap n B) := by
  simp only [torusExteriorMap, Matrix.mulVecLin_mul, exteriorPower.map_comp]

/-- Each degree-two coefficient is the actual ordered minor of the original matrix. -/
theorem torusSquareMap_coefficient (A : FibreMatrix) (i j : Fin 3) :
    torusSquareBasis.repr (torusExteriorMap 2 A (torusSquareBasis j)) i =
      torusSquareMatrix A i j := by
  rw [torusSquareBasis, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  change (standardExteriorBasis 3 2).repr
      (exteriorPower.map 2 A.mulVecLin (standardExteriorBasis 3 2 (torusPairSubset j)))
      (torusPairSubset i) = _
  rw [standardExterior_map_coefficient, torusPairSubset_ordered, torusPairSubset_ordered]
  exact (torusSquareMatrix_eq_det_submatrix A i j).symm

/-- The sole degree-three matrix coefficient is the determinant. -/
theorem torusCubeMap_coefficient (A : FibreMatrix) (i j : Fin 1) :
    torusCubeBasis.repr (torusExteriorMap 3 A (torusCubeBasis j)) i = A.det := by
  rw [torusCubeBasis, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  change (standardExteriorBasis 3 3).repr
      (exteriorPower.map 3 A.mulVecLin (standardExteriorBasis 3 3 (torusTripleSubset j)))
      (torusTripleSubset i) = _
  rw [standardExterior_map_coefficient, torusTripleSubset_ordered, torusTripleSubset_ordered]
  rfl

theorem torusSquareMap_toMatrix (A : FibreMatrix) :
    LinearMap.toMatrix torusSquareBasis torusSquareBasis (torusExteriorMap 2 A) =
      torusSquareMatrix A := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact torusSquareMap_coefficient A i j

theorem torusCubeMap_toMatrix (A : FibreMatrix) :
    LinearMap.toMatrix torusCubeBasis torusCubeBasis (torusExteriorMap 3 A) =
      (fun _ _ : Fin 1 => A.det) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact torusCubeMap_coefficient A i j

/-- The actual second exterior power is represented by the ordered-minor matrix. -/
theorem torusSquareCoordinates_map (A : FibreMatrix) (x : torusExterior 2) :
    torusSquareCoordinates (torusExteriorMap 2 A x) =
      torusSquareMatrix A *ᵥ torusSquareCoordinates x := by
  have h := LinearMap.toMatrix_mulVec_repr torusSquareBasis torusSquareBasis
    (torusExteriorMap 2 A) x
  rw [torusSquareMap_toMatrix] at h
  simpa only [torusSquareCoordinates, Module.Basis.equivFun_apply] using h.symm

/-- The actual top exterior power is multiplication by the determinant. -/
theorem torusCubeCoordinates_map (A : FibreMatrix) (x : torusExterior 3) :
    torusCubeCoordinates (torusExteriorMap 3 A x) = A.det * torusCubeCoordinates x := by
  rw [torusCubeCoordinates_apply, torusCubeCoordinates_apply]
  have h := LinearMap.toMatrix_mulVec_repr torusCubeBasis torusCubeBasis
    (torusExteriorMap 3 A) x
  rw [torusCubeMap_toMatrix] at h
  simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_one] using (congrFun h 0).symm

/-- Two arbitrary lattice vectors have the usual signed-minor exterior coordinates. -/
theorem torusSquareCoordinates_ιMulti (v : Fin 2 → FibreLattice) (i : Fin 3) :
    torusSquareCoordinates (exteriorPower.ιMulti ℤ 2 v) i =
      v 0 (fibrePair i 0) * v 1 (fibrePair i 1) -
        v 0 (fibrePair i 1) * v 1 (fibrePair i 0) := by
  rw [torusSquareCoordinates_apply, torusSquareBasis, Module.Basis.repr_reindex_apply]
  change ((Pi.basisFun ℤ (Fin 3)).exteriorPower 2).repr
    (exteriorPower.ιMulti ℤ 2 v) (torusPairSubset i) = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Module.Basis.coord_apply, Pi.basisFun_repr, torusPairSubset_ordered,
    Matrix.det_fin_two, Matrix.of_apply]

/-- The oriented volume coordinate is the determinant of the three column vectors. -/
theorem torusCubeCoordinates_ιMulti (v : Fin 3 → FibreLattice) :
    torusCubeCoordinates (exteriorPower.ιMulti ℤ 3 v) =
      (Matrix.of fun i j : Fin 3 => v j i).det := by
  rw [torusCubeCoordinates_apply, torusCubeBasis, Module.Basis.repr_reindex_apply]
  change ((Pi.basisFun ℤ (Fin 3)).exteriorPower 3).repr
    (exteriorPower.ιMulti ℤ 3 v) (torusTripleSubset 0) = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Module.Basis.coord_apply, Pi.basisFun_repr, torusTripleSubset_ordered]
  exact Matrix.det_transpose (Matrix.of fun i j : Fin 3 => v j i)

/-- Naturality of degree-two exterior coordinates as an equality of actual linear maps. -/
theorem torusSquareCoordinates_intertwines (A : FibreMatrix) :
    torusSquareCoordinates.toLinearMap.comp (torusExteriorMap 2 A) =
      (torusSquareMatrix A).mulVecLin.comp torusSquareCoordinates.toLinearMap := by
  apply LinearMap.ext
  exact torusSquareCoordinates_map A

/-- The top-degree coordinate square has determinant multiplication on the target. -/
theorem torusCubeCoordinates_intertwines (A : FibreMatrix) :
    torusCubeCoordinates.toLinearMap.comp (torusExteriorMap 3 A) =
      (A.det • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)).comp torusCubeCoordinates.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact torusCubeCoordinates_map A x

theorem torusSquareCoordinates_conjugate (A : FibreMatrix) :
    (torusSquareCoordinates.toLinearMap.comp (torusExteriorMap 2 A)).comp
        torusSquareCoordinates.symm.toLinearMap = (torusSquareMatrix A).mulVecLin := by
  apply LinearMap.ext
  intro x
  change torusSquareCoordinates (torusExteriorMap 2 A (torusSquareCoordinates.symm x)) = _
  rw [torusSquareCoordinates_map, LinearEquiv.apply_symm_apply]
  rfl

theorem torusCubeCoordinates_conjugate (A : FibreMatrix) :
    (torusCubeCoordinates.toLinearMap.comp (torusExteriorMap 3 A)).comp
        torusCubeCoordinates.symm.toLinearMap = A.det • (LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
  apply LinearMap.ext
  intro x
  change torusCubeCoordinates (torusExteriorMap 3 A (torusCubeCoordinates.symm x)) = _
  rw [torusCubeCoordinates_map, LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem torusSquareMatrix_one : torusSquareMatrix 1 = 1 := by
  rw [← torusSquareMap_toMatrix, torusExteriorMap_one, LinearMap.toMatrix_id]

/-- Ordered minors multiply because they represent the actual exterior-power maps. -/
theorem torusSquareMatrix_mul (A B : FibreMatrix) :
    torusSquareMatrix (A * B) = torusSquareMatrix A * torusSquareMatrix B := by
  rw [← torusSquareMap_toMatrix, torusExteriorMap_mul,
    LinearMap.toMatrix_comp torusSquareBasis torusSquareBasis torusSquareBasis,
    torusSquareMap_toMatrix, torusSquareMap_toMatrix]

/-- The actual degree-two action recovers the source's explicit elliptic matrix. -/
theorem torusSquareCoordinates_fibreMatrix (j : Kind) (x : torusExterior 2) :
    torusSquareCoordinates (torusExteriorMap 2 (fibreMatrix j) x) =
      fibreSquareMatrix j *ᵥ torusSquareCoordinates x := by
  rw [torusSquareCoordinates_map, torusSquareMatrix_fibreMatrix]

/-- Both actual elliptic fibre actions preserve the positively oriented top coordinate. -/
@[simp] theorem torusCubeCoordinates_fibreMatrix (j : Kind) (x : torusExterior 3) :
    torusCubeCoordinates (torusExteriorMap 3 (fibreMatrix j) x) = torusCubeCoordinates x := by
  rw [torusCubeCoordinates_map, fibreMatrix_det, one_mul]

end Wikipedia.HopfProblem.Elliptic.HigherHomology
