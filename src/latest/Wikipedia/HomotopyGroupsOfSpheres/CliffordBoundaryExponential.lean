import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryComplexStructure
import Wikipedia.HomotopyGroupsOfSpheres.ComplexRealLinearity
import Wikipedia.HomotopyGroupsOfSpheres.OrthogonalBottNativeFormula

/-! # Exact exponentials of the concrete rank-six complex-structure family -/

noncomputable section

open scoped Matrix Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott

open CliffordFiveHermitian BalancedRealInvolutions
open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

def scalarPhase (θ : ℝ) : unitary ℂ :=
  ⟨(Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I,
    Unitary.mem_iff_self_mul_star.mpr (by
      apply Complex.ext <;>
        norm_num [Complex.mul_re, Complex.mul_im,
          -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
          nlinarith [Real.cos_sq_add_sin_sq θ])⟩

def exponentialUnitary (θ : ℝ) (v : Sphere 2) : unitary (Matrix (Fin 3) (Fin 3) ℂ) :=
  MatrixBorder.unitaryBorder (scalarPhase θ, boundaryUnitary (latitudePoint θ v))

theorem exponentialUnitary_val (θ : ℝ) (v : Sphere 2) :
    (exponentialUnitary θ v).val =
      Real.cos θ • (1 : Matrix (Fin 3) (Fin 3) ℂ) +
        Real.sin θ • MatrixBorder.border Complex.I (generatorMatrix v.val) := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases
  · change (scalarPhase θ).val = Real.cos θ • (1 : ℂ) + Real.sin θ • Complex.I
    simp [scalarPhase, Complex.real_smul]
  · simp [exponentialUnitary, MatrixBorder.unitaryBorder, eq_comm]
  · simp [exponentialUnitary, MatrixBorder.unitaryBorder]
  · rename_i i j
    change (boundaryUnitary (latitudePoint θ v)).val i j =
      Real.cos θ • ((1 : Matrix (Fin 3) (Fin 3) ℂ) i.succ j.succ) +
        Real.sin θ • generatorMatrix v.val i j
    simpa only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Fin.succ_inj] using
      congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ ↦ A i j) (boundaryUnitary_latitude θ v)

theorem structureMap_operator (v : Sphere 2) :
    projectionRepresentation 3
      (ComplexMatrixRealification.matrix (MatrixBorder.border Complex.I (generatorMatrix v.val))) =
        (structureMap v).val.val := by
  rw [structureMap_apply]
  change Matrix.toEuclideanCLM (𝕜 := ℝ)
    (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (ComplexMatrixRealification.matrix (MatrixBorder.border Complex.I (generatorMatrix v.val)))) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (realGenerator v.val)
  rw [realGenerator_realification]

theorem exponential_eq_matrix (θ : ℝ) (v : Sphere 2) :
    OrthogonalExponential.exp (θ • (structureMap v).val) =
      matrixOrthogonal (ComplexMatrixRealification.unitaryMap (exponentialUnitary θ v)) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [OrthogonalComplexStructures.exp_smul]
  change _ = projectionRepresentation 3 (ComplexMatrixRealification.matrix
    (exponentialUnitary θ v).val)
  rw [exponentialUnitary_val, ComplexMatrixRealification.matrix_add,
    ComplexMatrixRealification.matrix_real_smul, ComplexMatrixRealification.matrix_real_smul,
    ComplexMatrixRealification.matrix_one, map_add, map_smul, map_smul, map_one,
    structureMap_operator]

theorem exponentialUnitary_reference (θ : ℝ) (v w : Sphere 2) :
    exponentialUnitary θ v * (exponentialUnitary θ w)⁻¹ =
      boundaryPaddedUnitary (latitudePoint θ v) *
        (boundaryPaddedUnitary (latitudePoint θ w))⁻¹ := by
  change MatrixBorder.unitaryBorder (scalarPhase θ, boundaryUnitary (latitudePoint θ v)) *
    (MatrixBorder.unitaryBorder (scalarPhase θ, boundaryUnitary (latitudePoint θ w)))⁻¹ =
      MatrixBorder.unitaryBorder (1, boundaryUnitary (latitudePoint θ v)) *
        (MatrixBorder.unitaryBorder (1, boundaryUnitary (latitudePoint θ w)))⁻¹
  rw [← map_inv, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply Prod.ext
  · simp
  · rfl

theorem exponential_reference (θ : ℝ) (v w : Sphere 2) :
    OrthogonalExponential.exp (θ • (structureMap v).val) *
      (OrthogonalExponential.exp (θ • (structureMap w).val))⁻¹ =
        boundaryOrthogonal (latitudePoint θ v) * (boundaryOrthogonal (latitudePoint θ w))⁻¹ := by
  rw [exponential_eq_matrix, exponential_eq_matrix]
  change matrixOrthogonal (ComplexMatrixRealification.unitaryMap (exponentialUnitary θ v)) *
    (matrixOrthogonal (ComplexMatrixRealification.unitaryMap (exponentialUnitary θ w)))⁻¹ =
      matrixOrthogonal (ComplexMatrixRealification.unitaryMap
        (boundaryPaddedUnitary (latitudePoint θ v))) *
        (matrixOrthogonal (ComplexMatrixRealification.unitaryMap
          (boundaryPaddedUnitary (latitudePoint θ w))))⁻¹
  simp only [← map_inv, ← map_mul, exponentialUnitary_reference]

end Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott
