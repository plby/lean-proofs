import Wikipedia.NoExoticSixSphere.RankSixLineProjection
import Wikipedia.NoExoticSixSphere.OrthogonalComplexStructures
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Trace

/-!
# From actual rank-six complex structures to complex-line projections

The matrix formulas are applied to the actual endomorphism underlying an
orthogonal complex structure. The resulting continuous complex-linear
operator is self-adjoint and idempotent, with one-dimensional complex range.
-/

namespace NoExoticSixSphere.RankSixComplexProjection

open RankSixSkewMatrix GLOrthonormalization LinearMap

abbrev Spinor := EuclideanSpace ℂ (Fin 4)

noncomputable def matrix (J : OrthogonalComplexStructures.Space 6) : Matrix6 :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 6)).symm
    (J.1 : Vector 6 →L[ℝ] Vector 6)

theorem matrix_transpose (J : OrthogonalComplexStructures.Space 6) :
    (matrix J).transpose = -matrix J := by
  have h : star (matrix J) = -matrix J := by
    simp only [matrix, ← map_star, ContinuousLinearMap.star_eq_adjoint,
      CayleyTransform.adjoint_eq_neg, map_neg]
  simpa only [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem matrix_square (J : OrthogonalComplexStructures.Space 6) :
    matrix J * matrix J = -(1 : Matrix6) := by
  have h : (J.1 : Vector 6 →L[ℝ] Vector 6) * J.1 = -1 := J.2
  simp only [matrix, ← map_mul, h, map_neg, map_one]

theorem continuous_matrix : Continuous matrix :=
  (LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 6)).symm.toAlgEquiv.toLinearMap).comp
      (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_pfaffian : Continuous pfaffian := by
  unfold pfaffian
  fun_prop

theorem continuous_spin : Continuous spin := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · change Continuous (fun A : Matrix6 ↦ (⟨-A 0 1 - A 2 3 - A 4 5, 0⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨-A 0 3 - A 1 2, -A 0 2 + A 1 3⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨-A 0 5 - A 1 4, -A 0 4 + A 1 5⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨-A 2 5 - A 3 4, -A 2 4 + A 3 5⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨-A 0 3 - A 1 2, A 0 2 - A 1 3⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨A 0 1 + A 2 3 - A 4 5, 0⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨A 2 5 - A 3 4, A 2 4 + A 3 5⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨-A 0 5 + A 1 4, -A 0 4 - A 1 5⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨-A 0 5 - A 1 4, A 0 4 - A 1 5⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨A 2 5 - A 3 4, -A 2 4 - A 3 5⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨A 0 1 - A 2 3 + A 4 5, 0⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨A 0 3 - A 1 2, A 0 2 + A 1 3⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨-A 2 5 - A 3 4, A 2 4 - A 3 5⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨-A 0 5 + A 1 4, A 0 4 + A 1 5⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨A 0 3 - A 1 2, -A 0 2 - A 1 3⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun A : Matrix6 ↦ (⟨-A 0 1 + A 2 3 + A 4 5, 0⟩ : ℂ))
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop

theorem continuous_lineProjection : Continuous lineProjection := by
  unfold lineProjection
  exact (continuous_const : Continuous (fun _ : Matrix6 ↦ (1 / 4 : ℂ))).smul
    ((continuous_const : Continuous (fun _ : Matrix6 ↦ (1 : Matrix4))).sub
      ((Complex.continuous_ofReal.comp continuous_pfaffian).smul continuous_spin))

noncomputable def projection (J : OrthogonalComplexStructures.Space 6) :
    Spinor →L[ℂ] Spinor :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 4) (lineProjection (matrix J))

theorem projection_idempotent (J : OrthogonalComplexStructures.Space 6) :
    IsIdempotentElem (projection J) := by
  change projection J * projection J = projection J
  simp only [projection, ← map_mul,
    lineProjection_idempotent _ (matrix_transpose J) (matrix_square J)]

theorem projection_selfAdjoint (J : OrthogonalComplexStructures.Space 6) :
    (projection J).adjoint = projection J := by
  change star (projection J) = projection J
  simp only [projection, ← map_star, Matrix.star_eq_conjTranspose,
    lineProjection_hermitian]

theorem continuous_projection : Continuous projection :=
  (LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 4)).toAlgEquiv.toLinearMap).comp
    (continuous_lineProjection.comp continuous_matrix)

theorem projection_trace (J : OrthogonalComplexStructures.Space 6) :
    LinearMap.trace ℂ Spinor (projection J).toLinearMap = 1 := by
  change LinearMap.trace ℂ Spinor
    (Matrix.toEuclideanLin (lineProjection (matrix J))) = 1
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]
  exact lineProjection_trace _

theorem projection_finrank (J : OrthogonalComplexStructures.Space 6) :
    Module.finrank ℂ (LinearMap.range (projection J).toLinearMap) = 1 := by
  have h : IsIdempotentElem (projection J).toLinearMap := by
    exact congrArg ContinuousLinearMap.toLinearMap (projection_idempotent J)
  have ht := h.isProj_range.trace
  rw [projection_trace J] at ht
  exact_mod_cast ht.symm

end NoExoticSixSphere.RankSixComplexProjection
