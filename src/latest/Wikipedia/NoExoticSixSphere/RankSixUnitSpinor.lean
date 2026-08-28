import Wikipedia.NoExoticSixSphere.RankSixComplexProjection
import Wikipedia.NoExoticSixSphere.RankSixSpinorIdentity

/-!
# Actual orthogonal complex structures from unit spinors

The homogeneous quadratic matrix defines a genuine orthogonal complex
structure on real Euclidean six-space when the spinor has norm one.
-/

namespace NoExoticSixSphere.RankSixComplexProjection

open RankSixSkewMatrix GLOrthonormalization

abbrev UnitSpinor := Metric.sphere (0 : Spinor) 1

theorem spinorNormSq_eq_norm_sq (q : Spinor) :
    spinorNormSq (fun i ↦ q i) = ‖q‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [sum_four, Complex.sq_norm, Complex.normSq_apply, spinorNormSq]
  ring

theorem unitSpinor_norm (q : UnitSpinor) : ‖(q : Spinor)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using q.2

theorem unitSpinor_normSq (q : UnitSpinor) : spinorNormSq (fun i ↦ q.1 i) = 1 := by
  rw [spinorNormSq_eq_norm_sq, unitSpinor_norm, one_pow]

noncomputable def ofMatrix (A : Matrix6) (hA : A.transpose = -A)
    (hsq : A * A = -(1 : Matrix6)) : OrthogonalComplexStructures.Space 6 :=
  ⟨⟨Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 6) A, by
    change star (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 6) A) =
      -(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 6) A)
    simp only [← map_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, hA, map_neg]⟩, by
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 6) A *
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 6) A = -1
    simp only [← map_mul, hsq, map_neg, map_one]⟩

theorem matrix_ofMatrix (A : Matrix6) (hA : A.transpose = -A)
    (hsq : A * A = -(1 : Matrix6)) : matrix (ofMatrix A hA hsq) = A :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 6)).symm_apply_apply A

noncomputable def fromSpinor (q : UnitSpinor) : OrthogonalComplexStructures.Space 6 :=
  ofMatrix (spinorMatrix (fun i ↦ q.1 i)) (spinorMatrix_transpose _) (by
    rw [spinorMatrix_square, unitSpinor_normSq]
    simp)

theorem matrix_fromSpinor (q : UnitSpinor) :
    matrix (fromSpinor q) = spinorMatrix (fun i ↦ q.1 i) := matrix_ofMatrix _ _ _

theorem continuous_spinorMatrix :
    Continuous (fun q : Spinor ↦ spinorMatrix (fun i ↦ q i)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · change Continuous (fun q : Spinor ↦
      0)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(q 0).re ^ 2 + (q 1).re ^ 2 + (q 2).re ^ 2 - (q 3).re ^ 2 - (q 0).im ^ 2 + (q 1).im ^ 2 +
      (q 2).im ^ 2 - (q 3).im ^ 2)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      2 * (q 0).re * (q 1).im - 2 * (q 1).re * (q 0).im - 2 * (q 2).re * (q 3).im + 2 * (q 3).re
      * (q 2).im)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -2 * (q 0).re * (q 1).re + 2 * (q 2).re * (q 3).re - 2 * (q 0).im * (q 1).im + 2 * (q
      2).im * (q 3).im)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      2 * (q 0).re * (q 2).im + 2 * (q 1).re * (q 3).im - 2 * (q 2).re * (q 0).im - 2 * (q 3).re
      * (q 1).im)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -2 * (q 0).re * (q 2).re - 2 * (q 1).re * (q 3).re - 2 * (q 0).im * (q 2).im - 2 * (q
      1).im * (q 3).im)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(-(q 0).re ^ 2 + (q 1).re ^ 2 + (q 2).re ^ 2 - (q 3).re ^ 2 - (q 0).im ^ 2 + (q 1).im ^ 2
      + (q 2).im ^ 2 - (q 3).im ^ 2))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      0)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -2 * (q 0).re * (q 1).re - 2 * (q 2).re * (q 3).re - 2 * (q 0).im * (q 1).im - 2 * (q
      2).im * (q 3).im)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -2 * (q 0).re * (q 1).im + 2 * (q 1).re * (q 0).im - 2 * (q 2).re * (q 3).im + 2 * (q
      3).re * (q 2).im)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -2 * (q 0).re * (q 2).re + 2 * (q 1).re * (q 3).re - 2 * (q 0).im * (q 2).im + 2 * (q
      1).im * (q 3).im)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -2 * (q 0).re * (q 2).im + 2 * (q 1).re * (q 3).im + 2 * (q 2).re * (q 0).im - 2 * (q
      3).re * (q 1).im)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(2 * (q 0).re * (q 1).im - 2 * (q 1).re * (q 0).im - 2 * (q 2).re * (q 3).im + 2 * (q
      3).re * (q 2).im))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(-2 * (q 0).re * (q 1).re - 2 * (q 2).re * (q 3).re - 2 * (q 0).im * (q 1).im - 2 * (q
      2).im * (q 3).im))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      0)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(q 0).re ^ 2 + (q 1).re ^ 2 - (q 2).re ^ 2 + (q 3).re ^ 2 - (q 0).im ^ 2 + (q 1).im ^ 2 -
      (q 2).im ^ 2 + (q 3).im ^ 2)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      2 * (q 0).re * (q 3).im - 2 * (q 1).re * (q 2).im + 2 * (q 2).re * (q 1).im - 2 * (q 3).re
      * (q 0).im)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -2 * (q 0).re * (q 3).re + 2 * (q 1).re * (q 2).re - 2 * (q 0).im * (q 3).im + 2 * (q
      1).im * (q 2).im)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(-2 * (q 0).re * (q 1).re + 2 * (q 2).re * (q 3).re - 2 * (q 0).im * (q 1).im + 2 * (q
      2).im * (q 3).im))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(-2 * (q 0).re * (q 1).im + 2 * (q 1).re * (q 0).im - 2 * (q 2).re * (q 3).im + 2 * (q
      3).re * (q 2).im))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(-(q 0).re ^ 2 + (q 1).re ^ 2 - (q 2).re ^ 2 + (q 3).re ^ 2 - (q 0).im ^ 2 + (q 1).im ^ 2
      - (q 2).im ^ 2 + (q 3).im ^ 2))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      0)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -2 * (q 0).re * (q 3).re - 2 * (q 1).re * (q 2).re - 2 * (q 0).im * (q 3).im - 2 * (q
      1).im * (q 2).im)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -2 * (q 0).re * (q 3).im - 2 * (q 1).re * (q 2).im + 2 * (q 2).re * (q 1).im + 2 * (q
      3).re * (q 0).im)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(2 * (q 0).re * (q 2).im + 2 * (q 1).re * (q 3).im - 2 * (q 2).re * (q 0).im - 2 * (q
      3).re * (q 1).im))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(-2 * (q 0).re * (q 2).re + 2 * (q 1).re * (q 3).re - 2 * (q 0).im * (q 2).im + 2 * (q
      1).im * (q 3).im))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(2 * (q 0).re * (q 3).im - 2 * (q 1).re * (q 2).im + 2 * (q 2).re * (q 1).im - 2 * (q
      3).re * (q 0).im))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(-2 * (q 0).re * (q 3).re - 2 * (q 1).re * (q 2).re - 2 * (q 0).im * (q 3).im - 2 * (q
      1).im * (q 2).im))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      0)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(q 0).re ^ 2 - (q 1).re ^ 2 + (q 2).re ^ 2 + (q 3).re ^ 2 - (q 0).im ^ 2 - (q 1).im ^ 2 +
      (q 2).im ^ 2 + (q 3).im ^ 2)
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(-2 * (q 0).re * (q 2).re - 2 * (q 1).re * (q 3).re - 2 * (q 0).im * (q 2).im - 2 * (q
      1).im * (q 3).im))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(-2 * (q 0).re * (q 2).im + 2 * (q 1).re * (q 3).im + 2 * (q 2).re * (q 0).im - 2 * (q
      3).re * (q 1).im))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(-2 * (q 0).re * (q 3).re + 2 * (q 1).re * (q 2).re - 2 * (q 0).im * (q 3).im + 2 * (q
      1).im * (q 2).im))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(-2 * (q 0).re * (q 3).im - 2 * (q 1).re * (q 2).im + 2 * (q 2).re * (q 1).im + 2 * (q
      3).re * (q 0).im))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      -(-(q 0).re ^ 2 - (q 1).re ^ 2 + (q 2).re ^ 2 + (q 3).re ^ 2 - (q 0).im ^ 2 - (q 1).im ^ 2
      + (q 2).im ^ 2 + (q 3).im ^ 2))
    fun_prop
  · change Continuous (fun q : Spinor ↦
      0)
    fun_prop

theorem continuous_fromSpinor : Continuous fromSpinor := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 6)).toAlgEquiv.toLinearMap).comp
      (continuous_spinorMatrix.comp continuous_subtype_val)

theorem fromSpinor_recovers_signed_matrix (J : OrthogonalComplexStructures.Space 6)
    (q : UnitSpinor)
    (hq : spinorOuter (fun i ↦ q.1 i) = lineProjection (matrix J)) :
    matrix (fromSpinor q) = (-pfaffian (matrix J)) • matrix J := by
  rw [matrix_fromSpinor]
  apply spin_injective_on_skew (spinorMatrix_transpose _)
    (by simp [Matrix.transpose_smul, matrix_transpose])
  rw [spinorMatrix_spin, unitSpinor_normSq, hq, spin_real_smul]
  simp only [lineProjection, Complex.ofReal_one, one_smul, smul_sub, smul_smul,
    Complex.ofReal_neg]
  module

end NoExoticSixSphere.RankSixComplexProjection
