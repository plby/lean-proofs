import ErdosProblems.Erdos964.ScalarKernelFaceMoments
import ErdosProblems.Erdos964.ScalarKernelFacePrimitive

/-!
# Finite coefficient vectors for the two scalar face moments
-/

namespace Erdos964

def scalarLargeFaceCoefficients : Fin 5 → ℝ := ![16, -56, 73, -42, 9]

def scalarSmallFaceCoefficients (z : ℝ) : Fin 3 → ℝ :=
  ![9 * z ^ 4 - 42 * z ^ 3 + 49 * z ^ 2, 36 * z ^ 3 - 84 * z ^ 2, 36 * z ^ 2]

theorem scalarLargeLogMoment_eq_sum (M R Q : ℕ) :
    scalarLargeLogMoment M R Q =
      ∑ j : Fin 5, scalarLargeFaceCoefficients j * scalarLogMoment M 2 R Q j := by
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
    scalarLargeFaceCoefficients, Matrix.cons_val_zero, Matrix.cons_val_succ]
  unfold scalarLargeLogMoment
  norm_num
  ring

theorem scalarSmallLogMoment_eq_sum (M R Q : ℕ) (z : ℝ) :
    scalarSmallLogMoment M R Q z =
      ∑ j : Fin 3, scalarSmallFaceCoefficients z j * scalarLogMoment M 2 R Q j := by
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
    scalarSmallFaceCoefficients, Matrix.cons_val_zero, Matrix.cons_val_succ]
  unfold scalarSmallLogMoment
  norm_num
  ring

theorem sum_abs_scalarLargeFaceCoefficients :
    (∑ j : Fin 5, |scalarLargeFaceCoefficients j|) = 196 := by
  norm_num [scalarLargeFaceCoefficients, Fin.sum_univ_succ]

theorem sum_abs_scalarSmallFaceCoefficients_le (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    (∑ j : Fin 3, |scalarSmallFaceCoefficients z j|) ≤ 256 := by
  have hz2 := pow_le_one₀ hz.1 hz.2 (n := 2)
  have hz3 := pow_le_one₀ hz.1 hz.2 (n := 3)
  have hz4 := pow_le_one₀ hz.1 hz.2 (n := 4)
  have hc0 : |9 * z ^ 4 - 42 * z ^ 3 + 49 * z ^ 2| ≤ 100 := by
    apply abs_le.mpr
    constructor <;> nlinarith [pow_nonneg hz.1 2, pow_nonneg hz.1 3, pow_nonneg hz.1 4]
  have hc1 : |36 * z ^ 3 - 84 * z ^ 2| ≤ 120 := by
    apply abs_le.mpr
    constructor <;> nlinarith [pow_nonneg hz.1 2, pow_nonneg hz.1 3]
  have hc2 : |36 * z ^ 2| ≤ 36 := by rw [abs_of_nonneg (by positivity)]; nlinarith
  simp only [Fin.sum_univ_succ, scalarSmallFaceCoefficients,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero]
  linarith

theorem scalarLargeFaceCoefficients_main (A L q : ℝ) (hL : L ≠ 0) :
    (∑ j : Fin 5, scalarLargeFaceCoefficients j *
      (A / ((2 + (j : ℕ) : ℕ) : ℝ) * q ^ (2 + (j : ℕ)) / L ^ (j : ℕ))) =
      A * L ^ 2 * scalarLargeFacePrimitive (q / L) := by
  norm_num [scalarLargeFaceCoefficients, Fin.sum_univ_succ]
  unfold scalarLargeFacePrimitive
  field_simp
  ring

theorem scalarSmallFaceCoefficients_main (A L q z : ℝ) (hL : L ≠ 0) :
    (∑ j : Fin 3, scalarSmallFaceCoefficients z j *
      (A / ((2 + (j : ℕ) : ℕ) : ℝ) * q ^ (2 + (j : ℕ)) / L ^ (j : ℕ))) =
      A * L ^ 2 * scalarSmallFacePrimitive z (q / L) := by
  norm_num [scalarSmallFaceCoefficients, Fin.sum_univ_succ]
  unfold scalarSmallFacePrimitive
  field_simp
  ring

theorem abs_linear_moment_error {ι : Type*} (s : Finset ι) (b x y : ι → ℝ) (E : ℝ)
    (herror : ∀ j ∈ s, |x j - y j| ≤ E) :
    |(∑ j ∈ s, b j * x j) - (∑ j ∈ s, b j * y j)| ≤ (∑ j ∈ s, |b j|) * E := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ s, |b j * x j - b j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ s, |b j| * |x j - y j| := by simp only [← mul_sub, abs_mul]
    _ ≤ ∑ j ∈ s, |b j| * E :=
      Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (herror j hj) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

end Erdos964
