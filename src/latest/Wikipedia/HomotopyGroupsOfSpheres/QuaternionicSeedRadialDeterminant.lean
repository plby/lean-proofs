import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductRadialKernel
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointSeed

/-! # A positive radial determinant at the exact midpoint seed

The three squared-coordinate phases, together with the positive coordinate
weights, give a nonsingular matrix for the norm and square-sum constraints.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

theorem phase_re_pos : 0 < phase.re := by
  have hs : 1 < s := by
    unfold s
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by norm_num)
  change 0 < k * (s - 1) / 4
  exact div_pos (mul_pos k_pos (sub_pos.mpr hs)) (by norm_num)

theorem phase_im_pos : 0 < phase.im := by
  change 0 < k * (s + 1) / 4
  exact div_pos (mul_pos k_pos (by linarith [s_pos])) (by norm_num)

theorem phase_re_lt_one : phase.re < 1 := by
  have hn := phase_normSq
  rw [Complex.normSq_apply] at hn
  nlinarith [sq_pos_of_pos phase_im_pos, phase_re_pos]

theorem rootC_sq : rootC ^ 2 = Complex.I * phase * (weight2 : ℂ) := by
  calc
    _ = (phase * star phase) * rootC ^ 2 := by rw [phase_unitary.2, one_mul]
    _ = Complex.I * phase * (star rootC * rootC) := by
      rw [rootC_star]
      simp only [Complex.star_def]
      ring_nf
      norm_num
    _ = _ := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, rootC_normSq]

def phaseMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, 1; phase.re, 0, -phase.im; -phase.im, 1, phase.re]

theorem phaseMatrix_det :
    phaseMatrix.det = phase.re * (1 - phase.re) + phase.im * (1 + phase.im) := by
  simp [phaseMatrix, Matrix.det_fin_three]
  ring

theorem phaseMatrix_det_pos : 0 < phaseMatrix.det := by
  rw [phaseMatrix_det]
  exact add_pos (mul_pos phase_re_pos (sub_pos.mpr phase_re_lt_one))
    (mul_pos phase_im_pos (by linarith [phase_im_pos]))

theorem radialMatrix_vector :
    radialMatrix vector = phaseMatrix * Matrix.diagonal ![weight0, weight1, weight2] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [radialMatrix, vector, phaseMatrix, Matrix.mul_diagonal, Matrix.cons_val_two,
      rootA_normSq, rootB_normSq, rootC_normSq, rootA_sq, rootB_sq, rootC_sq,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem radialMatrix_vector_det :
    (radialMatrix vector).det = phaseMatrix.det * (weight0 * weight1 * weight2) := by
  rw [radialMatrix_vector, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three]
  rfl

theorem radialMatrix_vector_det_pos : 0 < (radialMatrix vector).det := by
  rw [radialMatrix_vector_det]
  exact mul_pos phaseMatrix_det_pos (mul_pos (mul_pos weight0_pos weight1_pos) weight2_pos)

theorem radialMatrix_rotatedInput_det_pos : 0 < (radialMatrix rotatedInput.val).det :=
  radialMatrix_vector_det_pos

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
