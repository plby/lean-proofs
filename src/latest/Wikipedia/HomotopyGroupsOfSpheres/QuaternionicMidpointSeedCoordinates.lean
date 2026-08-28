import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointSeedRoots

/-! # Product and conjugation relations for the exact midpoint input -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

theorem delta_complex_ne_zero : (delta : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt delta_pos)

theorem delta_epsilon_complex : (delta : ℂ) * (epsilon : ℂ) = (weight1 : ℂ) := by
  exact_mod_cast delta_mul_epsilon

theorem delta_star_rootC : (delta : ℂ) * star rootC = Complex.I * rootA * rootB := by
  have h : (delta : ℂ) * star rootC = -(star phase * star rootA * star rootB) := by
    simpa [Complex.star_def] using congrArg star delta_rootC
  rw [rootA_star, rootB_star] at h
  calc
    _ = -(star phase * (phase * rootA) * (-Complex.I * rootB)) := h
    _ = Complex.I * (star phase * phase) * rootA * rootB := by ring
    _ = _ := by rw [phase_unitary.1]; ring

theorem rootC_star : star rootC = -Complex.I * star phase * rootC := by
  apply mul_left_cancel₀ delta_complex_ne_zero
  calc
    _ = Complex.I * rootA * rootB := delta_star_rootC
    _ = Complex.I * (star phase * phase) * rootA * rootB := by rw [phase_unitary.1]; ring
    _ = (delta : ℂ) * (-Complex.I * star phase * rootC) := by
      linear_combination (Complex.I * star phase) * delta_rootC

theorem rootA_mul_rootC : (s : ℂ) * rootA * rootC = -rootB := by
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt weight0_pos))
  calc
    _ = rootA * ((delta : ℂ) * rootC) := by simp [delta]; ring
    _ = -(phase * rootA ^ 2 * rootB) := by rw [delta_rootC]; ring
    _ = -(phase * star phase) * (weight0 : ℂ) * rootB := by rw [rootA_sq]; ring
    _ = _ := by rw [phase_unitary.2]; ring

theorem rootB_mul_rootC : rootB * rootC = -Complex.I * phase * (epsilon : ℂ) * rootA := by
  apply mul_left_cancel₀ delta_complex_ne_zero
  calc
    _ = rootB * ((delta : ℂ) * rootC) := by ring
    _ = -phase * rootA * rootB ^ 2 := by rw [delta_rootC]; ring
    _ = -Complex.I * phase * (weight1 : ℂ) * rootA := by rw [rootB_sq]; ring
    _ = _ := by rw [← delta_epsilon_complex]; ring

theorem rootA_ne_zero : rootA ≠ 0 :=
  Complex.normSq_pos.mp (by rw [rootA_normSq]; exact weight0_pos)

theorem rootB_ne_zero : rootB ≠ 0 :=
  Complex.normSq_pos.mp (by rw [rootB_normSq]; exact weight1_pos)

theorem rootC_ne_zero : rootC ≠ 0 :=
  Complex.normSq_pos.mp (by rw [rootC_normSq]; exact weight2_pos)

def vector : Vector := ![rootA, rootB, rootC]

theorem vector_normPolynomial : normPolynomial vector = 1 := by
  simp only [normPolynomial, Fin.sum_univ_three, vector, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  change star rootA * rootA + star rootB * rootB + star rootC * rootC = 1
  simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    rootA_normSq, rootB_normSq, rootC_normSq]
  exact_mod_cast weights_sum

def rotatedInput : UnitSphere := ⟨WithLp.toLp 2 vector, by
  apply mem_sphere_zero_iff_norm.mpr
  have he := normPolynomial_eq_norm_sq (WithLp.toLp 2 vector)
  change normPolynomial vector = _ at he
  rw [vector_normPolynomial] at he
  have hs : ‖WithLp.toLp 2 vector‖ ^ 2 = (1 : ℝ) := by exact_mod_cast he.symm
  nlinarith [norm_nonneg (WithLp.toLp 2 vector)]⟩

theorem rotatedInput_val : (fun r ↦ rotatedInput.val r) = vector := rfl

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
