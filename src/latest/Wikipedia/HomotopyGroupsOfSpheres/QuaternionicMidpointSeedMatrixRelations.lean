import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointSeedCoordinates

/-! # Entrywise conjugation identities for the midpoint seed matrix -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open QuaternionicBottMatrix

theorem target_zero_phase : targetEigenvalues 0 * phase = -star phase := by
  calc
    _ = targetEigenvalues 0 * phase * (phase * star phase) := by rw [phase_unitary.2, mul_one]
    _ = (targetEigenvalues 0 * phase ^ 2) * star phase := by ring
    _ = -star phase := by rw [phase_sq, targetEigenvalues_product]; ring

theorem phase_delta_zero : targetEigenvalues 0 * phase * (Complex.I * (delta : ℂ) - 1) =
    (delta : ℂ) - Complex.I := by
  have h : star phase * (1 - Complex.I * (delta : ℂ)) = (delta : ℂ) - Complex.I := by
    simpa [Complex.star_def, sub_eq_add_neg] using congrArg star phase_delta
  rw [target_zero_phase]
  linear_combination h

theorem phase_epsilon_two : phase * (1 - Complex.I * (epsilon : ℂ)) =
    -targetEigenvalues 2 * (1 + Complex.I * (epsilon : ℂ)) := by
  rw [← phase_sq]
  linear_combination phase * phase_epsilon

theorem target_zero_linear : targetEigenvalues 0 * ((s : ℂ) + Complex.I) =
    1 + Complex.I * (s : ℂ) := by
  have ht : targetEigenvalues 0 = ((s : ℂ) + Complex.I) / 2 := by
    simp [targetEigenvalues, targetAlpha, targetBeta, s]
    ring
  have hs : (s : ℂ) ^ 2 = 3 := by exact_mod_cast s_sq
  rw [ht]
  ring_nf
  norm_num [hs, Complex.I_sq]
  ring

theorem target_two_linear : targetEigenvalues 2 * ((s : ℂ) - Complex.I) =
    -1 + Complex.I * (s : ℂ) := by
  have ht : targetEigenvalues 2 = (-((s : ℂ)) + Complex.I) / 2 := by
    simp [targetEigenvalues, targetAlpha, targetBeta, s, Matrix.cons_val_two]
    ring
  have hs : (s : ℂ) ^ 2 = 3 := by exact_mod_cast s_sq
  rw [ht]
  ring_nf
  norm_num [hs, Complex.I_sq]
  ring

theorem star_rootA_mul_rootC : (s : ℂ) * star (rootA * rootC) = Complex.I * rootB := by
  have h : (s : ℂ) * star (rootA * rootC) = -star rootB := by
    simpa [Complex.star_def, mul_assoc] using congrArg star rootA_mul_rootC
  rw [h, rootB_star]
  ring

theorem star_rootB_mul_rootC : star (rootB * rootC) = Complex.I * (epsilon : ℂ) * rootA := by
  rw [rootB_mul_rootC]
  simp only [star_mul, star_neg, rootA_star]
  have he : star (epsilon : ℂ) = (epsilon : ℂ) := by simp
  have hi : star Complex.I = -Complex.I := Complex.conj_I
  rw [he, hi]
  calc
    _ = Complex.I * (star phase * phase) * (epsilon : ℂ) * rootA := by ring
    _ = _ := by rw [phase_unitary.1]; ring

theorem entry00 : rootA ^ 2 = -targetEigenvalues 0 * star (rootA ^ 2) := by
  rw [star_pow, rootA_star, mul_pow, phase_sq]
  calc
    _ = -(targetEigenvalues 0 * targetEigenvalues 2) * rootA ^ 2 := by
      rw [targetEigenvalues_product]; ring
    _ = _ := by ring

theorem entry11 : rootB ^ 2 = -star (rootB ^ 2) := by
  rw [star_pow, rootB_star, mul_pow, neg_sq, Complex.I_sq]
  ring

theorem entry22 : rootC ^ 2 = -targetEigenvalues 2 * star (rootC ^ 2) := by
  have hp : targetEigenvalues 2 * star phase ^ 2 = 1 := by
    rw [← phase_sq, ← mul_pow, phase_unitary.2, one_pow]
  rw [star_pow, rootC_star, mul_pow, mul_pow, neg_sq, Complex.I_sq]
  calc
    _ = (targetEigenvalues 2 * star phase ^ 2) * rootC ^ 2 := by rw [hp, one_mul]
    _ = _ := by ring

theorem entry01 : rootA * rootB - star rootC =
    -targetEigenvalues 0 * star (rootA * rootB - star rootC) := by
  rw [star_sub, star_mul, star_star, rootA_star, rootB_star]
  apply mul_left_cancel₀ delta_complex_ne_zero
  linear_combination -(rootA * rootB) * phase_delta_zero - delta_star_rootC -
    targetEigenvalues 0 * delta_rootC

theorem entry10 : rootA * rootB + star rootC = -star (rootA * rootB + star rootC) := by
  rw [star_add, star_mul, star_star, rootA_star, rootB_star]
  apply mul_left_cancel₀ delta_complex_ne_zero
  linear_combination -(rootA * rootB) * phase_delta + delta_rootC + delta_star_rootC

theorem entry02 : rootA * rootC + star rootB =
    -targetEigenvalues 0 * star (rootA * rootC + star rootB) := by
  rw [star_add, star_star, rootB_star]
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt s_pos))
  linear_combination rootA_mul_rootC + targetEigenvalues 0 * star_rootA_mul_rootC +
    rootB * target_zero_linear

theorem entry20 : rootA * rootC - star rootB =
    -targetEigenvalues 2 * star (rootA * rootC - star rootB) := by
  rw [star_sub, star_star, rootB_star]
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt s_pos))
  linear_combination rootA_mul_rootC + targetEigenvalues 2 * star_rootA_mul_rootC -
    rootB * target_two_linear

theorem entry12 : rootB * rootC - star rootA = -star (rootB * rootC - star rootA) := by
  rw [star_sub, star_star, star_rootB_mul_rootC, rootA_star, rootB_mul_rootC]
  linear_combination -rootA * phase_epsilon

theorem entry21 : rootB * rootC + star rootA =
    -targetEigenvalues 2 * star (rootB * rootC + star rootA) := by
  rw [star_add, star_star, star_rootB_mul_rootC, rootA_star, rootB_mul_rootC]
  linear_combination rootA * phase_epsilon_two

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
