import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointPreimageBound

/-!
# Exact scalar data for a midpoint preimage

The positive weights sum to one. The unit complex phase and its two
identities will provide the conjugation relations for an explicit input.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open QuaternionicBottMatrix

def k : ℝ := Real.sqrt 2
def s : ℝ := Real.sqrt 3

theorem k_sq : k ^ 2 = 2 := Real.sq_sqrt (by norm_num)
theorem k_cube : k ^ 3 = 2 * k := by rw [pow_succ, k_sq]
theorem s_sq : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
theorem k_pos : 0 < k := by unfold k; positivity
theorem s_pos : 0 < s := by unfold s; positivity

theorem k_gt_one : 1 < k := by
  unfold k
  exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by norm_num)

def weight0 : ℝ := (k - 1) * (1 - k * s / 3)
def weight1 : ℝ := (k - 1) ^ 2
def weight2 : ℝ := (k - 1) * (1 + k * s / 3)

theorem ks_sq : (k * s) ^ 2 = 6 := by rw [mul_pow, k_sq, s_sq]; norm_num

theorem weight0_pos : 0 < weight0 := by
  have hks : k * s < 3 := by nlinarith [ks_sq, mul_pos k_pos s_pos]
  exact mul_pos (sub_pos.mpr k_gt_one) (by linarith)

theorem weight1_pos : 0 < weight1 := sq_pos_of_pos (sub_pos.mpr k_gt_one)

theorem weight2_pos : 0 < weight2 := by
  apply mul_pos (sub_pos.mpr k_gt_one)
  have hks := mul_pos k_pos s_pos
  linarith

theorem weights_sum : weight0 + weight1 + weight2 = 1 := by
  unfold weight0 weight1 weight2
  nlinarith [k_sq]

def delta : ℝ := s * weight0
def epsilon : ℝ := s * weight2

theorem delta_pos : 0 < delta := mul_pos s_pos weight0_pos
theorem epsilon_pos : 0 < epsilon := mul_pos s_pos weight2_pos

theorem delta_eq : delta = (k - 1) * (s - k) := by
  unfold delta weight0
  ring_nf
  rw [s_sq]
  ring

theorem epsilon_eq : epsilon = (k - 1) * (s + k) := by
  unfold epsilon weight2
  ring_nf
  rw [s_sq]
  ring

theorem delta_mul_epsilon : delta * epsilon = weight1 := by
  rw [delta_eq, epsilon_eq]
  unfold weight1
  calc
    _ = (k - 1) ^ 2 * (s ^ 2 - k ^ 2) := by ring
    _ = _ := by rw [s_sq, k_sq]; ring

theorem delta_sq_mul_weight2 : delta ^ 2 * weight2 = weight0 * weight1 := by
  rw [← delta_mul_epsilon]
  unfold delta epsilon
  ring

def phase : ℂ := ⟨k * (s - 1) / 4, k * (s + 1) / 4⟩

theorem phase_normSq : Complex.normSq phase = 1 := by
  simp only [phase, Complex.normSq_apply]
  ring_nf
  rw [k_sq, s_sq]
  norm_num

theorem phase_unitary : phase ∈ unitary ℂ := by
  have h : star phase * phase = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, phase_normSq]
    rfl
  exact ⟨h, by rw [mul_comm]; exact h⟩

theorem phase_sq : phase ^ 2 = targetEigenvalues 2 := by
  have ht : targetEigenvalues 2 = ⟨-s / 2, 1 / 2⟩ := by
    apply Complex.ext <;>
      norm_num [targetEigenvalues, targetAlpha, targetBeta, s, Matrix.cons_val_two]
    ring
  rw [ht]
  apply Complex.ext <;> simp [phase, pow_two, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;> norm_num [k_sq, s_sq]
  ring

theorem phase_delta : phase * (1 + Complex.I * (delta : ℂ)) = (delta : ℂ) + Complex.I := by
  rw [delta_eq]
  apply Complex.ext <;> simp [phase, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;> norm_num [k_sq, k_cube, s_sq] <;> ring

theorem phase_epsilon : phase * (1 + Complex.I * (epsilon : ℂ)) = -1 + Complex.I * epsilon := by
  rw [epsilon_eq]
  apply Complex.ext <;> simp [phase, Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;> norm_num [k_sq, k_cube, s_sq] <;> ring

theorem targetEigenvalues_product : targetEigenvalues 0 * targetEigenvalues 2 = -1 := by
  change (targetAlpha + targetBeta) * (targetAlpha - targetBeta) = -1
  calc
    _ = targetAlpha ^ 2 - targetBeta ^ 2 := by ring
    _ = -1 := target_polynomial

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
