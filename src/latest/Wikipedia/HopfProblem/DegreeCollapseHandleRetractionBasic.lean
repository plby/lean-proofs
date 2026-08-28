import Wikipedia.SmoothSixDPoincare.MorseHandleModel
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic

/-!
# An explicit handle retraction: coordinate estimates

A product of closed disks retracts onto its attaching face together with
its core disk. The denominator stays at least one half, including in
zero-dimensional factors. These formulas will remove the positive disk
factor from the native Morse homotopy attachments.
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.DegreeCollapse.Handle

open Wikipedia.SmoothSixDPoincare.MorseHandle

variable {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]

abbrev Space := UnitDisk N × UnitDisk P

def denominator (z : Space (N := N) (P := P)) : ℝ :=
  max ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)

theorem half_le_denominator (z : Space (N := N) (P := P)) :
    (1 / 2 : ℝ) ≤ denominator z := by
  have hv : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.property
  have hd := le_max_right ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)
  change (1 / 2 : ℝ) ≤ max ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)
  linarith

theorem denominator_pos (z : Space (N := N) (P := P)) : 0 < denominator z :=
  lt_of_lt_of_le (by norm_num) (half_le_denominator z)

theorem denominator_le_one (z : Space (N := N) (P := P)) : denominator z ≤ 1 := by
  apply max_le (mem_closedBall_zero_iff.mp z.1.property)
  linarith [norm_nonneg (z.2 : P)]

def positiveMultiplier (z : Space (N := N) (P := P)) : ℝ :=
  (2 * denominator z + ‖(z.2 : P)‖ - 2) / (‖(z.2 : P)‖ * denominator z)

theorem positiveMultiplier_nonneg (z : Space (N := N) (P := P)) :
    0 ≤ positiveMultiplier z := by
  apply div_nonneg
  · have hd := le_max_right ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)
    change 0 ≤ 2 * max ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2) + ‖(z.2 : P)‖ - 2
    linarith
  · exact mul_nonneg (norm_nonneg _) (denominator_pos z).le

theorem positiveMultiplier_le_one (z : Space (N := N) (P := P)) :
    positiveMultiplier z ≤ 1 := by
  by_cases hv : (z.2 : P) = 0
  · simp [positiveMultiplier, hv]
  · apply (div_le_one (mul_pos (norm_pos_iff.mpr hv) (denominator_pos z))).mpr
    have hb : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.property
    have hprod := mul_nonneg (sub_nonneg.mpr (denominator_le_one z))
      (show 0 ≤ 2 - ‖(z.2 : P)‖ by linarith)
    nlinarith

variable [NormedSpace ℝ N] [NormedSpace ℝ P]

def negative (z : Space (N := N) (P := P)) : N := (denominator z)⁻¹ • (z.1 : N)

def positive (z : Space (N := N) (P := P)) : P := positiveMultiplier z • (z.2 : P)

omit [NormedSpace ℝ P] in
theorem norm_negative_le_one (z : Space (N := N) (P := P)) : ‖negative z‖ ≤ 1 := by
  rw [negative, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (denominator_pos z).le)]
  have h := mul_le_mul_of_nonneg_left
    (le_max_left ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2))
    (inv_nonneg.mpr (denominator_pos z).le)
  exact h.trans_eq (inv_mul_cancel₀ (denominator_pos z).ne')

omit [NormedSpace ℝ N] in
theorem norm_positive_le (z : Space (N := N) (P := P)) : ‖positive z‖ ≤ ‖(z.2 : P)‖ := by
  rw [positive, norm_smul, Real.norm_of_nonneg (positiveMultiplier_nonneg z)]
  exact (mul_le_mul_of_nonneg_right (positiveMultiplier_le_one z) (norm_nonneg _)).trans_eq
    (one_mul _)

omit [NormedSpace ℝ N] in
theorem positive_eq_zero_of_snd_eq_zero (z : Space (N := N) (P := P))
    (hz : (z.2 : P) = 0) : positive z = 0 := by
  simp only [positive, hz, smul_zero]

omit [NormedSpace ℝ N] [NormedSpace ℝ P] in
theorem denominator_eq_one_of_snd_eq_zero (z : Space (N := N) (P := P))
    (hz : (z.2 : P) = 0) : denominator z = 1 := by
  simp only [denominator, hz, norm_zero, zero_div, sub_zero]
  exact max_eq_right (mem_closedBall_zero_iff.mp z.1.property)

end Wikipedia.HopfProblem.DegreeCollapse.Handle
