import Wikipedia.SmoothSixDPoincare.MorseModelFlow
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite Morse-block exits in expanding directions

A nonzero expanding coordinate reaches the boundary of a controlled
product block in finite logarithmic time. The other block stays strictly
inside. The model height at the exit is therefore strictly below the
critical height in forward time, or strictly above it in backward time.
-/

noncomputable section

open Set Function Metric
open scoped Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The forward expanding coordinate constructs a finite exit below the
critical height, with the entire preceding model trajectory in the block. -/
theorem exists_forward_morse_model_exit {r : ℝ} (hr : 0 < r) {z : N × P}
    (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.1 ≠ 0) :
    ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Icc (0 : ℝ) T, MorseHandle.descentFlow t z ∈
        closedBall (0 : N) r ×ˢ closedBall (0 : P) r) ∧
      MorseHandle.quadratic (MorseHandle.descentFlow T z) < 0 := by
  let T := Real.log (r / ‖z.1‖)
  have hn : 0 < ‖z.1‖ := norm_pos_iff.mpr hne
  have hratio : 1 < r / ‖z.1‖ := (one_lt_div hn).mpr hzn
  have hT : 0 < T := Real.log_pos hratio
  have hexp : Real.exp T = r / ‖z.1‖ := Real.exp_log (div_pos hr hn)
  have hnorm : ‖(MorseHandle.descentFlow T z).1‖ = r := by
    rw [MorseHandle.norm_descentFlow_fst, hexp]
    exact div_mul_cancel₀ r hn.ne'
  have hsmall : ‖(MorseHandle.descentFlow T z).2‖ < r :=
    (MorseHandle.norm_snd_descentFlow_le hT.le z).trans_lt hzp
  refine ⟨T, hT, ?_, ?_⟩
  · intro t ht
    constructor
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_fst]
      calc
        Real.exp t * ‖z.1‖ ≤ Real.exp T * ‖z.1‖ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht.2) (norm_nonneg _)
        _ = r := by rw [hexp, div_mul_cancel₀ r hn.ne']
    · exact mem_closedBall_zero_iff.mpr
        ((MorseHandle.norm_snd_descentFlow_le ht.1 z).trans hzp.le)
  · change -‖(MorseHandle.descentFlow T z).1‖ ^ 2 +
      ‖(MorseHandle.descentFlow T z).2‖ ^ 2 < 0
    rw [hnorm]
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hsmall
    linarith

/-- The backward expanding coordinate constructs a finite exit above the
critical height, with the entire intervening model trajectory in the block. -/
theorem exists_backward_morse_model_exit {r : ℝ} (hr : 0 < r) {z : N × P}
    (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.2 ≠ 0) :
    ∃ T : ℝ, T < 0 ∧
      (∀ t ∈ Icc T (0 : ℝ), MorseHandle.descentFlow t z ∈
        closedBall (0 : N) r ×ˢ closedBall (0 : P) r) ∧
      0 < MorseHandle.quadratic (MorseHandle.descentFlow T z) := by
  let T := -Real.log (r / ‖z.2‖)
  have hn : 0 < ‖z.2‖ := norm_pos_iff.mpr hne
  have hratio : 1 < r / ‖z.2‖ := (one_lt_div hn).mpr hzp
  have hT : T < 0 := neg_neg_of_pos (Real.log_pos hratio)
  have hexp : Real.exp (-T) = r / ‖z.2‖ := by
    dsimp [T]
    rw [neg_neg, Real.exp_log (div_pos hr hn)]
  have hnorm : ‖(MorseHandle.descentFlow T z).2‖ = r := by
    rw [MorseHandle.norm_descentFlow_snd, hexp]
    exact div_mul_cancel₀ r hn.ne'
  have hsmall (t : ℝ) (ht : t ≤ 0) : ‖(MorseHandle.descentFlow t z).1‖ < r := by
    rw [MorseHandle.norm_descentFlow_fst]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ht)).trans_lt hzn
  refine ⟨T, hT, ?_, ?_⟩
  · intro t ht
    constructor
    · exact mem_closedBall_zero_iff.mpr (hsmall t ht.2).le
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_snd]
      calc
        Real.exp (-t) * ‖z.2‖ ≤ Real.exp (-T) * ‖z.2‖ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg ht.1)) (norm_nonneg _)
        _ = r := by rw [hexp, div_mul_cancel₀ r hn.ne']
  · change 0 < -‖(MorseHandle.descentFlow T z).1‖ ^ 2 +
      ‖(MorseHandle.descentFlow T z).2‖ ^ 2
    rw [hnorm]
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr (hsmall T hT.le)
    linarith

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
