import Wikipedia.HopfProblem.DegreeCollapseMorseModelExit
import Mathlib.Topology.Order.IntermediateValue

/-!
# Controlled exits at the fixed quadratic levels

Every sufficiently small point outside the pure negative plane reaches the
upper level `r²` in backward time. The entire intervening orbit stays in the
closed block of radius `2r`, and its negative coordinate stays no larger
than the original one. Coordinate swap gives the dual forward statement.
-/

noncomputable section

open Set Function Metric
open scoped Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem exists_backward_morse_quadratic_level_exit {r : ℝ} (hr : 0 < r) {z : N × P}
    (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.2 ≠ 0) :
    ∃ s : ℝ, s < 0 ∧
      MorseHandle.quadratic (MorseHandle.descentFlow s z) = r ^ 2 ∧
      (∀ t ∈ Icc s (0 : ℝ), MorseHandle.descentFlow t z ∈
        closedBall (0 : N) (2 * r) ×ˢ closedBall (0 : P) (2 * r)) ∧
      ‖(MorseHandle.descentFlow s z).1‖ ≤ ‖z.1‖ := by
  let R := 3 * r / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hR : 0 < R := hr.trans hrR
  let T := -Real.log (R / ‖z.2‖)
  have hn : 0 < ‖z.2‖ := norm_pos_iff.mpr hne
  have hratio : 1 < R / ‖z.2‖ := (one_lt_div hn).mpr (hzp.trans hrR)
  have hT : T < 0 := neg_neg_of_pos (Real.log_pos hratio)
  have hexp : Real.exp (-T) = R / ‖z.2‖ := by
    dsimp [T]
    rw [neg_neg, Real.exp_log (div_pos hR hn)]
  have hnorm : ‖(MorseHandle.descentFlow T z).2‖ = R := by
    rw [MorseHandle.norm_descentFlow_snd, hexp]
    exact div_mul_cancel₀ R hn.ne'
  have hsmall (t : ℝ) (ht : t ≤ 0) : ‖(MorseHandle.descentFlow t z).1‖ ≤ ‖z.1‖ := by
    rw [MorseHandle.norm_descentFlow_fst]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ht)
  have hstay (t : ℝ) (ht : t ∈ Icc T (0 : ℝ)) : MorseHandle.descentFlow t z ∈
      closedBall (0 : N) (2 * r) ×ˢ closedBall (0 : P) (2 * r) := by
    constructor
    · exact mem_closedBall_zero_iff.mpr ((hsmall t ht.2).trans (by linarith))
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_snd]
      calc
        Real.exp (-t) * ‖z.2‖ ≤ Real.exp (-T) * ‖z.2‖ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg ht.1)) (norm_nonneg _)
        _ = R := by rw [hexp, div_mul_cancel₀ R hn.ne']
        _ ≤ 2 * r := by dsimp [R]; linarith
  have hheightT : r ^ 2 < MorseHandle.quadratic (MorseHandle.descentFlow T z) := by
    change r ^ 2 < -‖(MorseHandle.descentFlow T z).1‖ ^ 2 +
      ‖(MorseHandle.descentFlow T z).2‖ ^ 2
    rw [hnorm]
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr ((hsmall T hT.le).trans_lt hzn)
    dsimp [R]
    nlinarith [sq_pos_of_pos hr]
  have hheight0 : MorseHandle.quadratic (MorseHandle.descentFlow 0 z) < r ^ 2 := by
    rw [Flow.map_zero_apply]
    change -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r ^ 2
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hzp
    nlinarith [sq_nonneg ‖z.1‖]
  have hc : Continuous (fun t : ℝ => MorseHandle.quadratic (MorseHandle.descentFlow t z)) := by
    change Continuous (fun t : ℝ => -‖(MorseHandle.descentFlow t z).1‖ ^ 2 +
      ‖(MorseHandle.descentFlow t z).2‖ ^ 2)
    exact (((MorseHandle.descentFlow.continuous continuous_id continuous_const).fst.norm.pow 2).neg).add
      ((MorseHandle.descentFlow.continuous continuous_id continuous_const).snd.norm.pow 2)
  obtain ⟨s, hs, hlevel⟩ := intermediate_value_Icc' hT.le hc.continuousOn
    (show r ^ 2 ∈ Icc (MorseHandle.quadratic (MorseHandle.descentFlow 0 z))
      (MorseHandle.quadratic (MorseHandle.descentFlow T z)) from ⟨hheight0.le, hheightT.le⟩)
  have hs0 : s < 0 := lt_of_le_of_ne hs.2 (by
    intro heq
    rw [heq] at hlevel
    linarith)
  exact ⟨s, hs0, hlevel, fun t ht => hstay t ⟨hs.1.trans ht.1, ht.2⟩, hsmall s hs0.le⟩

theorem morse_descentFlow_swap (t : ℝ) (z : N × P) :
    MorseHandle.descentFlow t z.swap = (MorseHandle.descentFlow (-t) z).swap := by
  simp only [MorseHandle.descentFlow, neg_neg, Prod.swap]

theorem morse_quadratic_swap (z : N × P) :
    MorseHandle.quadratic z.swap = -MorseHandle.quadratic z := by
  change -‖z.2‖ ^ 2 + ‖z.1‖ ^ 2 = -(-‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
  ring

theorem exists_forward_morse_quadratic_level_exit {r : ℝ} (hr : 0 < r) {z : N × P}
    (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.1 ≠ 0) :
    ∃ s : ℝ, 0 < s ∧
      MorseHandle.quadratic (MorseHandle.descentFlow s z) = -(r ^ 2) ∧
      (∀ t ∈ Icc (0 : ℝ) s, MorseHandle.descentFlow t z ∈
        closedBall (0 : N) (2 * r) ×ˢ closedBall (0 : P) (2 * r)) ∧
      ‖(MorseHandle.descentFlow s z).2‖ ≤ ‖z.2‖ := by
  obtain ⟨s, hs, hlevel, hstay, hsmall⟩ :=
    exists_backward_morse_quadratic_level_exit (z := z.swap) hr hzp hzn hne
  rw [morse_descentFlow_swap, morse_quadratic_swap] at hlevel
  rw [morse_descentFlow_swap] at hsmall
  refine ⟨-s, neg_pos.mpr hs, by linarith, ?_, hsmall⟩
  intro t ht
  have hh := hstay (-t) (show -t ∈ Icc s (0 : ℝ) from ⟨by linarith [ht.2], neg_nonpos.mpr ht.1⟩)
  rw [morse_descentFlow_swap, neg_neg] at hh
  exact ⟨hh.2, hh.1⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
