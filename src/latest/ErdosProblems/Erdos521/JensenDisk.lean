/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Jensen root-count bounds on translated disks for Erdős 521.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.InteriorBounds
import ErdosProblems.Erdos521.PolynomialDisk

namespace Erdos521

open MeasureTheory Metric MeromorphicOn

theorem finite_zeros_card_le_log {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (c : ℂ) (hfc : f c ≠ 0) {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hM : 1 ≤ M) (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ closedBall c r ∧ f z = 0) :
    (S.card : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log (R / r) := by
  have hcard := card_le_sum_divisor_center hf c hfc r S hS
  have hcard' : (S.card : ℝ) ≤ ((∑ᶠ z, divisor f (closedBall c r) z : ℤ) : ℝ) := by
    exact_mod_cast hcard
  have hJ := (hf.mono (Set.subset_univ (closedBall c |R|))).sum_divisor_le (r := r)
    (by simpa only [abs_of_pos hr] using hr)
    (by simpa only [abs_of_pos hr, abs_of_pos (hr.trans hrR)] using hrR) hM hfc
    (by simpa only [abs_of_pos (hr.trans hrR)] using hbound)
  rw [abs_of_pos hr] at hJ
  exact hcard'.trans hJ

/-- A root count on a disk is controlled by the boundary mean square on a disk
four times as large, together with the value at the center. -/
theorem polynomial_zeros_card_le_boundary (p : Polynomial ℂ) (c : ℂ) (hc : p.eval c ≠ 0)
    {r : ℝ} (hr : 0 < r) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ closedBall c r ∧ p.eval z = 0) :
    (S.card : ℝ) * Real.log 2 ≤
      Real.log (max 1 (Real.sqrt (2 * Real.circleAverage (fun z ↦ ‖p.eval z‖ ^ 2) c (4 * r))) /
        ‖p.eval c‖) := by
  let A := Real.circleAverage (fun z ↦ ‖p.eval z‖ ^ 2) c (4 * r)
  have hA : 0 ≤ A := Real.circleAverage_nonneg_of_nonneg (fun _ _ ↦ sq_nonneg _)
  have hbound (z : ℂ) (hz : z ∈ sphere c (2 * r)) : ‖p.eval z‖ ≤ max 1 (Real.sqrt (2 * A)) := by
    have hz' : ‖z - c‖ ≤ (4 * r) / 2 := by
      have heq : ‖z - c‖ = 2 * r := by simpa only [mem_sphere, dist_eq_norm] using hz
      linarith
    have hsq := polynomial_norm_sq_le_circleAverage_disk p c (by linarith : 0 < 4 * r) hz'
    have hsqrt : ‖p.eval z‖ ≤ Real.sqrt (2 * A) :=
      (Real.le_sqrt (norm_nonneg _) (mul_nonneg (by norm_num) hA)).mpr hsq
    exact hsqrt.trans (le_max_right _ _)
  have h := finite_zeros_card_le_log (AnalyticOnNhd.eval_polynomial p) c hc hr
    (by linarith : r < 2 * r) (le_max_left 1 (Real.sqrt (2 * A))) hbound S hS
  have hratio : (2 * r) / r = (2 : ℝ) := mul_div_cancel_right₀ 2 hr.ne'
  rw [hratio] at h
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp h

/-- An exponential root-count estimate with any upper bound on the boundary
mean square. -/
theorem polynomial_zeros_pow_le (p : Polynomial ℂ) (c : ℂ) {δ B r : ℝ}
    (hδ : 0 < δ) (hcenter : δ ≤ ‖p.eval c‖) (hr : 0 < r) (hB : 1 ≤ B)
    (hboundary : Real.circleAverage (fun z ↦ ‖p.eval z‖ ^ 2) c (4 * r) ≤ B)
    (S : Finset ℂ) (hS : ∀ z ∈ S, z ∈ closedBall c r ∧ p.eval z = 0) :
    δ ^ 2 * (4 : ℝ) ^ S.card ≤ 2 * B := by
  have hc : 0 < ‖p.eval c‖ := hδ.trans_le hcenter
  have hJ := polynomial_zeros_card_le_boundary p c (norm_pos_iff.mp hc) hr S hS
  have hB₀ : 0 ≤ 2 * B := by linarith
  have hM : 1 ≤ Real.sqrt (2 * B) := by
    apply (Real.le_sqrt zero_le_one hB₀).mpr
    nlinarith
  have hmax : max 1 (Real.sqrt (2 * Real.circleAverage (fun z ↦ ‖p.eval z‖ ^ 2) c (4 * r))) ≤
      Real.sqrt (2 * B) := by
    exact max_le hM (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hboundary (by norm_num)))
  have hpow : (2 : ℝ) ^ S.card ≤
      max 1 (Real.sqrt (2 * Real.circleAverage (fun z ↦ ‖p.eval z‖ ^ 2) c (4 * r))) /
        ‖p.eval c‖ := by
    rw [← Real.log_pow] at hJ
    exact (Real.log_le_log_iff (by positivity) (div_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hc)).mp hJ
  have hmul : (2 : ℝ) ^ S.card * ‖p.eval c‖ ≤ Real.sqrt (2 * B) :=
    ((le_div_iff₀ hc).mp hpow).trans hmax
  have hδmul : δ * (2 : ℝ) ^ S.card ≤ Real.sqrt (2 * B) := by
    calc
      δ * (2 : ℝ) ^ S.card ≤ ‖p.eval c‖ * (2 : ℝ) ^ S.card :=
        mul_le_mul_of_nonneg_right hcenter (by positivity)
      _ = (2 : ℝ) ^ S.card * ‖p.eval c‖ := mul_comm _ _
      _ ≤ _ := hmul
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ δ * (2 : ℝ) ^ S.card) hδmul 2
  rw [Real.sq_sqrt hB₀, mul_pow, ← pow_mul, Nat.mul_comm S.card 2, pow_mul] at hsq
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hsq
  exact hsq

end Erdos521
