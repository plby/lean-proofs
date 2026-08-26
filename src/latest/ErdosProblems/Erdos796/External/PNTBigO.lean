import Mathlib
import ErdosProblems.Erdos49.PNT.MediumPNT

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
The logarithmic-rate PNT estimate from PrimeNumberTheoremAnd, revision
80c12dfd932e99874e004d65537c57ef6421ff2b, RosserSchoenfeldPrime.lean.
The surrounding table and blueprint machinery is not required here.
Apache 2.0; see LICENSE and provenance in ../README.md.
-/

open scoped Topology
open Chebyshev Finset Nat Real MeasureTheory Filter Asymptotics

namespace Erdos796.External

theorem pntBigO : (θ - id) =O[atTop] fun (x : ℝ) ↦ x / log x ^ 2 := by
  obtain ⟨c, hc⟩ := MediumPNT
  have hl : (ψ - id) =O[atTop] fun (x : ℝ) ↦ x / log x ^ 2 := by
    have h_exp : (fun x : ℝ => exp (-c * (log x) ^ (1 / 10 : ℝ))) =O[atTop]
      (fun x : ℝ => (log x) ^ (-2 : ℝ)) := by
      -- This lemma is autoformalized by Aristotle.
      have h_exp : Tendsto (fun x : ℝ => exp (-c * (log x) ^ (1 / 10 : ℝ)) * (log x) ^ 2)
        atTop (𝓝 0) := by
        suffices h_y : Tendsto (fun y : ℝ => exp (-c * y) * y ^ 20) atTop (nhds 0) by
          have h_subst : Tendsto (fun x : ℝ => exp (-c * (log x) ^ (1 / 10 : ℝ)) *
          ((log x) ^ (1 / 10 : ℝ)) ^ 20) atTop (𝓝 0) :=
          h_y.comp (tendsto_rpow_atTop (by norm_num) |> Tendsto.comp <| tendsto_log_atTop)
          refine h_subst.congr' ?_
          filter_upwards [eventually_gt_atTop 1] with x hx
          rw [← rpow_natCast, ← rpow_mul (log_nonneg hx.le)]
          norm_num
        suffices h_z : Tendsto (fun z : ℝ => exp (-z) * (z / c) ^ 20) atTop (nhds 0) by
          convert! h_z.comp (tendsto_id.const_mul_atTop hc.1) using 2
          norm_num [hc.1.ne']
        convert! (tendsto_pow_mul_exp_neg_atTop_nhds_zero 20).div_const (c ^ 20) using 2 <;> ring
      rw [isBigO_iff]
      obtain ⟨M, hM⟩ := eventually_atTop.mp (h_exp.eventually (Metric.ball_mem_nhds _ zero_lt_one))
      norm_cast
      norm_num
      refine ⟨1, Max.max M 2, fun x hx => ?_⟩
      rw [← div_eq_mul_inv, le_div_iff₀ (sq_pos_of_pos <| log_pos <| by grind [le_max_right M 2])]
      have := abs_lt.mp (hM x <| le_trans (le_max_left M 2) hx)
      norm_num at *
      nlinarith
    refine hc.2.trans ?_
    convert! (isBigO_refl (fun x : ℝ => x) atTop).mul h_exp using 2
    simp [field]
  have : θ - id = (ψ - id) + (θ - ψ) := by ring
  refine this ▸ hl.add (isBigO_iff.2 ⟨432, ?_⟩)
  filter_upwards [Ioi_mem_atTop 1] with x hx
  simp only [Pi.sub_apply, norm_eq_abs, norm_div, norm_pow, sq_abs, mul_div]
  have nonnegx : 0 ≤ x := by grind
  calc
  _ ≤ 2 * √x * log x := by rw [← neg_sub, abs_neg]; exact abs_psi_sub_theta_le_sqrt_mul_log hx.le
  _ ≤ _ := by
    rw [le_div_iff₀ (sq_pos_of_pos (log_pos hx)), mul_assoc, ← pow_succ' _ 2]
    simp only [reduceAdd]
    have : log x ^ 3 ≤ 216 * x ^ (1 / 2 : ℝ) := by
      have := rpow_le_rpow (log_nonneg hx.le) (log_le_rpow_div nonnegx
        (by grind : 0 < 1 / (6 : ℝ))) (by grind : 0 ≤ (3 : ℝ))
      simp only [rpow_ofNat, one_div, div_inv_eq_mul, mul_comm,
        mul_rpow (by grind : 0 ≤ (6 : ℝ)) (rpow_nonneg nonnegx _), ← rpow_mul nonnegx] at this
      norm_num at this
      exact this
    have := mul_le_mul_of_nonneg_left this (mul_nonneg (by simp : 0 ≤ (2 : ℝ)) (by simp : 0 ≤ √x))
    rw [← sqrt_eq_rpow, mul_comm 216 √x, ← mul_assoc, mul_assoc 2 √x √x, mul_self_sqrt nonnegx,
      ← mul_comm 216, ← mul_assoc] at this
    nth_rewrite 3 [← abs_of_nonneg nonnegx] at this
    norm_num at this
    exact this

end Erdos796.External
