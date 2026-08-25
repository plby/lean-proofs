import ErdosProblems.Erdos964.LogPowerMeanLimit
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Transferring logarithmic means through an absolutely summable convolution

Only absolute summability of the correction is needed. The normalized
cumulative kernels have a uniform bound and converge at every fixed divisor.
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem tendsto_log_div_fixed_ratio (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.log (x / a) / Real.log x) atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => 1 - Real.log a / Real.log x) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      tendsto_const_nhds.sub (Real.tendsto_log_atTop.const_div_atTop (Real.log a))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hlog
  rw [Real.log_div hx.ne' ha.ne']
  field_simp

theorem tendsto_log_mean_scaled_argument (G : ℝ → ℝ) (c : ℝ) (m : ℕ)
    (hG : Tendsto (fun x : ℝ => G x / (Real.log x) ^ m) atTop (𝓝 c))
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => G (x / a) / (Real.log x) ^ m) atTop (𝓝 c) := by
  have hquot : Tendsto (fun x : ℝ => x / a) atTop atTop := tendsto_id.atTop_div_const ha
  have hprod := (hG.comp hquot).mul ((tendsto_log_div_fixed_ratio a ha).pow m)
  simp only [one_pow, mul_one] at hprod
  apply hprod.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp hquot).eventually
    (eventually_gt_atTop (0 : ℝ))] with x hx
  change 0 < Real.log (x / a) at hx
  simp only [Function.comp_apply]
  rw [div_pow]
  field_simp [hx.ne']

theorem tendsto_log_mean_convolution (f g : ArithmeticFunction ℝ) (m : ℕ) (c B : ℝ)
    (hB : 0 ≤ B) (hf : Summable (fun n : ℕ => |f n|))
    (hlimit : Tendsto (fun x : ℝ => abelCumulative g x / (Real.log x) ^ m) atTop (𝓝 c))
    (hbound : ∀ x : ℝ, 1 ≤ x → |abelCumulative g x| ≤ B * (1 + Real.log x) ^ m) :
    Tendsto (fun x : ℝ => abelCumulative (f * g : ArithmeticFunction ℝ) x /
      (Real.log x) ^ m) atTop (𝓝 ((∑' n : ℕ, f n) * c)) := by
  classical
  let F : ℝ → ℕ → ℝ := fun x n => if n ∈ Finset.Ioc 0 ⌊x⌋₊ then
    f n * abelCumulative g (x / n) / (Real.log x) ^ m else 0
  have hpoint (n : ℕ) : Tendsto (fun x : ℝ => F x n) atTop (𝓝 (f n * c)) := by
    by_cases hn : n = 0
    · subst n
      simp only [F, Finset.mem_Ioc, lt_self_iff_false, false_and, ite_false,
        ArithmeticFunction.map_zero, zero_mul]
      exact tendsto_const_nhds
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have h := (tendsto_log_mean_scaled_argument (abelCumulative g) c m hlimit n hnpos).const_mul
        (f n)
      apply h.congr'
      filter_upwards [eventually_ge_atTop (n : ℝ)] with x hx
      have hmem : n ∈ Finset.Ioc 0 ⌊x⌋₊ := Finset.mem_Ioc.mpr
        ⟨Nat.pos_of_ne_zero hn, (Nat.le_floor_iff (hnpos.le.trans hx)).mpr hx⟩
      dsimp only [F]
      rw [if_pos hmem]
      ring
  have hdom : ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, ‖F x n‖ ≤ |f n| * (B * 2 ^ m) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hlog n
    dsimp only [F]
    split_ifs with hn
    · obtain ⟨hq, hqlog, hqlogle⟩ := harmonic_quotient_log_bounds x hx n hn
      have hlogpos : 0 < Real.log x := zero_lt_one.trans_le hlog
      have hkernel : |abelCumulative g (x / n)| / (Real.log x) ^ m ≤ B * 2 ^ m := by
        calc
          _ ≤ B * (1 + Real.log (x / n)) ^ m / (Real.log x) ^ m :=
            div_le_div_of_nonneg_right (hbound _ hq) (by positivity)
          _ ≤ B * (2 * Real.log x) ^ m / (Real.log x) ^ m :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by linarith) (by linarith) m) hB) (by positivity)
          _ = B * 2 ^ m := by rw [mul_pow]; field_simp
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (pow_pos hlogpos m), mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hkernel (abs_nonneg _)
    · simp only [norm_zero]
      positivity
  have hsum := tendsto_tsum_of_dominated_convergence (hf.mul_right (B * 2 ^ m)) hpoint hdom
  have heq (x : ℝ) : (∑' n : ℕ, F x n) =
      abelCumulative (f * g : ArithmeticFunction ℝ) x / (Real.log x) ^ m := by
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) (fun n hn => by simp only [F, if_neg hn])]
    calc
      _ = (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n * abelCumulative g (x / n)) / (Real.log x) ^ m := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro n hn
        exact if_pos hn
      _ = _ := by rw [abelCumulative_convolution]
  simpa only [heq, tsum_mul_right] using hsum

end Erdos964
