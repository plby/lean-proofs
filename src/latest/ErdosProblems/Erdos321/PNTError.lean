import PrimeNumberTheoremAnd.MediumPNT

namespace Erdos321

open scoped Topology
open Chebyshev Finset Nat Real MeasureTheory Filter Asymptotics

/-- Direct consequence of `MediumPNT`: `θ(x)=x+O(x/log²x)`.  This proof is
adapted from the completed initial section of PrimeNumberTheoremAnd's
Rosser--Schoenfeld development, without importing its later unfinished files. -/
theorem theta_sub_id_isBigO :
    (θ - id) =O[atTop] fun (x : ℝ) ↦ x / log x ^ 2 := by
  obtain ⟨c, hc⟩ := MediumPNT
  have hl : (ψ - id) =O[atTop] fun (x : ℝ) ↦ x / log x ^ 2 := by
    have h_exp : (fun x : ℝ => exp (-c * (log x) ^ (1 / 10 : ℝ))) =O[atTop]
      (fun x : ℝ => (log x) ^ (-2 : ℝ)) := by
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
          convert h_z.comp (tendsto_id.const_mul_atTop hc.1) using 2
          norm_num [hc.1.ne']
        convert (tendsto_pow_mul_exp_neg_atTop_nhds_zero 20).div_const (c ^ 20) using 2 <;> ring
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
  _ ≤ 2 * √x * log x := by
    rw [← neg_sub, abs_neg]
    exact abs_psi_sub_theta_le_sqrt_mul_log hx.le
  _ ≤ _ := by
    rw [le_div_iff₀ (sq_pos_of_pos (log_pos hx)), mul_assoc, ← pow_succ' _ 2]
    simp only [reduceAdd]
    have hlog : log x ^ 3 ≤ 216 * x ^ (1 / 2 : ℝ) := by
      have h := rpow_le_rpow (log_nonneg hx.le) (log_le_rpow_div nonnegx
        (by grind : 0 < 1 / (6 : ℝ))) (by grind : 0 ≤ (3 : ℝ))
      simp only [rpow_ofNat, one_div, div_inv_eq_mul, mul_comm,
        mul_rpow (by grind : 0 ≤ (6 : ℝ)) (rpow_nonneg nonnegx _),
        ← rpow_mul nonnegx] at h
      norm_num at h
      exact h
    have h := mul_le_mul_of_nonneg_left hlog
      (mul_nonneg (by simp : 0 ≤ (2 : ℝ)) (by simp : 0 ≤ √x))
    rw [← sqrt_eq_rpow, mul_comm 216 √x, ← mul_assoc, mul_assoc 2 √x √x,
      mul_self_sqrt nonnegx, ← mul_comm 216, ← mul_assoc] at h
    nth_rewrite 3 [← abs_of_nonneg nonnegx] at h
    norm_num at h
    exact h

/-- Uniform global form: there is an absolute `C` such that
`|θ(x)-x| ≤ C x/log²x` for every `x≥2`. -/
theorem exists_theta_error_constant :
    ∃ C ≥ 0, ∀ x ≥ 2, |θ x - x| ≤ C * x / log x ^ 2 := by
  obtain ⟨c, hc⟩ := isBigO_iff'.1 theta_sub_id_isBigO
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc.2
  by_cases! hn : 2 ≤ N
  · refine ⟨max c (4 * (θ N + N)), le_max_of_le_left hc.1.le, fun x hx => ?_⟩
    by_cases! h : x ≤ N
    · suffices |θ x - x| * log x ^ 2 / x ≤ 4 * (θ N + N) from by
        rw [le_div_iff₀ (sq_pos_of_pos (log_pos (by linarith))),
          ← div_le_iff₀ (by linarith)]
        exact this.trans (le_max_right c (4 * (θ N + N)))
      have hAbs : |θ x - x| ≤ θ N + N := calc
        _ ≤ |θ x| + |x| := abs_sub _ _
        _ = θ x + x := by
          rw [abs_of_nonneg (theta_nonneg _), abs_of_nonneg (by linarith)]
        _ ≤ _ := by gcongr
      calc
      _ ≤ (θ N + N) * log x ^ 2 / x := by gcongr
      _ ≤ (θ N + N) * (x ^ (1 / 2 : ℝ) / (1 / 2)) ^ 2 / x := by
        have hcoef : 0 ≤ θ N + N := add_nonneg (theta_nonneg _) (by linarith)
        have hlog0 : 0 ≤ log x := log_nonneg (by linarith)
        have hrpow0 : 0 ≤ x ^ (1 / 2 : ℝ) / (1 / 2) := by positivity
        have hlogle : log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2) :=
          log_le_rpow_div (by linarith) (by norm_num)
        have hsq : log x ^ 2 ≤ (x ^ (1 / 2 : ℝ) / (1 / 2)) ^ 2 := by
          nlinarith [sq_nonneg (log x - x ^ (1 / 2 : ℝ) / (1 / 2))]
        apply (div_le_div_iff_of_pos_right (by linarith)).2
        exact mul_le_mul_of_nonneg_left hsq hcoef
      _ = _ := by
        rw [← sqrt_eq_rpow, div_pow, sq_sqrt (by linarith)]
        field_simp
        ring
    · simpa [abs_of_nonneg (by grind : 0 ≤ x), mul_div] using (hN x h.le).trans <|
        mul_le_mul_of_nonneg_right (le_max_left c (4 * (θ N + N))) (norm_nonneg _)
  · refine ⟨c, hc.1.le, fun x hx => ?_⟩
    simpa [abs_of_nonneg (by grind : 0 ≤ x), mul_div] using hN x (hn.le.trans hx)

#print axioms MediumPNT
#print axioms theta_sub_id_isBigO
#print axioms exists_theta_error_constant

end Erdos321
