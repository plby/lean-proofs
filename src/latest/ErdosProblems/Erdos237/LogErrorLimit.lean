import ErdosProblems.Erdos237.SieveScaleBounds

/-! A generic logarithmic error envelope negligible against the sieve scale. -/

namespace Erdos237

open Filter BoundedGaps.Maynard

theorem tendsto_normalized_of_log_bound {H : Finset ℕ} {alpha C : ℝ}
    (halpha : 0 < alpha) (hC : 0 ≤ C) (p : ℕ) (f : ℕ → ℝ)
    (hbound : ∀ᶠ N : ℕ in atTop, |f N| ≤
      C * N * Real.log (N : ℝ) ^ p /
        Real.log (N : ℝ) ^ (p + 3 * (Fintype.card H + 1) + 2)) :
    Tendsto (fun N : ℕ => f N / sieveScale H alpha N) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim : Tendsto (fun N : ℕ => C / Real.log (N : ℝ) ^ 2) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using ((tendsto_inv_atTop_zero.comp hlog).pow 2).const_mul C
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [hbound, eventually_sieveScale_pos H halpha,
    eventually_sieveScale_ge_modulus H halpha, eventually_engelsmaMaynardModulus_le_log_cube,
    hlog.eventually_gt_atTop 0, eventually_gt_atTop 0] with N hb hS hSlow hW hLN hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : (0 : ℝ) < engelsmaMaynardModulus N := by exact_mod_cast primorial_pos _
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hS]
  calc
    _ ≤ (C * N * Real.log (N : ℝ) ^ p /
        Real.log (N : ℝ) ^ (p + 3 * (Fintype.card H + 1) + 2)) /
        ((N : ℝ) / (engelsmaMaynardModulus N : ℝ) ^ (Fintype.card H + 1)) :=
      div_le_div₀ (by positivity) hb (by positivity) hSlow
    _ = C * Real.log (N : ℝ) ^ p *
        (engelsmaMaynardModulus N : ℝ) ^ (Fintype.card H + 1) /
          Real.log (N : ℝ) ^ (p + 3 * (Fintype.card H + 1) + 2) := by field_simp
    _ ≤ C * Real.log (N : ℝ) ^ p *
        (Real.log (N : ℝ) ^ 3) ^ (Fintype.card H + 1) /
          Real.log (N : ℝ) ^ (p + 3 * (Fintype.card H + 1) + 2) := by gcongr
    _ = _ := by
      simp only [pow_add, pow_mul]
      field_simp

end Erdos237
