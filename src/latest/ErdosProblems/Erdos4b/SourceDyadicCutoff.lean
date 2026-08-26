/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicScales

/-!
# The slow pre-sieve cutoff and small companion scale

The cutoff is `r / 100`, so its primorial is negligible compared with
the dyadic iterated-log scale. No prime-distribution assertion is used.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped Topology

theorem self_le_log_dyadicAmbientScale (a r : ℕ) :
    (r : ℝ) ≤ Real.log (dyadicAmbientScale a r) := by
  have hc : (2 : ℝ) ≤ core r := by exact_mod_cast two_le_dyadicCore r
  have hl := half_le_log_two
  have hrest : 1 ≤ (core r : ℝ) * Real.log 2 := by nlinarith
  have hrestPos : 0 < (core r : ℝ) * Real.log 2 := by linarith
  have hlogrest := Real.log_nonneg hrest
  have hform : dyadicAmbientScale a r =
      (2 : ℝ) ^ (a + 2 * r) * ((core r : ℝ) * Real.log 2) := by
    rw [dyadicAmbientScale_eq]
    simp only [primaryExponent, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]
  rw [hform, Real.log_mul (by positivity) hrestPos.ne', Real.log_pow]
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) a]

theorem sourcePreSieveCutoff_le_log_ambient_add_one (a r : ℕ) :
    (sourcePreSieveCutoff r : ℝ) ≤ Real.log (dyadicAmbientScale a r + 1) := by
  have hw : sourcePreSieveCutoff r ≤ r := Nat.div_le_self r 100
  have hV : 0 < dyadicAmbientScale a r :=
    lt_of_lt_of_le (by norm_num) (one_le_dyadicAmbientScale a r)
  exact (show (sourcePreSieveCutoff r : ℝ) ≤ r by exact_mod_cast hw).trans
    ((self_le_log_dyadicAmbientScale a r).trans (Real.log_le_log hV (by linarith)))

theorem tendsto_sourcePreSieveCutoff_atTop : Tendsto sourcePreSieveCutoff atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (N * 100)] with r hr
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr hr

theorem sourcePreSieveCutoff_mul_hundred_le (r : ℕ) :
    (sourcePreSieveCutoff r : ℝ) * 100 ≤ r := by
  exact_mod_cast Nat.div_mul_le_self r 100

theorem eventually_sourcePreSieve_primorial_le_exp_ambient (a : ℕ) :
    ∀ᶠ r in atTop,
      (primorial (sourcePreSieveCutoff r) : ℝ) ≤ Real.exp (dyadicAmbientScale a r / 8) := by
  filter_upwards [tendsto_sourcePreSieveCutoff_atTop.eventually eventually_log_primorial_lt_two_mul]
    with r hr
  have hE : (r : ℝ) ≤ primaryExponent a r := by exact_mod_cast self_le_primaryExponent a r
  have hV : (r : ℝ) / 2 ≤ dyadicAmbientScale a r := by
    rw [dyadicAmbientScale_eq]
    nlinarith [half_le_log_two, Nat.cast_nonneg (α := ℝ) r]
  have hbound : Real.log (primorial (sourcePreSieveCutoff r)) ≤ dyadicAmbientScale a r / 8 := by
    linarith [sourcePreSieveCutoff_mul_hundred_le r]
  exact (Real.log_le_iff_le_exp
    (by exact_mod_cast primorial_pos (sourcePreSieveCutoff r))).mp hbound

theorem eventually_dyadicCompanionScale_small (a K : ℕ) :
    ∀ᶠ r in atTop, (K : ℝ) * dyadicCompanionScale r ≤ dyadicAmbientScale a r / 40 := by
  have h := (tendsto_dyadicCompanionScale_div_ambient_zero a).const_mul (K : ℝ)
  have hlim : Tendsto (fun r ↦ (K : ℝ) * (dyadicCompanionScale r / dyadicAmbientScale a r))
      atTop (𝓝 0) := by simpa only [mul_zero] using h
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 40))] with r hr
  have hV : 0 < dyadicAmbientScale a r :=
    lt_of_lt_of_le (by norm_num) (one_le_dyadicAmbientScale a r)
  rw [← mul_div_assoc] at hr
  have hb := (div_lt_iff₀ hV).mp hr
  linarith

theorem tendsto_sourcePreSieve_primorial_div_twoPow_zero :
    Tendsto (fun r ↦ (primorial (sourcePreSieveCutoff r) : ℝ) / (2 : ℝ) ^ r) atTop (𝓝 0) := by
  have hlim : Tendsto (fun r : ℕ ↦ Real.exp (-((r : ℝ) / 4))) atTop (𝓝 0) := by
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 4))
  apply squeeze_zero' (Eventually.of_forall fun r ↦ by positivity) _ hlim
  filter_upwards [tendsto_sourcePreSieveCutoff_atTop.eventually eventually_log_primorial_lt_two_mul]
    with r hr
  have hP : (primorial (sourcePreSieveCutoff r) : ℝ) ≤ Real.exp ((r : ℝ) / 50) := by
    apply (Real.log_le_iff_le_exp (by exact_mod_cast primorial_pos (sourcePreSieveCutoff r))).mp
    linarith [sourcePreSieveCutoff_mul_hundred_le r]
  calc
    _ ≤ Real.exp ((r : ℝ) / 50) / (2 : ℝ) ^ r :=
      div_le_div_of_nonneg_right hP (by positivity)
    _ = Real.exp ((r : ℝ) / 50 - (r : ℝ) * Real.log 2) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_left half_le_log_two (Nat.cast_nonneg (α := ℝ) r)])

end

end Erdos4b.SmoothParameters
