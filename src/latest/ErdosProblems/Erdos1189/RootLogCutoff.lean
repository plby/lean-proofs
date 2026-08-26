/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A uniform cutoff estimate for the logarithmic square-root summand.
Informal source: BBMST Lemma 7.4; split below and above m^a, with a < 1.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.SqrtPrefixSums
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Erdos1189

noncomputable def rootLog (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) / Real.log n)

lemma rootLog_nonneg (n : ℕ) : 0 ≤ rootLog n := Real.sqrt_nonneg _

lemma rootLog_eq_zero {n : ℕ} (hn : n ≤ 1) : rootLog n = 0 := by
  interval_cases n <;> simp [rootLog]

lemma rootLog_cutoff {a m : ℝ} (ha : 0 < a) (hm : 1 < m) (s : ℕ) :
    rootLog s ≤ Real.sqrt (s : ℝ) / (Real.sqrt a * Real.sqrt (Real.log m)) +
      Real.sqrt (m ^ a) / Real.sqrt (Real.log 2) := by
  have hm0 := zero_lt_one.trans hm
  have hlogm := Real.log_pos hm
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hs : s ≤ 1
  · rw [rootLog_eq_zero hs]
    positivity
  · have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast (show 2 ≤ s by omega)
    have hs0 : (0 : ℝ) < s := by linarith
    have hlogs : Real.log 2 ≤ Real.log s := Real.log_le_log (by norm_num) hs2
    have hroots : 0 < Real.sqrt (Real.log s) := Real.sqrt_pos.mpr (hlog2.trans_le hlogs)
    rw [rootLog, Real.sqrt_div hs0.le]
    by_cases hlarge : m ^ a ≤ (s : ℝ)
    · have hlog : a * Real.log m ≤ Real.log s := by
        have h := Real.log_le_log (Real.rpow_pos_of_pos hm0 a) hlarge
        simpa only [Real.log_rpow hm0] using h
      have hroot : Real.sqrt a * Real.sqrt (Real.log m) ≤ Real.sqrt (Real.log s) := by
        rw [← Real.sqrt_mul ha.le]
        exact Real.sqrt_le_sqrt hlog
      have hden : 0 < Real.sqrt a * Real.sqrt (Real.log m) :=
        mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hlogm)
      have hle := div_le_div_of_nonneg_left (Real.sqrt_nonneg (s : ℝ)) hden hroot
      exact hle.trans (le_add_of_nonneg_right (by positivity))
    · have hsmall : (s : ℝ) ≤ m ^ a := le_of_not_ge hlarge
      have hle := (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hsmall)
        hroots.le).trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg (m ^ a))
          (Real.sqrt_pos.mpr hlog2) (Real.sqrt_le_sqrt hlogs))
      exact hle.trans (le_add_of_nonneg_left (by positivity))

lemma rootLog_cutoff_error_tendsto {a : ℝ} (ha : a < 1) :
    Filter.Tendsto (fun m : ℝ => Real.sqrt (m ^ a) * Real.sqrt (Real.log m) /
      (Real.sqrt m * Real.sqrt (Real.log 2))) Filter.atTop (nhds 0) := by
  have hpow : 0 < 1 - a := by linarith
  have ht := (isLittleO_log_rpow_atTop hpow).tendsto_div_nhds_zero.sqrt.div_const
    (Real.sqrt (Real.log 2))
  simp only [Real.sqrt_zero, zero_div] at ht
  apply ht.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with m hm
  have hm0 := zero_lt_one.trans hm
  have hlog := Real.log_pos hm
  have hpow0 : m ^ (1 - a) ≠ 0 := (Real.rpow_pos_of_pos hm0 _).ne'
  have hsm0 := (Real.sqrt_pos.mpr hm0).ne'
  change Real.sqrt (Real.log m / m ^ (1 - a)) / Real.sqrt (Real.log 2) = _
  rw [Real.sqrt_div hlog.le, Real.rpow_sub hm0, Real.rpow_one]
  rw [Real.sqrt_div hm0.le]
  field_simp

end Erdos1189
