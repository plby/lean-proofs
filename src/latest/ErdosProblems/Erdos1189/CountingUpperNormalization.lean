/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Normalizing the finite counting upper bound and removing all encoding losses.
Informal source: the final asymptotic estimates in BBMST Section 7.2.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountingUpperFinite
import ErdosProblems.Erdos1189.LogPowerDifferences

namespace Erdos1189

open Filter

lemma sqrt_log_div_sqrt_tendsto_zero :
    Tendsto (fun k : ℕ => Real.sqrt (Real.log k) / Real.sqrt k) atTop (nhds 0) := by
  have ht := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.sqrt.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simp only [Real.sqrt_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hlog : 0 ≤ Real.log k := Real.log_natCast_nonneg k
  exact Real.sqrt_div hlog (k : ℝ)

lemma log_sqrt_log_div_sqrt_tendsto_zero :
    Tendsto (fun k : ℕ => Real.log k * Real.sqrt (Real.log k) / Real.sqrt k)
      atTop (nhds 0) := by
  have ht := (Real.isLittleO_pow_log_id_atTop (n := 3)).tendsto_div_nhds_zero.sqrt.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simp only [Real.sqrt_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hlog : 0 ≤ Real.log k := Real.log_natCast_nonneg k
  change Real.sqrt (Real.log k ^ 3 / (k : ℝ)) = _
  rw [Real.sqrt_div (pow_nonneg hlog 3), pow_succ, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq hlog]

lemma log_succ_sqrt_log_div_sqrt_tendsto_zero :
    Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) * Real.sqrt (Real.log k) / Real.sqrt k)
      atTop (nhds 0) := by
  have hratio := tendsto_log_div_log_succ.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simp only [inv_one, inv_div] at hratio
  have ht := hratio.mul log_sqrt_log_div_sqrt_tendsto_zero
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hlog : Real.log k ≠ 0 := (Real.log_pos (by
    exact_mod_cast (show 1 < k by omega))).ne'
  change (Real.log ((k : ℝ) + 1) / Real.log k) *
    (Real.log k * Real.sqrt (Real.log k) / Real.sqrt k) = _
  field_simp

lemma countingEntropyError_normalized (C : ℝ) (T : ℕ) :
    Tendsto (fun k : ℕ => countingEntropyError C T k * Real.sqrt (Real.log k) / Real.sqrt k)
      atTop (nhds 0) := by
  have ht := (sqrt_log_div_sqrt_tendsto_zero.const_mul
    (C + Real.log 2 + T * Real.log ((T : ℝ) + 1))).add
      (log_succ_sqrt_log_div_sqrt_tendsto_zero.const_mul (T : ℝ))
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun k => by dsimp only [countingEntropyError]; ring

noncomputable def countingUpperCoefficient (a b η : ℝ) : ℝ :=
  b * (2 / (3 * Real.sqrt a)) * (1 + η) * Real.sqrt (1 + η)

lemma frameCodeBound_normalized {a : ℝ} (ha1 : a < 1) (b C : ℝ) (T : ℕ)
    {η : ℝ} (hη : 0 ≤ η) :
    Tendsto (fun k : ℕ =>
      frameCodeBound a b (countingEntropyError C T k) k ((1 + η) * k) *
        Real.sqrt (Real.log k) / ((k : ℝ) * Real.sqrt k))
      atTop (nhds (countingUpperCoefficient a b η)) := by
  have herr := (rootLog_cutoff_error_tendsto ha1).comp tendsto_natCast_atTop_atTop
  have ht := ((herr.const_mul (b * (1 + η))).add
    ((countingEntropyError_normalized C T).const_mul (1 + η))).const_add
      (countingUpperCoefficient a b η)
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hsk : Real.sqrt k ≠ 0 := (Real.sqrt_pos.mpr (by
    exact_mod_cast (show 0 < k by omega))).ne'
  have hsl : Real.sqrt (Real.log k) ≠ 0 := (Real.sqrt_pos.mpr
    (Real.log_pos (by exact_mod_cast (show 1 < k by omega)))).ne'
  dsimp only [frameCodeBound, countingUpperCoefficient, Function.comp_apply]
  rw [Real.sqrt_mul (show 0 ≤ 1 + η by linarith)]
  field_simp
  ring

lemma counting_encoding_loss_normalized :
    Tendsto (fun k : ℕ =>
      (((k : ℝ) + 1) * Real.log 2 + (2 * k + 1) * Real.log ((k : ℝ) + 1)) *
        Real.sqrt (Real.log k) / ((k : ℝ) * Real.sqrt k)) atTop (nhds 0) := by
  have hinv := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have ht := (((hinv.const_add 1).mul_const (Real.log 2)).mul
    sqrt_log_div_sqrt_tendsto_zero).add ((hinv.const_add 2).mul
      log_succ_sqrt_log_div_sqrt_tendsto_zero)
  simp only [add_zero, mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  change ((1 + (k : ℝ)⁻¹) * Real.log 2) *
    (Real.sqrt (Real.log k) / Real.sqrt k) +
      (2 + (k : ℝ)⁻¹) *
        (Real.log ((k : ℝ) + 1) * Real.sqrt (Real.log k) / Real.sqrt k) = _
  field_simp

theorem countingUpperExponent_normalized {a : ℝ} (ha1 : a < 1) (b C : ℝ) (T : ℕ)
    {η : ℝ} (hη : 0 ≤ η) :
    Tendsto (fun k : ℕ => countingUpperExponent a b C T η k * Real.sqrt (Real.log k) /
      ((k : ℝ) * Real.sqrt k)) atTop (nhds (countingUpperCoefficient a b η)) := by
  have ht := counting_encoding_loss_normalized.add (frameCodeBound_normalized ha1 b C T hη)
  simp only [zero_add] at ht
  apply ht.congr'
  exact Eventually.of_forall fun k => by dsimp only [countingUpperExponent]; ring

end Erdos1189
