/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Discrete differences of x^2/log x and x^3/log x.
Informal argument: algebra and the elementary bound 0 <= log(1+1/x) <= 1/x.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.Tau
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

namespace Erdos1189

open Filter Asymptotics
open scoped Asymptotics

noncomputable def logPower (r n : ℕ) : ℝ := (n : ℝ) ^ r / Real.log n

lemma logPower_nonneg (r n : ℕ) : 0 ≤ logPower r n := by
  exact div_nonneg (pow_nonneg (Nat.cast_nonneg n) r) (Real.log_natCast_nonneg n)

lemma log_succ_difference_bounds {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ Real.log ((n : ℝ) + 1) - Real.log n ∧
      (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hquot : (0 : ℝ) < ((n : ℝ) + 1) / n := div_pos (by positivity) hn0
  have h := Real.log_le_sub_one_of_pos hquot
  rw [Real.log_div (by positivity) hn0.ne'] at h
  have hmul := mul_le_mul_of_nonneg_left h hn0.le
  have halg : (n : ℝ) * (((n : ℝ) + 1) / n - 1) = 1 := by field_simp; ring
  refine ⟨sub_nonneg.mpr (Real.log_le_log hn0 (by linarith)), ?_⟩
  rwa [halg] at hmul

lemma tendsto_log_div_log_succ :
    Tendsto (fun n : ℕ => Real.log n / Real.log ((n : ℝ) + 1)) atTop (nhds 1) := by
  have hnorm : Tendsto (fun n : ℕ => ‖(n : ℝ)‖) atTop atTop := by
    simpa only [Real.norm_natCast] using (tendsto_natCast_atTop_atTop (R := ℝ))
  have hnat : (fun n : ℕ => (n : ℝ) + 1) ~[atTop] (fun n : ℕ => (n : ℝ)) :=
    IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm
  have hlog := hnat.log tendsto_natCast_atTop_atTop
  apply (isEquivalent_iff_tendsto_one ?_).mp hlog.symm
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))).ne'

lemma tendsto_log_difference_remainder :
    Tendsto (fun n : ℕ => (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) /
      Real.log ((n : ℝ) + 1)) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_mono
      (fun n : ℕ => show (n : ℝ) ≤ (n : ℝ) + 1 by linarith) tendsto_natCast_atTop_atTop)
  apply squeeze_zero' _ _ ht.inv_tendsto_atTop
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (log_succ_difference_bounds hn).1)
      (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n)))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [one_div, Pi.inv_apply] using
      div_le_div_of_nonneg_right (log_succ_difference_bounds hn).2
      (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n)))

lemma tendsto_logPower_two_difference :
    Tendsto (fun n : ℕ => (logPower 2 (n + 1) - logPower 2 n) / logPower 1 n)
      atTop (nhds 2) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have ht := (((tendsto_const_nhds (x := (2 : ℝ))).add hinv).mul tendsto_log_div_log_succ).sub
    tendsto_log_difference_remainder
  have ht' : Tendsto (fun n : ℕ => (2 + (n : ℝ)⁻¹) *
      (Real.log n / Real.log ((n : ℝ) + 1)) -
      (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) / Real.log ((n : ℝ) + 1))
      atTop (nhds 2) := by simpa using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  have hlog' : Real.log ((n : ℝ) + 1) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))).ne'
  dsimp [logPower]
  push_cast
  field_simp
  ring

lemma tendsto_logPower_three_difference :
    Tendsto (fun n : ℕ => (logPower 3 (n + 1) - logPower 3 n) / logPower 2 n)
      atTop (nhds 3) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hpoly : Tendsto (fun n : ℕ => 3 + 3 * (n : ℝ)⁻¹ + ((n : ℝ)⁻¹) ^ 2)
      atTop (nhds 3) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).add (hinv.pow 2)
  have ht := (hpoly.mul tendsto_log_div_log_succ).sub tendsto_log_difference_remainder
  have ht' : Tendsto (fun n : ℕ => (3 + 3 * (n : ℝ)⁻¹ + ((n : ℝ)⁻¹) ^ 2) *
      (Real.log n / Real.log ((n : ℝ) + 1)) -
      (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) / Real.log ((n : ℝ) + 1))
      atTop (nhds 3) := by simpa using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  have hlog' : Real.log ((n : ℝ) + 1) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))).ne'
  dsimp [logPower]
  push_cast
  field_simp
  ring

end Erdos1189
