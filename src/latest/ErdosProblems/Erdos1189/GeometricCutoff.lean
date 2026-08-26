/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A uniform small-measure cutoff for restrictions of product boxes.
Informal argument: split the number of fixed coordinates at a constant cutoff;
use small original measure below it and geometric decay above it.
Formal author: OpenAI Codex.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Erdos1189

open Filter

lemma exists_small_measure_cutoff {lam ε : ℝ} (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ m : ℕ, ∀ z : ℝ,
      z ≤ δ / ε ^ m → z ≤ (2 / ε) * (1 / 2 : ℝ) ^ m →
        z ≤ (lam / 16) * (35 / 48 : ℝ) ^ m := by
  have ht : Tendsto (fun m : ℕ => (24 / 35 : ℝ) ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb : 0 < lam * ε / 32 := div_pos (mul_pos hlam hε) (by norm_num)
  obtain ⟨L, hL⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 (lam * ε / 32) hb)
  let δ := min (1 / 2) ((lam / 16) * (ε * (35 / 48)) ^ L)
  have hδ : 0 < δ := lt_min (by norm_num) (mul_pos (div_pos hlam (by norm_num))
    (pow_pos (mul_pos hε (by norm_num)) _))
  refine ⟨δ, hδ, (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro m z hzSmall hzGeom
  by_cases hLm : L ≤ m
  · have hgeom := (hL m hLm).le
    have hpow : (1 / 2 : ℝ) ^ m = (24 / 35 : ℝ) ^ m * (35 / 48 : ℝ) ^ m := by
      rw [← mul_pow]
      norm_num
    calc
      z ≤ (2 / ε) * (1 / 2 : ℝ) ^ m := hzGeom
      _ = (2 / ε) * ((24 / 35 : ℝ) ^ m * (35 / 48 : ℝ) ^ m) := by rw [hpow]
      _ ≤ (2 / ε) * ((lam * ε / 32) * (35 / 48 : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hgeom (by positivity)) (by positivity)
      _ = (lam / 16) * (35 / 48 : ℝ) ^ m := by field_simp; norm_num
  · have hmL : m ≤ L := le_of_not_ge hLm
    have hePow := pow_le_pow_of_le_one hε.le hε1 hmL
    have haPow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 35 / 48)
      (by norm_num : (35 / 48 : ℝ) ≤ 1) hmL
    have hprod := mul_le_mul hePow haPow (by positivity) (by positivity)
    have hδle : δ ≤ (lam / 16) * ε ^ m * (35 / 48 : ℝ) ^ m := by
      calc
        δ ≤ (lam / 16) * (ε * (35 / 48)) ^ L := min_le_right _ _
        _ = (lam / 16) * (ε ^ L * (35 / 48 : ℝ) ^ L) := by rw [mul_pow]
        _ ≤ (lam / 16) * (ε ^ m * (35 / 48 : ℝ) ^ m) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = _ := by ring
    apply hzSmall.trans
    apply (div_le_iff₀ (pow_pos hε m)).mpr
    nlinarith [hδle]

end Erdos1189
