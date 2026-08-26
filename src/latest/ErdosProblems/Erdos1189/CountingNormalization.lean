/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Converting the frame-parameter entropy constant to the cardinality normalization.
Informal source: BBMST equations (19) and (21).
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountingLoss

namespace Erdos1189

open Filter

lemma entropy_normalization_eq {x n : ℝ} (hx : 1 < x) (hn : 0 < n) :
    entropyScale x * Real.sqrt (Real.log n) / (n * Real.sqrt n) =
      Real.sqrt (Real.log n / Real.log x) /
        ((n / realLogPower 2 x) * Real.sqrt (n / realLogPower 2 x)) := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl := Real.log_pos hx
  have hl0 := hl.ne'
  have hsl0 := (Real.sqrt_pos.mpr hl).ne'
  have hsn0 := (Real.sqrt_pos.mpr hn).ne'
  rw [Real.sqrt_div' _ hl.le, Real.sqrt_div hn.le]
  unfold realLogPower entropyScale
  rw [Real.sqrt_div (sq_nonneg x), Real.sqrt_sq (zero_lt_one.trans hx).le]
  field_simp
  rw [Real.sq_sqrt hl.le]
  ring

lemma entropy_normalization_constant :
    Real.sqrt 2 / ((tau / 2) * Real.sqrt (tau / 2)) = 4 / (tau * Real.sqrt tau) := by
  have ht0 := tau_pos.ne'
  have hs0 := (Real.sqrt_pos.mpr tau_pos).ne'
  rw [Real.sqrt_div tau_pos.le]
  field_simp
  norm_num

lemma entropy_normalization_limit :
    Tendsto (fun x : ℝ => entropyScale x * Real.sqrt (Real.log (countingSize x)) /
      ((countingSize x : ℝ) * Real.sqrt (countingSize x)))
      atTop (nhds (4 / (tau * Real.sqrt tau))) := by
  have hc : (tau / 2) * Real.sqrt (tau / 2) ≠ 0 := by
    exact (mul_pos (div_pos tau_pos (by norm_num))
      (Real.sqrt_pos.mpr (div_pos tau_pos (by norm_num)))).ne'
  have ht := countingSize_log_ratio.sqrt.div
    (countingSize_asymptotic.mul countingSize_asymptotic.sqrt) hc
  rw [entropy_normalization_constant] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (entropy_normalization_eq hx (by exact_mod_cast countingSize_pos x)).symm

lemma eventually_mul_lower_of_tendsto {α : Type*} {l : Filter α}
    {f g : α → ℝ} {A c b : ℝ}
    (hA : 0 < A) (hc : 0 < c)
    (hf : ∀ a < A, ∀ᶠ x in l, a < f x)
    (hg : Tendsto g l (nhds c)) (hb : b < A * c) :
    ∀ᶠ x in l, b < f x * g x := by
  have hb' : b / c < A := (div_lt_iff₀ hc).mpr hb
  obtain ⟨a, ha, haA⟩ := exists_between (max_lt hA hb')
  have hba : b < a * c := (div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt ha)
  filter_upwards [hf a haA, (tendsto_order.mp (hg.const_mul a)).1 b hba,
    (tendsto_order.mp hg).1 0 hc] with x hfx hbx hgx
  exact hbx.trans (mul_lt_mul_of_pos_right hfx hgx)

lemma sharp_counting_constant_eq :
    tau ^ 2 / 3 * (4 / (tau * Real.sqrt tau)) = 4 * Real.sqrt tau / 3 := by
  have ht0 := tau_pos.ne'
  have hs0 := (Real.sqrt_pos.mpr tau_pos).ne'
  field_simp
  rw [Real.sq_sqrt tau_pos.le]

/-- The sharp lower counting constant along the explicitly constructed frame sizes. -/
theorem counting_frame_cardinality_lower {b : ℝ} (hb : b < 4 * Real.sqrt tau / 3) :
    ∀ᶠ x : ℝ in atTop,
      b < Real.log (irreducibleCount (countingSize x)) *
        Real.sqrt (Real.log (countingSize x)) /
          ((countingSize x : ℝ) * Real.sqrt (countingSize x)) := by
  have hA : 0 < tau ^ 2 / 3 := div_pos (sq_pos_of_pos tau_pos) (by norm_num)
  have hc : 0 < 4 / (tau * Real.sqrt tau) :=
    div_pos (by norm_num) (mul_pos tau_pos (Real.sqrt_pos.mpr tau_pos))
  have ht := eventually_mul_lower_of_tendsto hA hc
    (fun _ ha => counting_frame_log_eventually_lower ha) entropy_normalization_limit
    (by simpa only [sharp_counting_constant_eq] using hb)
  filter_upwards [ht, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hs := (entropyScale_pos hx1).ne'
  convert hx using 1
  field_simp

end Erdos1189
