/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The sharp two-thirds constant for arbitrary ordered weighted prefix sums.
Informal source: BBMST Lemma 7.4.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.RootLogCutoff

namespace Erdos1189

open Finset Filter

noncomputable def rootLogPrefixBound (a m : ℝ) : ℝ :=
  (2 / (3 * Real.sqrt a)) * m * Real.sqrt m / Real.sqrt (Real.log m) +
    m * Real.sqrt (m ^ a) / Real.sqrt (Real.log 2)

lemma sum_rootLog_prefix_le_bound {β : Type*} (S : Finset β) (rank w : β → ℕ)
    (hinj : Set.InjOn rank S) {a : ℝ} (ha : 0 < a) (hm : 2 ≤ ∑ i ∈ S, w i) :
    (∑ i ∈ S, (w i : ℝ) * rootLog (prefixWeight S rank w i)) ≤
      rootLogPrefixBound a ((∑ i ∈ S, w i : ℕ) : ℝ) := by
  let m : ℝ := (∑ i ∈ S, w i : ℕ)
  have hm1 : 1 < m := by
    change (1 : ℝ) < ((∑ i ∈ S, w i : ℕ) : ℝ)
    exact_mod_cast (show 1 < ∑ i ∈ S, w i by omega)
  have hden : 0 ≤ Real.sqrt a * Real.sqrt (Real.log m) := by positivity
  have hsum : (∑ i ∈ S, (w i : ℝ) * rootLog (prefixWeight S rank w i)) ≤
      (∑ i ∈ S, (w i : ℝ) * Real.sqrt (prefixWeight S rank w i)) /
        (Real.sqrt a * Real.sqrt (Real.log m)) +
          m * Real.sqrt (m ^ a) / Real.sqrt (Real.log 2) := by
    have h := sum_le_sum (s := S) (fun i _ => mul_le_mul_of_nonneg_left
      (rootLog_cutoff ha hm1 (prefixWeight S rank w i)) (Nat.cast_nonneg (w i)))
    simpa only [mul_add, ← mul_div_assoc, sum_add_distrib, ← sum_div, ← sum_mul,
      ← Nat.cast_sum, m] using h
  have hconvex := div_le_div_of_nonneg_right (sum_sqrt_prefixWeight_le S rank w hinj) hden
  have hfinal := hsum.trans (add_le_add hconvex le_rfl)
  have heq : rootLogPrefixBound a ((∑ i ∈ S, w i : ℕ) : ℝ) =
      (2 / 3 : ℝ) * (∑ i ∈ S, w i) * Real.sqrt ((∑ i ∈ S, w i : ℕ) : ℝ) /
        (Real.sqrt a * Real.sqrt (Real.log m)) +
          m * Real.sqrt (m ^ a) / Real.sqrt (Real.log 2) := by
    unfold rootLogPrefixBound m
    ring
  rw [heq]
  exact hfinal

lemma rootLogPrefixBound_asymptotic {a : ℝ} (ha : a < 1) :
    Tendsto (fun m : ℝ => rootLogPrefixBound a m * Real.sqrt (Real.log m) /
      (m * Real.sqrt m)) atTop (nhds (2 / (3 * Real.sqrt a))) := by
  have ht := (rootLog_cutoff_error_tendsto ha).const_add (2 / (3 * Real.sqrt a))
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with m hm
  have hm0 := (zero_lt_one.trans hm).ne'
  have hsm0 := (Real.sqrt_pos.mpr (zero_lt_one.trans hm)).ne'
  have hsl0 := (Real.sqrt_pos.mpr (Real.log_pos hm)).ne'
  dsimp only [rootLogPrefixBound]
  field_simp

lemma exists_sqrt_prefix_exponent {b : ℝ} (hb : 2 / 3 < b) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ 2 / (3 * Real.sqrt a) < b := by
  obtain ⟨c, hc, hcb⟩ := exists_between hb
  have hc0 : 0 < c := by linarith
  have hr0 : 0 < 2 / (3 * c) := by positivity
  have hr1 : 2 / (3 * c) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  refine ⟨(2 / (3 * c)) ^ 2, sq_pos_of_pos hr0, by nlinarith, ?_⟩
  rw [Real.sqrt_sq hr0.le]
  have heq : 2 / (3 * (2 / (3 * c))) = c := by field_simp
  rwa [heq]

/-- Uniform over all finite index sets, ranks, and nonnegative integer weights. -/
theorem sum_rootLog_prefix_eventually_upper {b : ℝ} (hb : 2 / 3 < b) :
    ∀ᶠ m : ℕ in atTop, ∀ (β : Type) (S : Finset β) (rank w : β → ℕ),
      Set.InjOn rank S → (∑ i ∈ S, w i) = m →
      (∑ i ∈ S, (w i : ℝ) * rootLog (prefixWeight S rank w i)) * Real.sqrt (Real.log m) /
        ((m : ℝ) * Real.sqrt m) < b := by
  obtain ⟨a, ha, ha1, hab⟩ := exists_sqrt_prefix_exponent hb
  have ht := (rootLogPrefixBound_asymptotic ha1).comp tendsto_natCast_atTop_atTop
  filter_upwards [(tendsto_order.mp ht).2 b hab, eventually_ge_atTop 2] with m hm hm2
  intro β S rank w hinj hweight
  have hsum := sum_rootLog_prefix_le_bound S rank w hinj ha (hweight.symm ▸ hm2)
  rw [hweight] at hsum
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsum (Real.sqrt_nonneg _)) (by positivity)).trans_lt hm

end Erdos1189
