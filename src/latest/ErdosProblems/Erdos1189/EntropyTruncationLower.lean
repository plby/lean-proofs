/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An entropy lower bound obtained from fixed finite exponent truncations.
Informal argument: bound the truncated prime mass uniformly below its asymptotic,
then count weighted coordinate scores using the second prime moment.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.TruncatedCoordinates
import ErdosProblems.Erdos1189.CountingSizeAsymptotic

namespace Erdos1189

open Finset Filter

lemma truncatedPrimeMass_uniform_lower (T : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (haT : a < partialTau T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ∀ s : ℝ, 0 < s → s < x →
      a * s / Real.log x - C ≤ truncatedPrimeMass T s := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((tendsto_order.mp (truncatedPrimeMass_asymptotic T)).1 a haT)
  let Y := max B 2
  have hY : 0 ≤ Y := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_right _ _)
  have hC : 0 ≤ a * Y := mul_nonneg ha hY
  refine ⟨a * Y, hC, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx
  intro s hs hsx
  by_cases hsY : Y ≤ s
  · have hs1 : 1 < s := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      ((le_max_right B 2).trans hsY)
    have hratio := (hB s ((le_max_left B 2).trans hsY)).le
    have hq : 0 < realLogPower 1 s := by
      exact div_pos (by simpa using hs) (Real.log_pos hs1)
    have hmass : a * s / Real.log s ≤ truncatedPrimeMass T s := by
      have h := (le_div_iff₀ hq).mp hratio
      simpa only [realLogPower, pow_one, mul_div_assoc] using h
    have hlog : Real.log s ≤ Real.log x := Real.log_le_log hs hsx.le
    have h := (div_le_div_of_nonneg_left (mul_nonneg ha hs.le) (Real.log_pos hs1) hlog).trans hmass
    linarith
  · have hsY' : s ≤ Y := le_of_not_ge hsY
    have hdiv : a * s / Real.log x ≤ a * s :=
      div_le_self (mul_nonneg ha hs.le) hx
    have hmul := mul_le_mul_of_nonneg_left hsY' ha
    have hmass := truncatedPrimeMass_nonneg T s
    linarith

lemma entropy_lower_of_uniform_mass {x a C : ℝ} (T U : ℕ)
    (hlog : 0 < Real.log x) (ha : 0 ≤ a)
    (hbound : ∀ s : ℝ, 0 < s → s < x → a * s / Real.log x - C ≤ truncatedPrimeMass T s) :
    a / Real.log x * truncatedScoreMoment U x -
      (C + Real.log (T + 1 : ℝ)) * (simpsonWeight (countingInteger x) : ℝ) ≤ countingEntropy x := by
  classical
  have htrunc : truncatedScoreMoment U x ≤ ∑ c ∈ countingCoordinates x,
      ((c.1 - 1 : ℕ) : ℝ) * coordinateScore c.1 c.2 := by
    rw [truncatedScoreMoment_eq]
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro c hc _
    exact mul_nonneg (Nat.cast_nonneg _)
      (coordinateScore_pos (mem_countingCoordinates.mp hc).1 c.2).le
  have hweight : (simpsonWeight (countingInteger x) : ℝ) =
      ∑ c ∈ countingCoordinates x, ((c.1 - 1 : ℕ) : ℝ) := by
    rw [countingInteger_weight, Nat.cast_sum]
  calc
    _ ≤ a / Real.log x * (∑ c ∈ countingCoordinates x,
        ((c.1 - 1 : ℕ) : ℝ) * coordinateScore c.1 c.2) -
          (C + Real.log (T + 1 : ℝ)) * (simpsonWeight (countingInteger x) : ℝ) :=
      sub_le_sub_right (mul_le_mul_of_nonneg_left htrunc (div_nonneg ha hlog.le)) _
    _ = ∑ c ∈ countingCoordinates x, ((c.1 - 1 : ℕ) : ℝ) *
        (a * coordinateScore c.1 c.2 / Real.log x - C - Real.log (T + 1 : ℝ)) := by
      rw [hweight, mul_sum, mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro c _
      ring
    _ ≤ countingEntropy x := by
      apply sum_le_sum
      intro c hc
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hmass := hbound _ (coordinateScore_pos (mem_countingCoordinates.mp hc).1 c.2)
        (mem_countingCoordinates.mp hc).2
      have hinner := truncatedPrimeMass_le_entropy_inner hc T
      linarith

lemma eventually_entropy_truncation_lower (T U : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (haT : a < partialTau T) :
    ∃ D : ℝ, ∀ᶠ x : ℝ in atTop,
      a / Real.log x * truncatedScoreMoment U x -
        D * (simpsonWeight (countingInteger x) : ℝ) ≤ countingEntropy x := by
  obtain ⟨C, _, hC⟩ := truncatedPrimeMass_uniform_lower T ha haT
  refine ⟨C + Real.log (T + 1 : ℝ), ?_⟩
  filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  exact entropy_lower_of_uniform_mass T U (Real.log_pos hx1) ha hx

end Erdos1189
