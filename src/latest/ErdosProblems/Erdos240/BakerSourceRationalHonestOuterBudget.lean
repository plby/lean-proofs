/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourcePositiveStageGrowth
import ErdosProblems.Erdos240.BakerSourceRationalSharpBudget

/-!
# Source-faithful terminal outer-contour budget

The terminal Lemma-5 circle inherits algebraic growth `2 H + 15 H_t` and,
for the actual analytic auxiliary function, growth `2 H + 24 H_t`; neither
may be replaced by the smaller rational-target exponent `2 H`.  The source
seed `k^sigma >= 256` makes `H_t` a small fraction of `k^(1/2) H`; the
literal terminal nodal count therefore still absorbs either honest growth
bound together with the exact radical-degree Liouville exponent.
-/

noncomputable section

namespace Erdos240.VDPLParameters

open BakerLemma2Concrete
open BakerSourcePositiveStageGrowth

variable {oldRank : ℕ} [Nonempty (Fin oldRank)]
  (P : VDPLParameters (Fin oldRank))

/-- The terminal positive-stage unit, multiplied by `k^sigma`, is exactly
`k^(1/2)` times the fixed source height unit. -/
theorem terminalPositiveStageHeightUnit_mul_k_rpow_sigma :
    positiveStageHeightUnit P (3 * (P.rank + 1) - 1) * P.k ^ P.sigma =
      P.k ^ (1 / 2 : ℝ) * sourceHeightUnit P := by
  have hstage : 3 * (P.rank + 1) - 1 + 1 = 3 * (P.rank + 1) := by
    omega
  have hexponent :
      1 - P.sigma +
          P.epsilon * ((3 * (P.rank + 1) : ℕ) : ℝ) + P.sigma =
        (3 / 2 : ℝ) := by
    rw [P.epsilon_eq]
    push_cast
    have hr : (0 : ℝ) < P.rank + 1 := by positivity
    field_simp
    ring
  have hleft :
      P.k ^ (1 - P.sigma +
          P.epsilon * ((3 * (P.rank + 1) : ℕ) : ℝ)) *
          P.k ^ P.sigma =
        P.k ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add P.k_pos]
    congr 1
  have hright :
      P.k ^ (1 / 2 : ℝ) * P.k = P.k ^ (3 / 2 : ℝ) := by
    nth_rewrite 2 [← Real.rpow_one P.k]
    rw [← Real.rpow_add P.k_pos]
    congr 1
    ring
  unfold positiveStageHeightUnit sourceHeightUnit
  rw [hstage]
  calc
    (P.h : ℝ) *
          P.k ^ (1 - P.sigma +
            P.epsilon * ((3 * (P.rank + 1) : ℕ) : ℝ)) *
          P.Omega * Real.log P.OmegaOld * P.k ^ P.sigma =
        (P.h : ℝ) *
          (P.k ^ (1 - P.sigma +
              P.epsilon * ((3 * (P.rank + 1) : ℕ) : ℝ)) *
            P.k ^ P.sigma) * P.Omega * Real.log P.OmegaOld := by ring
    _ = (P.h : ℝ) * P.k ^ (3 / 2 : ℝ) * P.Omega *
        Real.log P.OmegaOld := by rw [hleft]
    _ = (P.h : ℝ) * (P.k ^ (1 / 2 : ℝ) * P.k) * P.Omega *
        Real.log P.OmegaOld := by rw [hright]
    _ = P.k ^ (1 / 2 : ℝ) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) := by ring

/-- The exact terminal count pays the honest outer growth
`2 H + 15 H_t`, the exact radical degree, and the additive unit used for
the `3/2` Cauchy factor. -/
theorem honestTerminal_outerExponent_add_growth_add_one_lt_count_log_two
    {J : ℕ} (hJ : P.LevelOK J) :
    (6 + 34 * (13 ^ (oldRank + 1) : ℝ)) * sourceHeightUnit P + 1 +
        (2 * sourceHeightUnit P +
          15 * positiveStageHeightUnit P (3 * (P.rank + 1) - 1)) <
      ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 := by
  let d : ℝ := (13 ^ (oldRank + 1) : ℝ)
  let u : ℝ := P.k ^ (1 / 2 : ℝ)
  let v : ℝ := P.k ^ (1 / 6 : ℝ)
  let H : ℝ := sourceHeightUnit P
  let T : ℝ := positiveStageHeightUnit P (3 * (P.rank + 1) - 1)
  let n : ℕ := P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J
  have hH : (1 : ℝ) ≤ H := by
    simpa only [H, sourceHeightUnit] using P.one_le_sourceHeightUnit
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    exact (positiveStageHeightUnit_pos P _).le
  have hu : (64 : ℝ) ≤ u := by
    simpa only [u] using P.sixtyFour_le_k_rpow_half
  have hu0 : 0 ≤ u := (by positivity)
  have hv : (1 : ℝ) ≤ v := by
    dsimp only [v]
    exact Real.one_le_rpow P.one_le_k (by norm_num)
  have hdv : d ≤ v := by
    simpa only [d, v] using P.sourceRadicalDegree_le_k_rpow_one_sixth
  have huv : 128 * v ≤ u := by
    simpa only [u, v] using
      P.oneTwentyEight_mul_k_rpow_one_sixth_le_k_rpow_half
  have hks : (256 : ℝ) ≤ P.k ^ P.sigma :=
    twoHundredFiftySix_le_k_rpow_sigma P
  have hTH : T * P.k ^ P.sigma = u * H := by
    simpa only [T, u, H] using
      P.terminalPositiveStageHeightUnit_mul_k_rpow_sigma
  have hTbound : 256 * T ≤ u * H := by
    calc
      256 * T = T * 256 := by ring
      _ ≤ T * P.k ^ P.sigma := mul_le_mul_of_nonneg_left hks hT0
      _ = u * H := hTH
  have hdegreeCoeff : 8 + 34 * d ≤ 42 * v := by nlinarith
  have hdegree :
      (8 + 34 * d) * H ≤ (42 / 128 : ℝ) * (u * H) := by
    have hscaled := mul_le_mul_of_nonneg_right hdegreeCoeff hH0
    have huvH := mul_le_mul_of_nonneg_right huv hH0
    nlinarith
  have hstage : 15 * T ≤ (15 / 256 : ℝ) * (u * H) := by
    nlinarith
  have hone : (1 : ℝ) ≤ (1 / 64 : ℝ) * (u * H) := by
    have huH := mul_le_mul_of_nonneg_right hu hH0
    nlinarith
  have hsum :
      (8 + 34 * d) * H + 15 * T + 1 ≤
        (103 / 256 : ℝ) * (u * H) := by
    nlinarith
  have hcoeff :
      (103 / 256 : ℝ) < (15 / 19 : ℝ) * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have huHpos : 0 < u * H := by
    exact mul_pos (lt_of_lt_of_le (by norm_num) hu)
      (lt_of_lt_of_le (by norm_num) hH)
  have hmiddle :
      (103 / 256 : ℝ) * (u * H) <
        ((15 / 19 : ℝ) * u * H) * Real.log 2 := by
    have := mul_lt_mul_of_pos_right hcoeff huHpos
    nlinarith
  have hcount :=
    P.fifteen_nineteenths_mul_sqrtK_mul_sourceHeight_lt_lemmaFive_count hJ
  have hcountLog := mul_lt_mul_of_pos_right hcount
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  dsimp only [d, u, v, H, T, n] at hsum hmiddle hcountLog ⊢
  calc
    (6 + 34 * (13 ^ (oldRank + 1) : ℝ)) * sourceHeightUnit P + 1 +
        (2 * sourceHeightUnit P +
          15 * positiveStageHeightUnit P (3 * (P.rank + 1) - 1)) =
      (8 + 34 * (13 ^ (oldRank + 1) : ℝ)) * sourceHeightUnit P +
        15 * positiveStageHeightUnit P (3 * (P.rank + 1) - 1) + 1 := by ring
    _ ≤ (103 / 256 : ℝ) *
        (P.k ^ (1 / 2 : ℝ) * sourceHeightUnit P) := hsum
    _ < ((15 / 19 : ℝ) * P.k ^ (1 / 2 : ℝ) *
        sourceHeightUnit P) * Real.log 2 := hmiddle
    _ < ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 := by
      simpa only [sourceHeightUnit] using hcountLog

/-- The exact terminal count also pays the analytic auxiliary-function
growth `2 H + 24 H_t`.  The extra nine stage units are the perturbation
loss in `sourceSharpAnalyticGrowthMajorant_le_positiveContour`. -/
theorem honestAnalyticTerminal_outerExponent_add_growth_add_one_lt_count_log_two
    {J : ℕ} (hJ : P.LevelOK J) :
    (6 + 34 * (13 ^ (oldRank + 1) : ℝ)) * sourceHeightUnit P + 1 +
        (2 * sourceHeightUnit P +
          24 * positiveStageHeightUnit P (3 * (P.rank + 1) - 1)) <
      ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 := by
  let d : ℝ := (13 ^ (oldRank + 1) : ℝ)
  let u : ℝ := P.k ^ (1 / 2 : ℝ)
  let v : ℝ := P.k ^ (1 / 6 : ℝ)
  let H : ℝ := sourceHeightUnit P
  let T : ℝ := positiveStageHeightUnit P (3 * (P.rank + 1) - 1)
  let n : ℕ := P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J
  have hH : (1 : ℝ) ≤ H := by
    simpa only [H, sourceHeightUnit] using P.one_le_sourceHeightUnit
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    exact (positiveStageHeightUnit_pos P _).le
  have hu : (64 : ℝ) ≤ u := by
    simpa only [u] using P.sixtyFour_le_k_rpow_half
  have hv : (1 : ℝ) ≤ v := by
    dsimp only [v]
    exact Real.one_le_rpow P.one_le_k (by norm_num)
  have hdv : d ≤ v := by
    simpa only [d, v] using P.sourceRadicalDegree_le_k_rpow_one_sixth
  have huv : 128 * v ≤ u := by
    simpa only [u, v] using
      P.oneTwentyEight_mul_k_rpow_one_sixth_le_k_rpow_half
  have hks : (256 : ℝ) ≤ P.k ^ P.sigma :=
    twoHundredFiftySix_le_k_rpow_sigma P
  have hTH : T * P.k ^ P.sigma = u * H := by
    simpa only [T, u, H] using
      P.terminalPositiveStageHeightUnit_mul_k_rpow_sigma
  have hTbound : 256 * T ≤ u * H := by
    calc
      256 * T = T * 256 := by ring
      _ ≤ T * P.k ^ P.sigma := mul_le_mul_of_nonneg_left hks hT0
      _ = u * H := hTH
  have hdegreeCoeff : 8 + 34 * d ≤ 42 * v := by nlinarith
  have hdegree :
      (8 + 34 * d) * H ≤ (42 / 128 : ℝ) * (u * H) := by
    have hscaled := mul_le_mul_of_nonneg_right hdegreeCoeff hH0
    have huvH := mul_le_mul_of_nonneg_right huv hH0
    nlinarith
  have hstage : 24 * T ≤ (24 / 256 : ℝ) * (u * H) := by
    nlinarith
  have hone : (1 : ℝ) ≤ (1 / 64 : ℝ) * (u * H) := by
    have huH := mul_le_mul_of_nonneg_right hu hH0
    nlinarith
  have hsum :
      (8 + 34 * d) * H + 24 * T + 1 ≤
        (7 / 16 : ℝ) * (u * H) := by
    nlinarith
  have hcoeff :
      (7 / 16 : ℝ) < (15 / 19 : ℝ) * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have huHpos : 0 < u * H := by
    exact mul_pos (lt_of_lt_of_le (by norm_num) hu)
      (lt_of_lt_of_le (by norm_num) hH)
  have hmiddle :
      (7 / 16 : ℝ) * (u * H) <
        ((15 / 19 : ℝ) * u * H) * Real.log 2 := by
    have := mul_lt_mul_of_pos_right hcoeff huHpos
    nlinarith
  have hcount :=
    P.fifteen_nineteenths_mul_sqrtK_mul_sourceHeight_lt_lemmaFive_count hJ
  have hcountLog := mul_lt_mul_of_pos_right hcount
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  dsimp only [d, u, v, H, T, n] at hsum hmiddle hcountLog ⊢
  calc
    (6 + 34 * (13 ^ (oldRank + 1) : ℝ)) * sourceHeightUnit P + 1 +
        (2 * sourceHeightUnit P +
          24 * positiveStageHeightUnit P (3 * (P.rank + 1) - 1)) =
      (8 + 34 * (13 ^ (oldRank + 1) : ℝ)) * sourceHeightUnit P +
        24 * positiveStageHeightUnit P (3 * (P.rank + 1) - 1) + 1 := by ring
    _ ≤ (7 / 16 : ℝ) *
        (P.k ^ (1 / 2 : ℝ) * sourceHeightUnit P) := hsum
    _ < ((15 / 19 : ℝ) * P.k ^ (1 / 2 : ℝ) *
        sourceHeightUnit P) * Real.log 2 := hmiddle
    _ < ((P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J : ℕ) : ℝ) *
        Real.log 2 := by
      simpa only [sourceHeightUnit] using hcountLog

/-- Ready-to-use terminal outer estimate with the honest source boundary
growth.  Its output keeps one full height unit beyond the exact rational
Liouville exponent. -/
theorem lemmaFive_outerFactor_lt_exp_neg_sourceRadicalDegreeScale_of_honestGrowth
    {J : ℕ} (hJ : P.LevelOK J) {outer : ℝ}
    (houter0 : 0 ≤ outer)
    (houter : outer ≤ Real.exp
      (2 * sourceHeightUnit P +
        15 * positiveStageHeightUnit P (3 * (P.rank + 1) - 1))) :
    (3 / 2 : ℝ) *
        ((1 / 2 : ℝ) ^
          (P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J) * outer) <
      Real.exp (-((6 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        sourceHeightUnit P)) := by
  apply three_halves_mul_two_inv_pow_mul_lt_exp_neg_of_count houter0 houter
  exact P.honestTerminal_outerExponent_add_growth_add_one_lt_count_log_two hJ

/-- Ready-to-use terminal outer estimate for the actual analytic auxiliary
function, whose checked contour majorant costs `2 H + 24 H_t`. -/
theorem lemmaFive_outerFactor_lt_exp_neg_sourceRadicalDegreeScale_of_honestAnalyticGrowth
    {J : ℕ} (hJ : P.LevelOK J) {outer : ℝ}
    (houter0 : 0 ≤ outer)
    (houter : outer ≤ Real.exp
      (2 * sourceHeightUnit P +
        24 * positiveStageHeightUnit P (3 * (P.rank + 1) - 1))) :
    (3 / 2 : ℝ) *
        ((1 / 2 : ℝ) ^
          (P.lemmaFiveLocalRadius J * P.lemmaFiveLocalMultiplicity J) * outer) <
      Real.exp (-((6 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        sourceHeightUnit P)) := by
  apply three_halves_mul_two_inv_pow_mul_lt_exp_neg_of_count houter0 houter
  exact P.honestAnalyticTerminal_outerExponent_add_growth_add_one_lt_count_log_two hJ

end Erdos240.VDPLParameters

#print axioms Erdos240.VDPLParameters.terminalPositiveStageHeightUnit_mul_k_rpow_sigma
#print axioms Erdos240.VDPLParameters.honestTerminal_outerExponent_add_growth_add_one_lt_count_log_two
#print axioms Erdos240.VDPLParameters.lemmaFive_outerFactor_lt_exp_neg_sourceRadicalDegreeScale_of_honestGrowth
#print axioms Erdos240.VDPLParameters.honestAnalyticTerminal_outerExponent_add_growth_add_one_lt_count_log_two
#print axioms Erdos240.VDPLParameters.lemmaFive_outerFactor_lt_exp_neg_sourceRadicalDegreeScale_of_honestAnalyticGrowth
