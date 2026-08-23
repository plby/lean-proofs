/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma4OuterEstimate
import ErdosProblems.Erdos240.BakerSourceBudgetInequalities

/-!
# The exceptional initial outer-contour budget in source Lemma 4

Every genuinely new target, including the exceptional stage `t = 0`, uses
the sharp `3^(-R*S)` quotient.  This module pays the exact printed target
and growth exponents against that first-stage count, including the `3/2`
Cauchy loss.
-/

noncomputable section

namespace Erdos240.VDPLParameters

variable {ι : Type*} [Fintype ι] (P : VDPLParameters ι)

/-- The source's third p.39 requirement makes the varying part of the
initial-stage growth exponent smaller than `4k/15`. -/
theorem thirtyTwo_mul_initialStagePower_lt_four_fifteenths_mul_k
    (hreq : P.sourceTenThreshold ∈ P.kRequirements) :
    32 * P.k ^ (1 - P.sigma + P.epsilon) < (4 / 15 : ℝ) * P.k := by
  have hraw :=
    P.thirtyTwo_mul_nextStagePower_lt_sixteen_fifths_mul_epsilon_mul_stagePower
      hreq 0
  have heps : P.epsilon ≤ (1 / 12 : ℝ) := by
    rw [P.epsilon_eq]
    have hrank : (2 : ℝ) ≤ P.rank + 1 := by
      exact_mod_cast Nat.succ_le_succ P.one_le_rank
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * (P.rank + 1))).2
    nlinarith
  have hk0 : 0 ≤ P.k := P.k_pos.le
  have hupper : (16 / 5 : ℝ) * P.epsilon * P.k ≤
      (4 / 15 : ℝ) * P.k := by
    have heps' : (16 / 5 : ℝ) * P.epsilon ≤ 4 / 15 := by nlinarith
    exact mul_le_mul_of_nonneg_right heps' hk0
  have hraw' : 32 * P.k ^ (1 - P.sigma + P.epsilon) <
      (16 / 5 : ℝ) * P.epsilon * P.k := by
    simpa only [Nat.zero_add, Nat.cast_one, Nat.cast_zero, mul_zero, mul_one, add_zero,
      Real.rpow_one] using hraw
  exact hraw'.trans_le hupper

/-- The common source-height unit is already larger than `26/3`; this
quantitative reserve pays the additive unit used for the `3/2` factor. -/
theorem twentySix_thirds_lt_sourceHeightUnit [Nonempty ι] :
    (26 / 3 : ℝ) <
      (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld := by
  have hepsOne : P.epsilon ≤ 1 := by
    rw [P.epsilon_eq]
    have hrank : (1 : ℝ) ≤ P.rank + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.rank)
    apply (div_le_one (by positivity :
      (0 : ℝ) < 6 * (P.rank + 1))).2
    nlinarith
  have hkEps : P.k ^ P.epsilon ≤ P.k := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le P.one_le_k hepsOne
  have hk : (13 : ℝ) ≤ P.k := by
    calc
      (13 : ℝ) = P.q := by norm_num [VDPLParameters.q]
      _ ≤ P.k ^ P.epsilon := P.q_le_k_rpow_epsilon
      _ ≤ P.k := hkEps
  have hh : (2 : ℝ) ≤ P.h := by exact_mod_cast P.two_le_h
  have hlog : (2 / 3 : ℝ) ≤ Real.log P.OmegaOld :=
    (by nlinarith [Real.log_two_gt_d9] :
      (2 / 3 : ℝ) ≤ Real.log 2).trans P.log_two_le_log_OmegaOld
  have hW : (2 / 3 : ℝ) ≤ P.Omega * Real.log P.OmegaOld := by
    calc
      (2 / 3 : ℝ) = 1 * (2 / 3) := by ring
      _ ≤ P.Omega * Real.log P.OmegaOld :=
        mul_le_mul P.one_le_Omega hlog (by norm_num) P.Omega_pos.le
  have hlarge : (2 : ℝ) * 13 * (2 / 3) ≤
      (P.h : ℝ) * P.k * (P.Omega * Real.log P.OmegaOld) := by
    gcongr
  nlinarith

/-- Exact logarithmic budget for the exceptional first interpolation stage.
The left side is the target exponent, the outer-growth exponent, and the
single unit paying the normalized Cauchy factor. -/
theorem initialStage_outerExponent_add_growth_add_one_lt_count_mul_log_three
    [Nonempty ι] {N : ℕ} (hN : P.LevelOK N)
    (hreq : P.sourceTenThreshold ∈ P.kRequirements) :
    ((4 * (P.h : ℝ) * P.k +
        32 * (P.h : ℝ) * P.k ^ (1 - P.sigma + P.epsilon)) *
      (P.Omega * Real.log P.OmegaOld)) + 1 <
      ((P.lemmaFourRadius N 0 *
        (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1) : ℕ) : ℝ) *
        Real.log 3 := by
  let K : ℝ := P.k ^ (1 - P.sigma + P.epsilon)
  let W : ℝ := P.Omega * Real.log P.OmegaOld
  let H : ℝ := (P.h : ℝ) * P.k * W
  have hK :=
    P.thirtyTwo_mul_initialStagePower_lt_four_fifteenths_mul_k hreq
  have hhW : 0 < (P.h : ℝ) * W := by
    dsimp only [W]
    exact mul_pos (by exact_mod_cast P.h_pos)
      (mul_pos P.Omega_pos P.log_OmegaOld_pos)
  have hscaled :
      (4 * (P.h : ℝ) * P.k + 32 * (P.h : ℝ) * K) * W <
        (64 / 15 : ℝ) * H := by
    have hcoeff : 4 * P.k + 32 * K < (64 / 15 : ℝ) * P.k := by
      dsimp only [K] at hK ⊢
      nlinarith
    have := mul_lt_mul_of_pos_right hcoeff hhW
    dsimp only [H]
    calc
      (4 * (P.h : ℝ) * P.k + 32 * (P.h : ℝ) * K) * W =
          (4 * P.k + 32 * K) * ((P.h : ℝ) * W) := by ring
      _ < (64 / 15 : ℝ) * P.k * ((P.h : ℝ) * W) := this
      _ = (64 / 15 : ℝ) * ((P.h : ℝ) * P.k * W) := by ring
  have hHpos : 0 < H := by
    dsimp only [H, W]
    exact mul_pos (mul_pos (by exact_mod_cast P.h_pos) P.k_pos)
      (mul_pos P.Omega_pos P.log_OmegaOld_pos)
  have hseven :
      ((4 * (P.h : ℝ) * P.k + 32 * (P.h : ℝ) * K) * W) + 1 <
        7 * H + 1 := by
    nlinarith
  have hcount := P.initial_seven_mul_sourceHeight_add_one_lt_count_mul_log_three hN
  dsimp only [K, W, H] at hseven ⊢
  exact hseven.trans (by simpa only [mul_assoc] using hcount)

/-- Ready-to-use exact `t=0` outer-contour decay.  It complements
`positiveStage_threeHalves_mul_outerFactor_lt_exp_neg_target`. -/
theorem initialStage_threeHalves_mul_outerFactor_lt_exp_neg_target
    [Nonempty ι] {N : ℕ} (hN : P.LevelOK N)
    (hreq : P.sourceTenThreshold ∈ P.kRequirements)
    {growth : ℝ} (hgrowth0 : 0 ≤ growth)
    (hgrowth : growth ≤ Real.exp
      ((2 * (P.h : ℝ) * P.k +
        24 * (P.h : ℝ) * P.k ^ (1 - P.sigma + P.epsilon)) *
        (P.Omega * Real.log P.OmegaOld))) :
    (3 / 2 : ℝ) *
        ((1 / 3 : ℝ) ^
          (P.lemmaFourRadius N 0 *
            (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1)) * growth) <
      Real.exp (-((2 * (P.h : ℝ) * P.k +
        8 * (P.h : ℝ) * P.k ^ (1 - P.sigma + P.epsilon)) *
        (P.Omega * Real.log P.OmegaOld))) := by
  apply three_halves_mul_three_inv_pow_mul_lt_exp_neg_of_count
    hgrowth0 hgrowth
  have hcount :=
    P.initialStage_outerExponent_add_growth_add_one_lt_count_mul_log_three hN hreq
  convert hcount using 1 <;> ring

end Erdos240.VDPLParameters

#print axioms Erdos240.VDPLParameters.initialStage_outerExponent_add_growth_add_one_lt_count_mul_log_three
#print axioms Erdos240.VDPLParameters.initialStage_threeHalves_mul_outerFactor_lt_exp_neg_target
