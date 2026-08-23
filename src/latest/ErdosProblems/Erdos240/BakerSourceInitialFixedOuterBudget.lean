/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.BakerSourceInitialOuterBudget

/-!
# Fixed-height exceptional Lemma-4 outer budget

At the exceptional inner stage `t = 0`, the actual source boundary estimate
contains the varying contribution

`24 h k^(1 - sigma + epsilon) Omega log OmegaOld`.

The older fixed-height wrapper retained only the static `2H` part.  This
module uses the exact first-stage node count and the third source parameter
requirement to absorb the honest varying contribution while still leaving
five full source-height units.  It is deliberately isolated from the generic
outer-estimate modules so that consumers can migrate without changing their
other numerical interfaces.
-/

noncomputable section

namespace Erdos240.VDPLParameters

variable {ι : Type*} [Fintype ι] (P : VDPLParameters ι)

/-- The exact first-stage node count pays five source-height units, the
honest boundary growth `2H + 24H₀`, and the unit used for the normalized
`3/2` Cauchy factor. -/
theorem initialStage_fiveHeight_add_honestGrowth_add_one_lt_count_mul_log_three
    [Nonempty ι] {N : ℕ} (hN : P.LevelOK N)
    (hreq : P.sourceTenThreshold ∈ P.kRequirements) :
    5 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) + 1 +
        ((2 * (P.h : ℝ) * P.k +
            24 * (P.h : ℝ) * P.k ^ (1 - P.sigma + P.epsilon)) *
          (P.Omega * Real.log P.OmegaOld)) <
      ((P.lemmaFourRadius N 0 *
        (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1) : ℕ) : ℝ) *
        Real.log 3 := by
  let K : ℝ := P.k ^ (1 - P.sigma + P.epsilon)
  let W : ℝ := P.Omega * Real.log P.OmegaOld
  let H : ℝ := (P.h : ℝ) * P.k * W
  let G : ℝ := (2 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) * K) * W
  let count : ℕ := P.lemmaFourRadius N 0 *
    (P.lemmaFourBudget N 0 - P.lemmaFourBudget N 1 + 1)
  have hK32 := P.thirtyTwo_mul_initialStagePower_lt_four_fifteenths_mul_k hreq
  have hK24 : 24 * K < (1 / 5 : ℝ) * P.k := by
    dsimp only [K] at hK32 ⊢
    nlinarith
  have hhW : 0 < (P.h : ℝ) * W := by
    dsimp only [W]
    exact mul_pos (by exact_mod_cast P.h_pos)
      (mul_pos P.Omega_pos P.log_OmegaOld_pos)
  have hG : G < (11 / 5 : ℝ) * H := by
    have hcoeff : 2 * P.k + 24 * K < (11 / 5 : ℝ) * P.k := by
      nlinarith
    have hmul := mul_lt_mul_of_pos_right hcoeff hhW
    dsimp only [G, H]
    calc
      (2 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) * K) * W =
          (2 * P.k + 24 * K) * ((P.h : ℝ) * W) := by ring
      _ < (11 / 5 : ℝ) * P.k * ((P.h : ℝ) * W) := hmul
      _ = (11 / 5 : ℝ) * ((P.h : ℝ) * P.k * W) := by ring
  have hH : (26 / 3 : ℝ) < H := by
    have h := P.twentySix_thirds_lt_sourceHeightUnit
    dsimp only [H, W]
    convert h using 1 <;> ring
  have hleft : 5 * H + 1 + G < (15 / 2 : ℝ) * H := by
    nlinarith
  have hfive := P.initial_five_mul_sourceHeight_lt_count_mul_log_two hN
  have hfive' : 5 * H < (count : ℝ) * Real.log 2 := by
    dsimp only [H, W, count]
    convert hfive using 1 <;> ring
  have hcountPos : (0 : ℝ) < count := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    by_contra hn
    have hle : (count : ℝ) ≤ 0 := le_of_not_gt hn
    have hnonneg : (0 : ℝ) ≤ count := Nat.cast_nonneg count
    have hzero : (count : ℝ) = 0 := le_antisymm hle hnonneg
    rw [hzero, zero_mul] at hfive'
    nlinarith
  have hlogs : (3 / 2 : ℝ) * Real.log 2 < Real.log 3 := by
    nlinarith [Real.log_two_lt_d9, Real.log_three_gt_d9]
  have hcountLogs :
      (3 / 2 : ℝ) * ((count : ℝ) * Real.log 2) <
        (count : ℝ) * Real.log 3 := by
    have := mul_lt_mul_of_pos_left hlogs hcountPos
    nlinarith
  have hscaled : (15 / 2 : ℝ) * H < (count : ℝ) * Real.log 3 := by
    calc
      (15 / 2 : ℝ) * H = (3 / 2 : ℝ) * (5 * H) := by ring
      _ < (3 / 2 : ℝ) * ((count : ℝ) * Real.log 2) :=
        mul_lt_mul_of_pos_left hfive' (by norm_num)
      _ < (count : ℝ) * Real.log 3 := hcountLogs
  have hresult : 5 * H + 1 + G < (count : ℝ) * Real.log 3 :=
    hleft.trans hscaled
  dsimp only [H, G, K, W, count] at hresult ⊢
  convert hresult using 1 <;> ring

/-- Ready-to-use sharp first-stage decay with the actual source boundary
growth.  This is the fixed-height theorem needed by the Lemma-4 pointwise
callback. -/
theorem initialStage_threeHalves_mul_outerFactor_lt_exp_neg_five_of_honestGrowth
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
      Real.exp (-(5 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
  apply three_halves_mul_three_inv_pow_mul_lt_exp_neg_of_count
    hgrowth0 hgrowth
  have hcount :=
    P.initialStage_fiveHeight_add_honestGrowth_add_one_lt_count_mul_log_three
      hN hreq
  convert hcount using 1 <;> ring

end Erdos240.VDPLParameters

#print axioms
  Erdos240.VDPLParameters.initialStage_fiveHeight_add_honestGrowth_add_one_lt_count_mul_log_three
#print axioms
  Erdos240.VDPLParameters.initialStage_threeHalves_mul_outerFactor_lt_exp_neg_five_of_honestGrowth
