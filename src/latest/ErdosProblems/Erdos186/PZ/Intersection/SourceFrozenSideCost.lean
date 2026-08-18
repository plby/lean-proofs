/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceScaleSelectorCost

/-!
# Uniform side-selection cost on the frozen square-root range
-/

namespace Erdos186.PZ.Intersection

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- A finite bound for the loss-plus-reserve coefficient in every source
rank below `rankCeiling`. -/
def sourceScaleSelectorCostBound {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (rankCeiling + 1), context.lossConstant r + 1

theorem lossConstant_add_one_le_sourceScaleSelectorCostBound
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    {r rankCeiling : ℕ} (hrank : r ≤ rankCeiling) :
    context.lossConstant r + 1 ≤
      sourceScaleSelectorCostBound context rankCeiling := by
  unfold sourceScaleSelectorCostBound
  apply Nat.add_le_add_right
  exact Finset.single_le_sum
    (s := Finset.range (rankCeiling + 1))
    (f := fun i ↦ context.lossConstant i)
    (a := r)
    (fun i _hi ↦ Nat.zero_le (context.lossConstant i))
    (by simp only [Finset.mem_range]; omega)

theorem sourceScaleSelectorCostBound_pos {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) :
    0 < sourceScaleSelectorCostBound context rankCeiling := by
  exact (by omega : 0 < context.lossConstant 0 + 1).trans_le
    (lossConstant_add_one_le_sourceScaleSelectorCostBound context
      (show 0 ≤ rankCeiling by omega))

/-- After freezing the source parameters at `initialCard`, every dense
canonical-scale side input of size at most the current population has loss,
reserve, and one extra rounding unit bounded by an arbitrarily prescribed
fraction of `gamma₀ * mu₀ * currentCard`. -/
theorem eventually_frozen_scaleSelector_sideCost
    {beta eta exponent : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (kappa K : ℝ)
    (hkappa : 0 < kappa) (hK : 0 < K)
    (Q : ℝ) (hQ : 0 < Q) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ (currentCard : ℕ),
        Real.sqrt (initialCard : ℝ) ≤ (currentCard : ℝ) →
        currentCard ≤ initialCard →
        ∀ {r : ℕ} (X : Finset (LatticePoint r))
          (hX : (context.scaleSelector exponent).Eligible X),
          r ≤ rankCeiling →
          delta kappa initialCard * (currentCard : ℝ) ≤
            (X.card : ℝ) →
          X.card ≤ currentCard →
          Q * (((((context.scaleSelector exponent).chosen X hX).loss +
              ((context.scaleSelector exponent).chosen X hX).reserveBound : ℕ) : ℝ) + 1) ≤
            gamma kappa K initialCard * mu kappa initialCard *
              (currentCard : ℝ) := by
  let B : ℝ := sourceScaleSelectorCostBound context rankCeiling
  have hB : 0 < B := by
    dsimp only [B]
    exact_mod_cast sourceScaleSelectorCostBound_pos context rankCeiling
  have hdeltaLower : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(1 / 8 : ℝ)) ≤ delta kappa N :=
    eventually_nat_rpow_neg_le_delta kappa (by norm_num)
  have hpowerLarge : ∀ᶠ N : ℕ in atTop,
      2 ≤ (N : ℝ) ^ (3 / 8 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 8)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hlogGrowth := eventually_const_le_gamma_mul_mu_mul_log
    kappa K (8 * Q * B)
  have hpopulationGrowth :=
    eventually_const_le_gamma_natPow_mul_mu_mul_nat_rpow
      kappa K 1 (by norm_num : (0 : ℝ) < 1 / 2) (4 * Q)
  filter_upwards [hdeltaLower, hpowerLarge, hlogGrowth,
      hpopulationGrowth, eventually_delta_pos kappa,
      eventually_gamma_pos kappa hK, eventually_mu_mem_Ioo hkappa,
      eventually_ge_atTop (3 : ℕ)]
    with initialCard hdeltaN hpowerN hlogGrowthN hpopulationGrowthN
      hdeltaPos hgammaPos hmuRange hNthree
  intro currentCard hsqrt hcurrentUpper r X hX hrank hdense hXupper
  have hNpos : (0 : ℝ) < (initialCard : ℝ) := by
    exact_mod_cast (by omega : 0 < initialCard)
  have hcurrentNonneg : (0 : ℝ) ≤ (currentCard : ℝ) := by positivity
  have hroot : Real.sqrt (initialCard : ℝ) =
      (initialCard : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hsidePower : (initialCard : ℝ) ^ (3 / 8 : ℝ) ≤
      (X.card : ℝ) := by
    have hmul : (initialCard : ℝ) ^ (-(1 / 8 : ℝ)) *
          Real.sqrt (initialCard : ℝ) ≤
        delta kappa initialCard * (currentCard : ℝ) :=
      mul_le_mul hdeltaN hsqrt (Real.sqrt_nonneg _) hdeltaPos.le
    calc
      (initialCard : ℝ) ^ (3 / 8 : ℝ) =
          (initialCard : ℝ) ^ (-(1 / 8 : ℝ)) *
            Real.sqrt (initialCard : ℝ) := by
        rw [hroot, ← Real.rpow_add hNpos]
        congr 1
        ring
      _ ≤ delta kappa initialCard * (currentCard : ℝ) := hmul
      _ ≤ (X.card : ℝ) := hdense
  have hXtwoReal : (2 : ℝ) ≤ (X.card : ℝ) := hpowerN.trans hsidePower
  have hXtwo : 2 ≤ X.card := by exact_mod_cast hXtwoReal
  have hlogN : 0 < Real.log (initialCard : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < initialCard by omega))
  have hlogX : 0 < Real.log (X.card : ℝ) :=
    Real.log_pos (one_lt_two.trans_le hXtwoReal)
  have hlogSide : (3 / 8 : ℝ) * Real.log (initialCard : ℝ) ≤
      Real.log (X.card : ℝ) := by
    have hlogMono := Real.log_le_log
      (Real.rpow_pos_of_pos hNpos (3 / 8 : ℝ)) hsidePower
    rw [Real.log_rpow hNpos] at hlogMono
    exact hlogMono
  have hlogbN : 0 < Real.logb 2 (initialCard : ℝ) :=
    div_pos hlogN (Real.log_pos (by norm_num))
  have hlogbX : 0 < Real.logb 2 (X.card : ℝ) :=
    div_pos hlogX (Real.log_pos (by norm_num))
  have hlogbSide : (1 / 4 : ℝ) *
      Real.logb 2 (initialCard : ℝ) ≤
        Real.logb 2 (X.card : ℝ) := by
    rw [Real.logb, Real.logb]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith [hlogSide])
      (Real.log_pos (by norm_num)).le
  have hlogLeLogb : Real.log (initialCard : ℝ) ≤
      Real.logb 2 (initialCard : ℝ) := by
    rw [Real.logb]
    have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
      convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
      norm_num
    exact (le_div_iff₀ (Real.log_pos (by norm_num))).2 (by nlinarith)
  have hXupperReal : (X.card : ℝ) ≤ (currentCard : ℝ) := by
    exact_mod_cast hXupper
  have hfraction : (X.card : ℝ) /
        Real.logb 2 (X.card : ℝ) ≤
      4 * (currentCard : ℝ) / Real.log (initialCard : ℝ) := by
    calc
      (X.card : ℝ) / Real.logb 2 (X.card : ℝ) ≤
          (currentCard : ℝ) /
            Real.logb 2 (X.card : ℝ) := by
        exact div_le_div_of_nonneg_right hXupperReal hlogbX.le
      _ ≤ (currentCard : ℝ) /
          ((1 / 4 : ℝ) * Real.logb 2 (initialCard : ℝ)) := by
        exact div_le_div_of_nonneg_left hcurrentNonneg
          (mul_pos (by norm_num) hlogbN) hlogbSide
      _ = 4 * (currentCard : ℝ) /
          Real.logb 2 (initialCard : ℝ) := by field_simp
      _ ≤ 4 * (currentCard : ℝ) /
          Real.log (initialCard : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) hlogN hlogLeLogb
  have hcoefficient : ((context.lossConstant r : ℝ) + 1) ≤ B := by
    dsimp only [B]
    exact_mod_cast
      lossConstant_add_one_le_sourceScaleSelectorCostBound context hrank
  have hrawCost := scaleSelector_loss_add_reserveBound_le
    context X hX hXtwo
  let cost : ℝ :=
    ((((context.scaleSelector exponent).chosen X hX).loss +
      ((context.scaleSelector exponent).chosen X hX).reserveBound : ℕ) : ℝ)
  have hcost : cost ≤ 4 * B * (currentCard : ℝ) /
      Real.log (initialCard : ℝ) + 1 := by
    calc
      cost ≤ ((context.lossConstant r : ℝ) + 1) *
          (X.card : ℝ) / Real.logb 2 (X.card : ℝ) + 1 := hrawCost
      _ ≤ B * ((X.card : ℝ) /
          Real.logb 2 (X.card : ℝ)) + 1 := by
        rw [mul_div_assoc]
        gcongr
      _ ≤ B * (4 * (currentCard : ℝ) /
          Real.log (initialCard : ℝ)) + 1 := by gcongr
      _ = 4 * B * (currentCard : ℝ) /
          Real.log (initialCard : ℝ) + 1 := by ring
  have hmainHalf : Q * (4 * B * (currentCard : ℝ) /
        Real.log (initialCard : ℝ)) ≤
      (gamma kappa K initialCard * mu kappa initialCard *
        (currentCard : ℝ)) / 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hlogGrowthN
      (div_nonneg hcurrentNonneg (by norm_num : (0 : ℝ) ≤ 2))
    field_simp [hlogN.ne'] at hscaled ⊢
    nlinarith
  have hrootGrowth : 4 * Q ≤ gamma kappa K initialCard *
      mu kappa initialCard * Real.sqrt (initialCard : ℝ) := by
    simpa only [pow_one, hroot] using hpopulationGrowthN
  have honeHalf : Q * 2 ≤
      (gamma kappa K initialCard * mu kappa initialCard *
        (currentCard : ℝ)) / 2 := by
    have h := mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg hgammaPos.le hmuRange.1.le)
    nlinarith
  have hQnonneg : 0 ≤ Q := hQ.le
  calc
    Q * (cost + 1) ≤
        Q * ((4 * B * (currentCard : ℝ) /
          Real.log (initialCard : ℝ) + 1) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hcost]) hQnonneg
    _ ≤ gamma kappa K initialCard * mu kappa initialCard *
        (currentCard : ℝ) := by nlinarith

/-- Arbitrary positive power-range form of the frozen side-cost bound. -/
theorem eventually_powerRange_scaleSelector_sideCost
    {beta eta exponent : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (p : ℝ) (hp : 0 < p)
    (kappa K : ℝ)
    (hkappa : 0 < kappa) (hK : 0 < K)
    (Q : ℝ) (hQ : 0 < Q) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ (currentCard : ℕ),
        (initialCard : ℝ) ^ p ≤ (currentCard : ℝ) →
        currentCard ≤ initialCard →
        ∀ {r : ℕ} (X : Finset (LatticePoint r))
          (hX : (context.scaleSelector exponent).Eligible X),
          r ≤ rankCeiling →
          delta kappa initialCard * (currentCard : ℝ) ≤
            (X.card : ℝ) →
          X.card ≤ currentCard →
          Q * (((((context.scaleSelector exponent).chosen X hX).loss +
              ((context.scaleSelector exponent).chosen X hX).reserveBound : ℕ) : ℝ) + 1) ≤
            gamma kappa K initialCard * mu kappa initialCard *
              (currentCard : ℝ) := by
  let B : ℝ := sourceScaleSelectorCostBound context rankCeiling
  let q : ℝ := p / 4
  have hB : 0 < B := by
    dsimp only [B]
    exact_mod_cast sourceScaleSelectorCostBound_pos context rankCeiling
  have hq : 0 < q := by dsimp only [q]; positivity
  have hthreeQuarter : 0 < 3 * p / 4 := by positivity
  have hdeltaLower : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-q) ≤ delta kappa N :=
    eventually_nat_rpow_neg_le_delta kappa hq
  have hpowerLarge : ∀ᶠ N : ℕ in atTop,
      2 ≤ (N : ℝ) ^ (3 * p / 4) :=
    ((tendsto_rpow_atTop hthreeQuarter).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hlogGrowth := eventually_const_le_gamma_mul_mu_mul_log
    kappa K (4 * Q * B / p)
  have hpopulationGrowth :=
    eventually_const_le_gamma_natPow_mul_mu_mul_nat_rpow
      kappa K 1 hp (4 * Q)
  filter_upwards [hdeltaLower, hpowerLarge, hlogGrowth,
      hpopulationGrowth, eventually_delta_pos kappa,
      eventually_gamma_pos kappa hK, eventually_mu_mem_Ioo hkappa,
      eventually_ge_atTop (3 : ℕ)]
    with initialCard hdeltaN hpowerN hlogGrowthN hpopulationGrowthN
      hdeltaPos hgammaPos hmuRange hNthree
  intro currentCard hlower hcurrentUpper r X hX hrank hdense hXupper
  have hNpos : (0 : ℝ) < (initialCard : ℝ) := by
    exact_mod_cast (by omega : 0 < initialCard)
  have hcurrentNonneg : (0 : ℝ) ≤ (currentCard : ℝ) := by positivity
  have hsidePower : (initialCard : ℝ) ^ (3 * p / 4) ≤
      (X.card : ℝ) := by
    have hmul : (initialCard : ℝ) ^ (-q) *
          (initialCard : ℝ) ^ p ≤
        delta kappa initialCard * (currentCard : ℝ) :=
      mul_le_mul hdeltaN hlower (Real.rpow_nonneg hNpos.le _) hdeltaPos.le
    calc
      (initialCard : ℝ) ^ (3 * p / 4) =
          (initialCard : ℝ) ^ (-q) * (initialCard : ℝ) ^ p := by
        rw [← Real.rpow_add hNpos]
        dsimp only [q]
        congr 1
        ring
      _ ≤ delta kappa initialCard * (currentCard : ℝ) := hmul
      _ ≤ (X.card : ℝ) := hdense
  have hXtwoReal : (2 : ℝ) ≤ (X.card : ℝ) := hpowerN.trans hsidePower
  have hXtwo : 2 ≤ X.card := by exact_mod_cast hXtwoReal
  have hlogN : 0 < Real.log (initialCard : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < initialCard by omega))
  have hlogX : 0 < Real.log (X.card : ℝ) :=
    Real.log_pos (one_lt_two.trans_le hXtwoReal)
  have hlogSide : (3 * p / 4) * Real.log (initialCard : ℝ) ≤
      Real.log (X.card : ℝ) := by
    have hlogMono := Real.log_le_log
      (Real.rpow_pos_of_pos hNpos (3 * p / 4)) hsidePower
    rw [Real.log_rpow hNpos] at hlogMono
    exact hlogMono
  have hlogbN : 0 < Real.logb 2 (initialCard : ℝ) :=
    div_pos hlogN (Real.log_pos (by norm_num))
  have hlogbX : 0 < Real.logb 2 (X.card : ℝ) :=
    div_pos hlogX (Real.log_pos (by norm_num))
  have hlogbSide : (p / 2) * Real.logb 2 (initialCard : ℝ) ≤
      Real.logb 2 (X.card : ℝ) := by
    rw [Real.logb, Real.logb]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith [hlogSide, hlogN])
      (Real.log_pos (by norm_num)).le
  have hlogLeLogb : Real.log (initialCard : ℝ) ≤
      Real.logb 2 (initialCard : ℝ) := by
    rw [Real.logb]
    have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
      convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
      norm_num
    exact (le_div_iff₀ (Real.log_pos (by norm_num))).2 (by nlinarith)
  have hXupperReal : (X.card : ℝ) ≤ (currentCard : ℝ) := by
    exact_mod_cast hXupper
  have hfraction : (X.card : ℝ) /
        Real.logb 2 (X.card : ℝ) ≤
      (2 / p) * (currentCard : ℝ) / Real.log (initialCard : ℝ) := by
    calc
      (X.card : ℝ) / Real.logb 2 (X.card : ℝ) ≤
          (currentCard : ℝ) / Real.logb 2 (X.card : ℝ) := by
        exact div_le_div_of_nonneg_right hXupperReal hlogbX.le
      _ ≤ (currentCard : ℝ) /
          ((p / 2) * Real.logb 2 (initialCard : ℝ)) := by
        exact div_le_div_of_nonneg_left hcurrentNonneg
          (mul_pos (by positivity) hlogbN) hlogbSide
      _ = (2 / p) * (currentCard : ℝ) /
          Real.logb 2 (initialCard : ℝ) := by field_simp
      _ ≤ (2 / p) * (currentCard : ℝ) /
          Real.log (initialCard : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) hlogN hlogLeLogb
  have hcoefficient : ((context.lossConstant r : ℝ) + 1) ≤ B := by
    dsimp only [B]
    exact_mod_cast
      lossConstant_add_one_le_sourceScaleSelectorCostBound context hrank
  have hrawCost := scaleSelector_loss_add_reserveBound_le
    context X hX hXtwo
  let cost : ℝ :=
    ((((context.scaleSelector exponent).chosen X hX).loss +
      ((context.scaleSelector exponent).chosen X hX).reserveBound : ℕ) : ℝ)
  have hcost : cost ≤ B * ((2 / p) * (currentCard : ℝ) /
      Real.log (initialCard : ℝ)) + 1 := by
    calc
      cost ≤ ((context.lossConstant r : ℝ) + 1) *
          (X.card : ℝ) / Real.logb 2 (X.card : ℝ) + 1 := hrawCost
      _ ≤ B * ((X.card : ℝ) /
          Real.logb 2 (X.card : ℝ)) + 1 := by
        rw [mul_div_assoc]
        gcongr
      _ ≤ B * ((2 / p) * (currentCard : ℝ) /
          Real.log (initialCard : ℝ)) + 1 := by gcongr
  have hmainHalf : Q * (B * ((2 / p) * (currentCard : ℝ) /
        Real.log (initialCard : ℝ))) ≤
      (gamma kappa K initialCard * mu kappa initialCard *
        (currentCard : ℝ)) / 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hlogGrowthN
      (div_nonneg hcurrentNonneg (by norm_num : (0 : ℝ) ≤ 2))
    field_simp [hlogN.ne', hp.ne'] at hscaled ⊢
    nlinarith
  have hpowerGrowth : 4 * Q ≤ gamma kappa K initialCard *
      mu kappa initialCard * (initialCard : ℝ) ^ p := by
    simpa only [pow_one] using hpopulationGrowthN
  have honeHalf : Q * 2 ≤
      (gamma kappa K initialCard * mu kappa initialCard *
        (currentCard : ℝ)) / 2 := by
    have h := mul_le_mul_of_nonneg_left hlower
      (mul_nonneg hgammaPos.le hmuRange.1.le)
    nlinarith
  have hQnonneg : 0 ≤ Q := hQ.le
  calc
    Q * (cost + 1) ≤
        Q * ((B * ((2 / p) * (currentCard : ℝ) /
          Real.log (initialCard : ℝ)) + 1) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hcost]) hQnonneg
    _ ≤ gamma kappa K initialCard * mu kappa initialCard *
        (currentCard : ℝ) := by nlinarith

end

end Erdos186.PZ.Intersection
