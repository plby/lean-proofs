/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZOrientedSourceCentralTail

/-!
# Central shell-zero tail with an actual replacement-rank union

A fixed source count `r` need not determine the raised favorite-site rank:
each moved domino can create zero, one, or two threshold sites.  The safe
finite rank union therefore has at most `2 * (r - s) + 1` members, where `s`
is the retained central count.  This file absorbs that linear multiplicity
into a slightly slower geometric base and retains logarithmic-square decay at
the uniform oriented source cut.
-/

open Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.HLOZShellZeroRankUnionCentralTail

open HLOZOrientedSourceCentralTail HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroCentralTail
open HLOZShellZeroReplacementProduct HLOZShellZeroReplacementNumerics
open TilingOrientedShellZeroSourcePartition

noncomputable section

/-- Safe number of possible raised favorite-site ranks at exact source count
`r`. -/
def centralReplacementRankMultiplicity (C : ℝ) (r : ℕ) : ℕ :=
  2 * (r - centralReplacementUpperCount C r) + 1

lemma centralReplacementRankMultiplicity_le (C : ℝ) (r : ℕ) :
    centralReplacementRankMultiplicity C r ≤ 2 * (r + 1) := by
  unfold centralReplacementRankMultiplicity
  omega

/-- Exact-count coefficient after paying the safe rank-union multiplicity. -/
def centralReplacementRankUnionRatio (C : ℝ) (r : ℕ) : ℝ :=
  centralReplacementRankMultiplicity C r * centralReplacementRatio C r

lemma ofReal_centralReplacementRankUnionRatio (C : ℝ) (r : ℕ) :
    ENNReal.ofReal (centralReplacementRankUnionRatio C r) =
      (centralReplacementRankMultiplicity C r : ℝ≥0∞) *
        ENNReal.ofReal (centralReplacementRatio C r) := by
  unfold centralReplacementRankUnionRatio
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- A base strictly between the old replacement base and one. -/
def rankUnionReplacementBase (C : ℝ) : ℝ :=
  (1 + replacementBase C) / 2

lemma rankUnionReplacementBase_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < rankUnionReplacementBase C := by
  unfold rankUnionReplacementBase
  positivity [replacementBase_pos hC]

lemma replacementBase_lt_rankUnionReplacementBase
    {C : ℝ} (hC : 0 ≤ C) :
    replacementBase C < rankUnionReplacementBase C := by
  unfold rankUnionReplacementBase
  linarith [replacementBase_lt_one hC]

lemma rankUnionReplacementBase_lt_one {C : ℝ} (hC : 0 ≤ C) :
    rankUnionReplacementBase C < 1 := by
  unfold rankUnionReplacementBase
  linarith [replacementBase_lt_one hC]

/-- Ratio used to absorb the extra linear rank multiplicity. -/
def rankUnionBaseRatio (C : ℝ) : ℝ :=
  replacementBase C / rankUnionReplacementBase C

lemma rankUnionBaseRatio_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ rankUnionBaseRatio C := by
  unfold rankUnionBaseRatio
  exact div_nonneg (replacementBase_nonneg hC)
    (rankUnionReplacementBase_pos hC).le

lemma rankUnionBaseRatio_lt_one {C : ℝ} (hC : 0 ≤ C) :
    rankUnionBaseRatio C < 1 := by
  unfold rankUnionBaseRatio
  exact (div_lt_one₀ (rankUnionReplacementBase_pos hC)).2
    (replacementBase_lt_rankUnionReplacementBase hC)

/-- Uniform constant after absorbing the rank-union multiplicity. -/
def rankUnionTailConstant (C : ℝ) : ℝ :=
  2 * centralTailConstant C / (1 - rankUnionBaseRatio C) ^ 2

lemma rankUnionTailConstant_pos {C : ℝ} (hC : 0 < C) :
    0 < rankUnionTailConstant C := by
  unfold rankUnionTailConstant
  have hcentral : 0 < centralTailConstant C := by
    unfold centralTailConstant
    have hq := centralBaseRatio_lt_one hC.le
    positivity
  have hq := rankUnionBaseRatio_lt_one hC.le
  positivity

lemma replacementBase_eq_rankUnionBaseRatio_mul
    {C : ℝ} (hC : 0 ≤ C) :
    replacementBase C =
      rankUnionBaseRatio C * rankUnionReplacementBase C := by
  unfold rankUnionBaseRatio
  exact (div_mul_cancel₀ (replacementBase C)
    (rankUnionReplacementBase_pos hC).ne').symm

/-- Exact-count rank-union coefficients still have a uniform geometric
majorant. -/
theorem centralReplacementRankUnionRatio_le
    {C : ℝ} (hC : 0 < C) (r : ℕ) :
    centralReplacementRankUnionRatio C r ≤
      rankUnionTailConstant C * rankUnionReplacementBase C ^ r := by
  let q := rankUnionBaseRatio C
  let b := rankUnionReplacementBase C
  have hq0 : 0 ≤ q := rankUnionBaseRatio_nonneg hC.le
  have hq1 : q < 1 := rankUnionBaseRatio_lt_one hC.le
  have hb0 : 0 ≤ b := (rankUnionReplacementBase_pos hC.le).le
  have hratio := centralReplacementRatio_le_tailConstant_mul_pow hC r
  have hmult := centralReplacementRankMultiplicity_le C r
  have hseries := nat_succ_mul_pow_le_inv_one_sub_sq hq0 hq1 r
  have hbase : replacementBase C = q * b := by
    exact replacementBase_eq_rankUnionBaseRatio_mul hC.le
  unfold centralReplacementRankUnionRatio
  calc
    (centralReplacementRankMultiplicity C r : ℝ) *
        centralReplacementRatio C r ≤
      (centralReplacementRankMultiplicity C r : ℝ) *
        (centralTailConstant C * replacementBase C ^ r) := by
          exact mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)
    _ ≤ (2 * ((r + 1 : ℕ) : ℝ)) *
        (centralTailConstant C * replacementBase C ^ r) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hmult
          · exact mul_nonneg (centralTailConstant_nonneg hC.le)
              (pow_nonneg (replacementBase_nonneg hC.le) _)
    _ = 2 * centralTailConstant C *
        ((((r + 1 : ℕ) : ℝ) * q ^ r) * b ^ r) := by
          rw [hbase, mul_pow]
          ring
    _ ≤ 2 * centralTailConstant C *
        ((1 / (1 - q) ^ 2) * b ^ r) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right hseries (pow_nonneg hb0 _)
          · exact mul_nonneg (by norm_num)
              (centralTailConstant_nonneg hC.le)
    _ = rankUnionTailConstant C * rankUnionReplacementBase C ^ r := by
          unfold rankUnionTailConstant q b
          ring

/-- Exact-count tail including all possible replacement ranks. -/
def centralReplacementRankUnionTailCost (C : ℝ) (cut : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal
    (centralReplacementRankUnionRatio C (cut + 1 + n))

/-- Closed geometric majorant for the rank-union tail. -/
def centralReplacementRankUnionTailMajorant (C : ℝ) (cut : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (rankUnionTailConstant C) *
    ENNReal.ofReal (rankUnionReplacementBase C) ^ (cut + 1) *
      (1 - ENNReal.ofReal (rankUnionReplacementBase C))⁻¹

/-- Real prefactor of the closed rank-union tail. -/
def rankUnionTailPrefactor (C : ℝ) : ℝ :=
  rankUnionTailConstant C / (1 - rankUnionReplacementBase C)

lemma rankUnionTailPrefactor_pos {C : ℝ} (hC : 0 < C) :
    0 < rankUnionTailPrefactor C := by
  unfold rankUnionTailPrefactor
  positivity [rankUnionTailConstant_pos hC,
    rankUnionReplacementBase_lt_one hC.le]

theorem centralReplacementRankUnionTailCost_le_majorant
    {C : ℝ} (hC : 0 < C) (cut : ℕ) :
    centralReplacementRankUnionTailCost C cut ≤
      centralReplacementRankUnionTailMajorant C cut := by
  unfold centralReplacementRankUnionTailCost
    centralReplacementRankUnionTailMajorant
  calc
    (∑' n : ℕ, ENNReal.ofReal
        (centralReplacementRankUnionRatio C (cut + 1 + n))) ≤
      ∑' n : ℕ, ENNReal.ofReal
        (rankUnionTailConstant C *
          rankUnionReplacementBase C ^ (cut + 1 + n)) := by
            apply ENNReal.tsum_le_tsum
            intro n
            exact ENNReal.ofReal_mono
              (centralReplacementRankUnionRatio_le hC _)
    _ = ∑' n : ℕ,
        ENNReal.ofReal (rankUnionTailConstant C) *
          ENNReal.ofReal (rankUnionReplacementBase C) ^ (cut + 1) *
            ENNReal.ofReal (rankUnionReplacementBase C) ^ n := by
          apply tsum_congr
          intro n
          rw [pow_add,
            ENNReal.ofReal_mul (rankUnionTailConstant_pos hC).le,
            ENNReal.ofReal_mul
              (pow_nonneg (rankUnionReplacementBase_pos hC.le).le _),
            ENNReal.ofReal_pow (rankUnionReplacementBase_pos hC.le).le,
            ENNReal.ofReal_pow (rankUnionReplacementBase_pos hC.le).le]
          ring
    _ = ENNReal.ofReal (rankUnionTailConstant C) *
        ENNReal.ofReal (rankUnionReplacementBase C) ^ (cut + 1) *
          ∑' n : ℕ, ENNReal.ofReal (rankUnionReplacementBase C) ^ n := by
            rw [← ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (rankUnionTailConstant C) *
        ENNReal.ofReal (rankUnionReplacementBase C) ^ (cut + 1) *
          (1 - ENNReal.ofReal (rankUnionReplacementBase C))⁻¹ := by
            rw [ENNReal.tsum_geometric]

lemma centralReplacementRankUnionTailMajorant_eq_ofReal
    {C : ℝ} (hC : 0 < C) (cut : ℕ) :
    centralReplacementRankUnionTailMajorant C cut =
      ENNReal.ofReal
        (rankUnionTailPrefactor C *
          rankUnionReplacementBase C ^ (cut + 1)) := by
  unfold centralReplacementRankUnionTailMajorant rankUnionTailPrefactor
  have hb0 := (rankUnionReplacementBase_pos hC.le).le
  have hb1 := rankUnionReplacementBase_lt_one hC.le
  have hconstant := (rankUnionTailConstant_pos hC).le
  rw [ENNReal.ofReal_mul
      (div_nonneg hconstant (sub_nonneg.mpr hb1.le)),
    ENNReal.ofReal_div_of_pos (sub_pos.mpr hb1),
    ENNReal.ofReal_sub 1 hb0, ENNReal.ofReal_one,
    ENNReal.ofReal_pow hb0]
  simp only [div_eq_mul_inv]
  ring

/-- Exponential rate of the slower rank-union base. -/
def rankUnionReplacementRate (C : ℝ) : ℝ :=
  -Real.log (rankUnionReplacementBase C)

lemma rankUnionReplacementRate_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < rankUnionReplacementRate C := by
  unfold rankUnionReplacementRate
  exact neg_pos.mpr (Real.log_neg (rankUnionReplacementBase_pos hC)
    (rankUnionReplacementBase_lt_one hC))

lemma rankUnionReplacementBase_pow_eq_exp
    {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    rankUnionReplacementBase C ^ n =
      Real.exp (-rankUnionReplacementRate C * (n : ℝ)) := by
  have hb := rankUnionReplacementBase_pos hC
  rw [show rankUnionReplacementBase C =
      Real.exp (Real.log (rankUnionReplacementBase C)) by
        rw [Real.exp_log hb]]
  rw [← Real.exp_nat_mul]
  congr 1
  unfold rankUnionReplacementRate
  ring

/-- Positive logarithmic-square rate retained after both the four oriented
source classes and the replacement-rank union. -/
def orientedRankUnionCentralTailRate (C : ℝ) : ℝ :=
  rankUnionReplacementRate C / 16

lemma orientedRankUnionCentralTailRate_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < orientedRankUnionCentralTailRate C := by
  unfold orientedRankUnionCentralTailRate
  positivity [rankUnionReplacementRate_pos hC]

/-- The safe rank-union tail retains logarithmic-square decay at the uniform
oriented `/8` source cut. -/
theorem eventually_centralReplacementRankUnionTailCost_orientedSourceCut48_le_exp
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      centralReplacementRankUnionTailCost C (orientedSourceCut48 m) ≤
        ENNReal.ofReal (Real.exp
          (-orientedRankUnionCentralTailRate C *
            Real.log (m : ℝ) ^ 2)) := by
  let A := rankUnionTailPrefactor C
  let R := rankUnionReplacementRate C
  have hA : 0 < A := rankUnionTailPrefactor_pos hC
  have hR : 0 < R := rankUnionReplacementRate_pos hC.le
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ m : ℕ in atTop,
      max 1 (16 * Real.log A / R) ≤ Real.log (m : ℝ) :=
    hlog.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with m hm
  have hlogA : Real.log A ≤ R / 16 * Real.log (m : ℝ) ^ 2 := by
    have hone : 1 ≤ Real.log (m : ℝ) := (le_max_left _ _).trans hm
    have hthreshold : 16 * Real.log A / R ≤ Real.log (m : ℝ) :=
      (le_max_right _ _).trans hm
    have hsq : Real.log (m : ℝ) ≤ Real.log (m : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (m : ℝ) - 1)]
    have hmul : 16 * Real.log A ≤ R * Real.log (m : ℝ) := by
      rw [div_le_iff₀ hR] at hthreshold
      simpa only [mul_comm] using hthreshold
    nlinarith
  have hAexp : A ≤ Real.exp
      (R / 16 * Real.log (m : ℝ) ^ 2) := by
    rw [show A = Real.exp (Real.log A) by rw [Real.exp_log hA]]
    exact Real.exp_le_exp.mpr hlogA
  have hpow : rankUnionReplacementBase C ^ (orientedSourceCut48 m + 1) ≤
      Real.exp (-(R / 8) * Real.log (m : ℝ) ^ 2) := by
    rw [rankUnionReplacementBase_pow_eq_exp hC.le]
    apply Real.exp_le_exp.mpr
    have hcut := log_sq_le_eight_mul_orientedSourceCut48_add_one m
    nlinarith
  have hreal : A *
      rankUnionReplacementBase C ^ (orientedSourceCut48 m + 1) ≤
      Real.exp (-orientedRankUnionCentralTailRate C *
        Real.log (m : ℝ) ^ 2) := by
    calc
      A * rankUnionReplacementBase C ^ (orientedSourceCut48 m + 1) ≤
          Real.exp (R / 16 * Real.log (m : ℝ) ^ 2) *
            Real.exp (-(R / 8) * Real.log (m : ℝ) ^ 2) := by
              exact mul_le_mul hAexp hpow
                (pow_nonneg (rankUnionReplacementBase_pos hC.le).le _)
                (Real.exp_pos _).le
      _ = Real.exp (-orientedRankUnionCentralTailRate C *
          Real.log (m : ℝ) ^ 2) := by
            rw [← Real.exp_add]
            unfold orientedRankUnionCentralTailRate R
            congr 1
            ring
  calc
    centralReplacementRankUnionTailCost C (orientedSourceCut48 m) ≤
        centralReplacementRankUnionTailMajorant C
          (orientedSourceCut48 m) :=
      centralReplacementRankUnionTailCost_le_majorant hC _
    _ = ENNReal.ofReal (A *
        rankUnionReplacementBase C ^ (orientedSourceCut48 m + 1)) := by
      exact centralReplacementRankUnionTailMajorant_eq_ofReal hC _
    _ ≤ ENNReal.ofReal (Real.exp
        (-orientedRankUnionCentralTailRate C *
          Real.log (m : ℝ) ^ 2)) :=
      ENNReal.ofReal_mono hreal

lemma centralReplacementRankUnionTailCost_ne_top
    {C : ℝ} (hC : 0 < C) (cut : ℕ) :
    centralReplacementRankUnionTailCost C cut ≠ ∞ := by
  apply ne_top_of_le_ne_top
    (show centralReplacementRankUnionTailMajorant C cut ≠ ∞ by
      unfold centralReplacementRankUnionTailMajorant
      apply ENNReal.mul_ne_top
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
      · apply ENNReal.inv_ne_top.mpr
        exact ne_of_gt (tsub_pos_iff_lt.mpr
          (ENNReal.ofReal_lt_one.mpr
            (rankUnionReplacementBase_lt_one hC.le))))
  exact centralReplacementRankUnionTailCost_le_majorant hC cut

private theorem ennreal_series_ne_top_of_eventually_exp_neg_log_sq_bound
    (f : ℕ → ℝ≥0∞) (hfinite : ∀ m, f m ≠ ∞)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ m : ℕ in atTop,
      f m ≤ ENNReal.ofReal
        (Real.exp (-c * Real.log (m : ℝ) ^ 2))) :
    ∑' m, f m ≠ ∞ := by
  let g : ℕ → ℝ≥0 := fun m ↦ (f m).toNNReal
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpoly : Summable (fun m : ℕ ↦ (m : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hg : Summable (fun m : ℕ ↦ (g m : ℝ)) := by
    apply Summable.of_norm_bounded_eventually hpoly
    have hbound' : ∀ᶠ m : ℕ in cofinite,
        f m ≤ ENNReal.ofReal
          (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
      simpa only [Nat.cofinite_eq_atTop] using hbound
    have hlarge : ∀ᶠ m : ℕ in cofinite,
        2 / c ≤ Real.log (m : ℝ) := by
      simpa only [Nat.cofinite_eq_atTop] using
        hlog.eventually (eventually_ge_atTop (2 / c))
    have hmpos : ∀ᶠ m : ℕ in cofinite, 0 < m := by
      simpa only [Nat.cofinite_eq_atTop] using (eventually_gt_atTop 0)
    filter_upwards [hbound', hlarge, hmpos] with m hm hlogm hmpos
    have hmReal : (f m).toReal ≤
        Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
      rw [← ENNReal.toReal_ofReal (Real.exp_nonneg _)]
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    have hlogNonneg : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hmpos)
    have hexponent : -c * Real.log (m : ℝ) ^ 2 ≤
        Real.log (m : ℝ) * (-2) := by
      have hcMul : 2 ≤ c * Real.log (m : ℝ) := by
        calc
          2 = c * (2 / c) := by field_simp
          _ ≤ c * Real.log (m : ℝ) :=
            mul_le_mul_of_nonneg_left hlogm hc.le
      nlinarith
    have hexp : Real.exp (-c * Real.log (m : ℝ) ^ 2) ≤
        (m : ℝ) ^ (-2 : ℝ) := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast hmpos)]
      exact Real.exp_le_exp.mpr hexponent
    simpa [g, ENNReal.toReal, Real.norm_eq_abs, abs_of_nonneg] using
      hmReal.trans hexp
  have hcoe : ∀ m, (g m : ℝ≥0∞) = f m := by
    intro m
    exact ENNReal.coe_toNNReal (hfinite m)
  rw [← tsum_congr hcoe]
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hg

theorem tsum_centralReplacementRankUnionTailCost_orientedSourceCut48_ne_top
    {C : ℝ} (hC : 0 < C) :
    ∑' m : ℕ,
      centralReplacementRankUnionTailCost C
        (orientedSourceCut48 m) ≠ ∞ := by
  exact ennreal_series_ne_top_of_eventually_exp_neg_log_sq_bound
    (fun m ↦ centralReplacementRankUnionTailCost C (orientedSourceCut48 m))
    (fun m ↦ centralReplacementRankUnionTailCost_ne_top hC _)
    (orientedRankUnionCentralTailRate_pos hC.le)
    (eventually_centralReplacementRankUnionTailCost_orientedSourceCut48_le_exp
      hC)

end

end Erdos1165.HLOZShellZeroRankUnionCentralTail
