/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZSharpWindowProductClosure
import ErdosProblems.Erdos1165.HLOZSourceCorrectBandProductClosure
import ErdosProblems.Erdos1165.HLOZFilteredSourceCorrectBandProductClosure
import ErdosProblems.Erdos1165.HLOZFullBetaRegimeSplit
import ErdosProblems.Erdos1165.HLOZGapBetaNumerics

/-!
# Numerical closure of the sharp positive shells

The source-correct shell-zero replacement is independent of the adjacent
positive-shell recurrence.  This file closes the latter from the literal
all-six product package when both its geometric-balance coefficient and its
interface envelope have the checked sharp-window rate.  The balance budget
is not required to vanish: the nonempty `Theta` complement is retained in
the numerical tail.
-/

open Filter
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZSharpPositiveShellNumerics

open HLOZAllSixBandProductClosure HLOZCanonicalWindowProductClosure
open HLOZFullBetaRegimeSplit HLOZPathEvents
open HLOZGapRandomClockScreen HLOZProposition48Candidates
open HLOZGapBetaNumerics
open HLOZQuarterCutCentralTail
open HLOZSharpProductNumerics HLOZSourceCorrectBandProductClosure
open HLOZFilteredSourceCorrectBandProductClosure
open HLOZShellZeroCentralTail HLOZShellZeroReplacementWindows
open HLOZTilingEndpointBandExtraction
open ScreeningInstantiation

noncomputable section

/-- Arithmetic properties of the literal positive-shell product package.
There is no event-probability field. -/
structure SharpPositiveShellBounds
    {t : TilingLazyDecomposition.DominoTiling} {m cutoff : ℕ}
    {band : RandomClockBand}
    (interfaces : AllSixBandProductData t m cutoff band) : Prop where
  balanceCost_le : ∀ (hstart : interfaces.lawStart ≤ m)
    (hm : 0 < m) shell,
    (((interfaces.balanceLaw hstart hm shell).budget : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
          ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal ≤
      Real.exp (-sharpProductRate * Real.log (m : ℝ) ^ 2)
  interfaceCost_le : ∀ shell,
    interfaces.interfaceCost shell ≤
      sharpInterfaceCost
        (geometricShellThreshold (initialBudget48 m) shellGrowth48) shell

theorem shellCount48_le_level_of_beta_le_sevenTenths
    {m : ℕ} (hm : 1 ≤ m) {beta : ℝ} (hbeta : beta ≤ (7 / 10 : ℝ)) :
    shellCount48 m beta ≤ m := by
  unfold shellCount48
  apply Nat.ceil_le.mpr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  calc
    (m : ℝ) ^ (beta - kappaOne) ≤ (m : ℝ) ^ (1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hmR
      norm_num [kappaOne] at hbeta ⊢
      linarith
    _ = m := Real.rpow_one _

theorem sharpInterfaceCost_geometric_le_exp_log_sq
    (m shell : ℕ) :
    sharpInterfaceCost
        (geometricShellThreshold (initialBudget48 m) shellGrowth48) shell ≤
      Real.exp (-sharpProductRate * Real.log (m : ℝ) ^ 2) := by
  unfold sharpInterfaceCost
  rw [Real.exp_le_exp]
  have hbudget : Real.log (m : ℝ) ^ 2 ≤ (initialBudget48 m : ℝ) := by
    unfold initialBudget48
    have hceil : Real.log (m : ℝ) ^ 2 ≤
        (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  have hthreshold : initialBudget48 m ≤
      geometricShellThreshold (initialBudget48 m) shellGrowth48 (shell + 1) := by
    unfold geometricShellThreshold
    exact Nat.le_mul_of_pos_right _ (pow_pos shellGrowth48_pos _)
  have hcast : Real.log (m : ℝ) ^ 2 ≤
      ((geometricShellThreshold (initialBudget48 m) shellGrowth48
        (shell + 1) + 1 : ℕ) : ℝ) := by
    exact hbudget.trans (by exact_mod_cast (hthreshold.trans (by omega)))
  nlinarith [sharpProductRate_pos]

/-- The real contribution of all adjacent positive shells in one band. -/
noncomputable def positiveShellRealCost
    {t : TilingLazyDecomposition.DominoTiling} {m cutoff : ℕ}
    {band : RandomClockBand}
    (interfaces : AllSixBandProductData t m cutoff band)
    (hstart : interfaces.lawStart ≤ m) (hm : 0 < m) : ℝ :=
  ∑ shell ∈ Finset.range (shellCount48 m band.beta - 1),
    ((((interfaces.balanceLaw hstart hm shell).budget : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
          ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal +
      interfaces.interfaceCost shell)

lemma positiveShellRealCost_nonneg
    {t : TilingLazyDecomposition.DominoTiling} {m cutoff : ℕ}
    {band : RandomClockBand}
    (interfaces : AllSixBandProductData t m cutoff band)
    (hstart : interfaces.lawStart ≤ m) (hm : 0 < m) :
    0 ≤ positiveShellRealCost interfaces hstart hm := by
  unfold positiveShellRealCost
  apply Finset.sum_nonneg
  intro shell _hshell
  exact add_nonneg ENNReal.toReal_nonneg
    (interfaces.interfaceCost_nonneg shell)

/-- A source-low band has at most `m` positive shells, and every sharp
interface pays the first logarithmic-square threshold. -/
theorem positiveShellRealCost_le_level_mul_exp
    {t : TilingLazyDecomposition.DominoTiling} {m cutoff : ℕ}
    {band : RandomClockBand}
    (hm : 1 ≤ m) (hbeta : band.beta ≤ (7 / 10 : ℝ))
    (interfaces : AllSixBandProductData t m cutoff band)
    (hstart : interfaces.lawStart ≤ m)
    (bounds : SharpPositiveShellBounds interfaces) :
    positiveShellRealCost interfaces hstart (by omega) ≤
      2 * (m : ℝ) * Real.exp
        (-sharpProductRate * Real.log (m : ℝ) ^ 2) := by
  unfold positiveShellRealCost
  calc
    (∑ shell ∈ Finset.range (shellCount48 m band.beta - 1),
        ((((interfaces.balanceLaw hstart (by omega) shell).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal +
          interfaces.interfaceCost shell)) ≤
        ∑ _shell ∈ Finset.range (shellCount48 m band.beta - 1),
          2 * Real.exp (-sharpProductRate * Real.log (m : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro shell _hshell
      have hbalance := bounds.balanceCost_le hstart (by omega) shell
      have hinterface := (bounds.interfaceCost_le shell).trans
        (sharpInterfaceCost_geometric_le_exp_log_sq m shell)
      nlinarith
    _ = ((shellCount48 m band.beta - 1 : ℕ) : ℝ) *
        (2 * Real.exp (-sharpProductRate * Real.log (m : ℝ) ^ 2)) := by
      simp
    _ ≤ 2 * (m : ℝ) * Real.exp
        (-sharpProductRate * Real.log (m : ℝ) ^ 2) := by
      have hcard : ((shellCount48 m band.beta - 1 : ℕ) : ℝ) ≤ m := by
        exact_mod_cast (Nat.sub_le _ _).trans
          (shellCount48_le_level_of_beta_le_sevenTenths hm hbeta)
      have hexp : 0 ≤ Real.exp
          (-sharpProductRate * Real.log (m : ℝ) ^ 2) := Real.exp_nonneg _
      nlinarith

/-- The polynomial number of positive shells is absorbed by half of the
sharp logarithmic-square exponent. -/
theorem eventually_level_mul_exp_sharp_le :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) * Real.exp
          (-sharpProductRate * Real.log (m : ℝ) ^ 2) ≤
        Real.exp
          (-(sharpProductRate / 2) * Real.log (m : ℝ) ^ 2) := by
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually
      (eventually_ge_atTop (2 / sharpProductRate)),
      eventually_ge_atTop (1 : ℕ)] with m hlarge hm
  have hmPosR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlogNonneg : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm)
  have hdominate : Real.log (m : ℝ) ≤
      (sharpProductRate / 2) * Real.log (m : ℝ) ^ 2 := by
    have hr := sharpProductRate_pos
    have hscaled : 2 ≤ sharpProductRate * Real.log (m : ℝ) := by
      calc
        2 = sharpProductRate * (2 / sharpProductRate) := by
          field_simp [hr.ne']
        _ ≤ sharpProductRate * Real.log (m : ℝ) :=
          mul_le_mul_of_nonneg_left hlarge hr.le
    nlinarith [mul_le_mul_of_nonneg_right hscaled hlogNonneg]
  calc
    (m : ℝ) * Real.exp
          (-sharpProductRate * Real.log (m : ℝ) ^ 2) =
        Real.exp (Real.log (m : ℝ)) *
          Real.exp (-sharpProductRate * Real.log (m : ℝ) ^ 2) := by
      rw [Real.exp_log hmPosR]
    _ = Real.exp (Real.log (m : ℝ) +
          -sharpProductRate * Real.log (m : ℝ) ^ 2) := by
      rw [Real.exp_add]
    _ ≤ Real.exp
          (-(sharpProductRate / 2) * Real.log (m : ℝ) ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith)

/-- The factor two from the lower and upper geometric-balance tails is
absorbed as well. -/
theorem eventually_two_level_mul_exp_sharp_le :
    ∀ᶠ m : ℕ in atTop,
      2 * (m : ℝ) * Real.exp
          (-sharpProductRate * Real.log (m : ℝ) ^ 2) ≤
        Real.exp
          (-(sharpProductRate / 4) * Real.log (m : ℝ) ^ 2) := by
  have hlevel := eventually_level_mul_exp_sharp_le
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlevel,
      hlog.eventually (eventually_ge_atTop
        (4 * Real.log 2 / sharpProductRate)),
      hlog.eventually (eventually_ge_atTop 1)] with m hlevelM hlarge hlogOne
  have hlogTwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hr := sharpProductRate_pos
  have hdominate : Real.log (2 : ℝ) ≤
      (sharpProductRate / 4) * Real.log (m : ℝ) ^ 2 := by
    have hlinear : Real.log (2 : ℝ) ≤
        (sharpProductRate / 4) * Real.log (m : ℝ) := by
      have hscaled : 4 * Real.log (2 : ℝ) ≤
          sharpProductRate * Real.log (m : ℝ) := by
        calc
          4 * Real.log (2 : ℝ) =
              sharpProductRate *
                (4 * Real.log (2 : ℝ) / sharpProductRate) := by
                  field_simp [hr.ne']
          _ ≤ sharpProductRate * Real.log (m : ℝ) :=
            mul_le_mul_of_nonneg_left hlarge hr.le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hlogOne
      (div_nonneg hr.le (by norm_num : (0 : ℝ) ≤ 4))]
  calc
    2 * (m : ℝ) * Real.exp
        (-sharpProductRate * Real.log (m : ℝ) ^ 2) ≤
      2 * Real.exp
        (-(sharpProductRate / 2) * Real.log (m : ℝ) ^ 2) := by
          nlinarith [Real.exp_pos
            (-(sharpProductRate / 2) * Real.log (m : ℝ) ^ 2)]
    _ = Real.exp (Real.log 2 +
          (-(sharpProductRate / 2) * Real.log (m : ℝ) ^ 2)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp
        (-(sharpProductRate / 4) * Real.log (m : ℝ) ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith)

/-- Totalized positive-shell coefficient; the finite prefix before the
literal product laws start receives the harmless value one. -/
noncomputable def totalPositiveShellCost
    {t : TilingLazyDecomposition.DominoTiling} {m cutoff : ℕ}
    {band : RandomClockBand}
    (interfaces : AllSixBandProductData t m cutoff band) : ℝ≥0∞ :=
  if h : interfaces.lawStart ≤ m ∧ 0 < m then
    ENNReal.ofReal (positiveShellRealCost interfaces h.1 h.2)
  else 1

/-- The geometric-balance complement at the initial shell.  This is the
`Theta ≠ ∅` contribution; it is deliberately not simplified to zero. -/
noncomputable def stageZeroBalanceCost
    {t : TilingLazyDecomposition.DominoTiling} {m cutoff : ℕ}
    {band : RandomClockBand}
    (interfaces : AllSixBandProductData t m cutoff band)
    (hstart : interfaces.lawStart ≤ m) (hm : 0 < m) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((((interfaces.balanceLaw hstart hm 0).budget : ℝ≥0∞) *
      (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
        ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal)

/-- Totalized stage-zero balance coefficient. -/
noncomputable def totalStageZeroBalanceCost
    {t : TilingLazyDecomposition.DominoTiling} {m cutoff : ℕ}
    {band : RandomClockBand}
    (interfaces : AllSixBandProductData t m cutoff band) : ℝ≥0∞ :=
  if h : interfaces.lawStart ≤ m ∧ 0 < m then
    stageZeroBalanceCost interfaces h.1 h.2
  else 1

/-- Eventual per-band positive-shell envelope, uniform over every source-low
band and independent of its scale and ranks. -/
theorem eventually_positiveShellRealCost_le_exp
    (t : TilingLazyDecomposition.DominoTiling)
    (cap externalThreshold : ℕ → ℕ)
    (interfaces : ∀ m band,
      AllSixBandProductData t m (levelCutoffTime upperTailDelta m) band)
    (hstart : ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ sourceProductEndpointBands m
        (cap m) (externalThreshold m),
        (interfaces m band).lawStart ≤ m)
    (bounds : ∀ m band, SharpPositiveShellBounds (interfaces m band)) :
    ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ sourceProductEndpointBands m
          (cap m) (externalThreshold m),
        totalPositiveShellCost (interfaces m band) ≤
          ENNReal.ofReal (Real.exp
            (-(sharpProductRate / 4) * Real.log (m : ℝ) ^ 2)) := by
  filter_upwards [hstart, eventually_two_level_mul_exp_sharp_le,
      eventually_ge_atTop (1 : ℕ)] with m hstartM habsorb hm
  intro band hband
  rw [totalPositiveShellCost, dif_pos ⟨hstartM band hband, by omega⟩]
  apply ENNReal.ofReal_mono
  exact (positiveShellRealCost_le_level_mul_exp hm
    (sourceProductEndpointBand_betaUpperRange hband)
    (interfaces m band) (hstartM band hband) (bounds m band)).trans habsorb

/-- The fixed finite family of source-low beta bands preserves a positive
logarithmic-square rate after summation. -/
theorem eventually_sum_totalPositiveShellCost_le_exp
    (t : TilingLazyDecomposition.DominoTiling)
    (cap externalThreshold : ℕ → ℕ)
    (interfaces : ∀ m band,
      AllSixBandProductData t m (levelCutoffTime upperTailDelta m) band)
    (hstart : ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ sourceProductEndpointBands m
        (cap m) (externalThreshold m),
        (interfaces m band).lawStart ≤ m)
    (bounds : ∀ m band, SharpPositiveShellBounds (interfaces m band)) :
    ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
          totalPositiveShellCost (interfaces m band) ≤
        ENNReal.ofReal (Real.exp
          (-(sharpProductRate / 8) * Real.log (m : ℝ) ^ 2)) := by
  have heach := eventually_positiveShellRealCost_le_exp t cap
    externalThreshold interfaces hstart bounds
  have hr : 0 < sharpProductRate / 8 := by
    positivity [sharpProductRate_pos]
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
    (Nat.card CanonicalEndpointLowGapBandTag) hr
  filter_upwards [heach, habsorb] with m heachM habsorbM
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (-(sharpProductRate / 4) * Real.log (m : ℝ) ^ 2))
  calc
    ∑ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
        totalPositiveShellCost (interfaces m band) ≤
      ∑ _band ∈ sourceProductEndpointBands m (cap m)
        (externalThreshold m), q := Finset.sum_le_sum heachM
    _ = ((sourceProductEndpointBands m (cap m)
        (externalThreshold m)).card : ℝ≥0∞) * q := by simp
    _ ≤ (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) * q := by
      gcongr
      exact_mod_cast sourceProductEndpointBands_card_le m (cap m)
        (externalThreshold m)
    _ ≤ ENNReal.ofReal (Real.exp
        (-(sharpProductRate / 8) * Real.log (m : ℝ) ^ 2)) := by
      simpa only [show 2 * (sharpProductRate / 8) =
        sharpProductRate / 4 by ring] using habsorbM

/-- The finite family of nonzero stage-zero balance complements has a
logarithmic-square tail. -/
theorem eventually_sum_totalStageZeroBalanceCost_le_exp
    (t : TilingLazyDecomposition.DominoTiling)
    (cap externalThreshold : ℕ → ℕ)
    (interfaces : ∀ m band,
      AllSixBandProductData t m (levelCutoffTime upperTailDelta m) band)
    (hstart : ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ sourceProductEndpointBands m
        (cap m) (externalThreshold m),
        (interfaces m band).lawStart ≤ m)
    (bounds : ∀ m band, SharpPositiveShellBounds (interfaces m band)) :
    ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
          totalStageZeroBalanceCost (interfaces m band) ≤
        ENNReal.ofReal (Real.exp
          (-(sharpProductRate / 2) * Real.log (m : ℝ) ^ 2)) := by
  have hr : 0 < sharpProductRate / 2 := by
    positivity [sharpProductRate_pos]
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
    (Nat.card CanonicalEndpointLowGapBandTag) hr
  filter_upwards [hstart, habsorb, eventually_ge_atTop (1 : ℕ)] with
      m hstartM habsorbM hm
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (-sharpProductRate * Real.log (m : ℝ) ^ 2))
  calc
    ∑ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
        totalStageZeroBalanceCost (interfaces m band) ≤
      ∑ _band ∈ sourceProductEndpointBands m (cap m)
        (externalThreshold m), q := by
          apply Finset.sum_le_sum
          intro band hband
          rw [totalStageZeroBalanceCost,
            dif_pos ⟨hstartM band hband, by omega⟩]
          unfold stageZeroBalanceCost
          exact ENNReal.ofReal_mono
            ((bounds m band).balanceCost_le
              (hstartM band hband) (by omega) 0)
    _ = ((sourceProductEndpointBands m (cap m)
        (externalThreshold m)).card : ℝ≥0∞) * q := by simp
    _ ≤ (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) * q := by
      gcongr
      exact_mod_cast sourceProductEndpointBands_card_le m (cap m)
        (externalThreshold m)
    _ ≤ ENNReal.ofReal (Real.exp
        (-(sharpProductRate / 2) * Real.log (m : ℝ) ^ 2)) := by
      simpa only [show 2 * (sharpProductRate / 2) =
        sharpProductRate by ring] using habsorbM

/-! ## Combination with the fixed-count shell-zero term -/

/-- The final rate reserved for the complete full-beta gap screen. -/
noncomputable def fullBetaSourceCorrectRate : ℝ :=
  min (centralTailRate shellZeroLocalRatioConstant / 32)
    (sharpProductRate / 32)

lemma fullBetaSourceCorrectRate_pos : 0 < fullBetaSourceCorrectRate := by
  unfold fullBetaSourceCorrectRate
  exact lt_min
    (div_pos (centralTailRate_pos
      shellZeroLocalRatioConstant_pos.le) (by norm_num))
    (div_pos sharpProductRate_pos (by norm_num))

lemma four_mul_fullBetaSourceCorrectRate_le_central :
    4 * fullBetaSourceCorrectRate ≤
      centralTailRate shellZeroLocalRatioConstant / 8 := by
  unfold fullBetaSourceCorrectRate
  have h := min_le_left
    (centralTailRate shellZeroLocalRatioConstant / 32)
    (sharpProductRate / 32)
  linarith

lemma four_mul_fullBetaSourceCorrectRate_le_quarterCut :
    4 * fullBetaSourceCorrectRate ≤
      quarterCutCentralTailRate shellZeroLocalRatioConstant / 2 := by
  have h := four_mul_fullBetaSourceCorrectRate_le_central
  unfold centralTailRate at h
  unfold quarterCutCentralTailRate
  nlinarith

lemma four_mul_fullBetaSourceCorrectRate_le_sharp :
    4 * fullBetaSourceCorrectRate ≤ sharpProductRate / 8 := by
  unfold fullBetaSourceCorrectRate
  have h := min_le_right
    (centralTailRate shellZeroLocalRatioConstant / 32)
    (sharpProductRate / 32)
  linarith

lemma centralReplacementTailCost_ne_top (m : ℕ) :
    centralReplacementTailCost shellZeroLocalRatioConstant
      (initialBudget48 m) ≠ ∞ := by
  apply ne_top_of_le_ne_top
    (tsum_centralReplacementTailCost_ne_top
      shellZeroLocalRatioConstant_pos)
  exact ENNReal.le_tsum m

/-- The source-correct totalized coefficient is exactly the shell-zero cost,
the positive-shell recurrence, and the nonzero stage-zero balance cost once
the literal laws have started. -/
theorem totalSourceCorrectBandOverflowCoefficient_eq_add
    {t : TilingLazyDecomposition.DominoTiling} {m cutoff : ℕ}
    {band : RandomClockBand}
    (data : AllSixSourceCorrectBandProductData t m cutoff band)
    (bounds : SharpPositiveShellBounds data.interfaces)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 1 < m) :
    totalSourceCorrectBandOverflowCoefficient data =
      centralReplacementTailCost shellZeroLocalRatioConstant
          (initialBudget48 m) +
        totalPositiveShellCost data.interfaces +
        totalStageZeroBalanceCost data.interfaces := by
  rw [totalSourceCorrectBandOverflowCoefficient, dif_pos ⟨hstart, hm⟩,
    totalPositiveShellCost, dif_pos ⟨hstart, by omega⟩,
    totalStageZeroBalanceCost, dif_pos ⟨hstart, by omega⟩]
  unfold sourceCorrectUnfilteredBandOverflowCoefficient
    sourceCorrectStageZeroBalanceCost stageZeroBalanceCost
  unfold sourceCorrectBandOverflowCoefficient
  change ENNReal.ofReal
      ((centralReplacementTailCost shellZeroLocalRatioConstant
        (initialBudget48 m)).toReal +
        positiveShellRealCost data.interfaces hstart (by omega)) + _ = _
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg
      (positiveShellRealCost_nonneg data.interfaces hstart (by omega)),
    ENNReal.ofReal_toReal (centralReplacementTailCost_ne_top m)]

/-- On a literal eligible source, the filtered coefficient consists only of
the central shell-zero tail and the positive-shell recurrence. -/
theorem totalFilteredSourceCorrectBandOverflowCoefficient_eq_add
    {t : TilingLazyDecomposition.DominoTiling} {m cutoff : ℕ}
    {band : RandomClockBand} {eligible : Set WalkPath}
    (data : AllSixFilteredSourceCorrectBandProductData t m cutoff band
      eligible)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 1 < m) :
    totalFilteredSourceCorrectBandOverflowCoefficient data =
      centralReplacementTailCost shellZeroLocalRatioConstant
          (sourceCut48 m) +
        totalPositiveShellCost data.interfaces := by
  rw [totalFilteredSourceCorrectBandOverflowCoefficient,
    dif_pos ⟨hstart, hm⟩, totalPositiveShellCost,
    dif_pos ⟨hstart, by omega⟩]
  unfold filteredSourceCorrectBandOverflowCoefficient
  change ENNReal.ofReal
      ((centralReplacementTailCost shellZeroLocalRatioConstant
        (sourceCut48 m)).toReal +
        positiveShellRealCost data.interfaces hstart (by omega)) = _
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg
      (positiveShellRealCost_nonneg data.interfaces hstart (by omega)),
    ENNReal.ofReal_toReal (centralReplacementTailCost_ne_top_at_cut
      shellZeroLocalRatioConstant_pos (sourceCut48 m))]

/-- The fixed finite beta family multiplies the common shell-zero tail by
only a fixed cardinality. -/
theorem eventually_sum_centralReplacementTailCost_le_exp :
    ∀ᶠ m : ℕ in atTop,
      (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) *
          centralReplacementTailCost shellZeroLocalRatioConstant
            (initialBudget48 m) ≤
        ENNReal.ofReal (Real.exp
          (-(centralTailRate shellZeroLocalRatioConstant / 2) *
            Real.log (m : ℝ) ^ 2)) := by
  have hbase :=
    eventually_centralReplacementTailCost_le_exp_neg_log_sq
      shellZeroLocalRatioConstant_pos
  have hr : 0 < centralTailRate shellZeroLocalRatioConstant / 2 := by
    positivity [centralTailRate_pos shellZeroLocalRatioConstant_pos.le]
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
    (Nat.card CanonicalEndpointLowGapBandTag) hr
  filter_upwards [hbase, habsorb] with m hbaseM habsorbM
  calc
    (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) *
        centralReplacementTailCost shellZeroLocalRatioConstant
          (initialBudget48 m) ≤
      (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp
          (-centralTailRate shellZeroLocalRatioConstant *
            Real.log (m : ℝ) ^ 2)) := by gcongr
    _ ≤ ENNReal.ofReal (Real.exp
        (-(centralTailRate shellZeroLocalRatioConstant / 2) *
          Real.log (m : ℝ) ^ 2)) := by
      simpa only [show 2 *
        (centralTailRate shellZeroLocalRatioConstant / 2) =
          centralTailRate shellZeroLocalRatioConstant by ring] using habsorbM

/-- The same fixed finite beta family at the reduced spatial-source cut. -/
theorem eventually_sum_quarterCut_centralReplacementTailCost_le_exp :
    ∀ᶠ m : ℕ in atTop,
      (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) *
          centralReplacementTailCost shellZeroLocalRatioConstant
            (sourceCut48 m) ≤
        ENNReal.ofReal (Real.exp
          (-(quarterCutCentralTailRate shellZeroLocalRatioConstant / 2) *
            Real.log (m : ℝ) ^ 2)) := by
  have hbase :=
    eventually_centralReplacementTailCost_sourceCut48_le_exp_neg_log_sq
      shellZeroLocalRatioConstant_pos
  have hr : 0 < quarterCutCentralTailRate
      shellZeroLocalRatioConstant / 2 := by
    positivity [quarterCutCentralTailRate_pos
      shellZeroLocalRatioConstant_pos.le]
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
    (Nat.card CanonicalEndpointLowGapBandTag) hr
  filter_upwards [hbase, habsorb] with m hbaseM habsorbM
  calc
    (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) *
        centralReplacementTailCost shellZeroLocalRatioConstant
          (sourceCut48 m) ≤
      (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp
          (-quarterCutCentralTailRate shellZeroLocalRatioConstant *
            Real.log (m : ℝ) ^ 2)) := by gcongr
    _ ≤ ENNReal.ofReal (Real.exp
        (-(quarterCutCentralTailRate shellZeroLocalRatioConstant / 2) *
          Real.log (m : ℝ) ^ 2)) := by
      simpa only [show 2 *
        (quarterCutCentralTailRate shellZeroLocalRatioConstant / 2) =
          quarterCutCentralTailRate shellZeroLocalRatioConstant by ring] using
            habsorbM

/-- All explicit source-correct product coefficients have the rate required
by `FullBetaSourceCorrectProductData`; no numerical tail is assumed. -/
theorem eventually_sum_totalSourceCorrectBandOverflowCoefficient_le_exp
    (t : TilingLazyDecomposition.DominoTiling)
    (cap externalThreshold : ℕ → ℕ)
    (data : ∀ m band,
      AllSixSourceCorrectBandProductData t m
        (levelCutoffTime upperTailDelta m) band)
    (hstart : ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ sourceProductEndpointBands m
        (cap m) (externalThreshold m),
        (data m band).interfaces.lawStart ≤ m)
    (bounds : ∀ m band,
      SharpPositiveShellBounds (data m band).interfaces) :
    ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
          totalSourceCorrectBandOverflowCoefficient (data m band) ≤
        ENNReal.ofReal (Real.exp
          (-(2 * fullBetaSourceCorrectRate) *
            Real.log (m : ℝ) ^ 2)) := by
  have hpositive := eventually_sum_totalPositiveShellCost_le_exp t cap
    externalThreshold (fun m band ↦ (data m band).interfaces)
    hstart bounds
  have hstage := eventually_sum_totalStageZeroBalanceCost_le_exp t cap
    externalThreshold (fun m band ↦ (data m band).interfaces)
    hstart bounds
  have hbaseAll := eventually_sum_centralReplacementTailCost_le_exp
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
    3 (show 0 < 2 * fullBetaSourceCorrectRate by
      positivity [fullBetaSourceCorrectRate_pos])
  filter_upwards [hstart, hpositive, hstage, hbaseAll, habsorb,
      eventually_ge_atTop (2 : ℕ)] with
      m hstartM hpositiveM hstageM hbaseM habsorbM hm
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (-(4 * fullBetaSourceCorrectRate) * Real.log (m : ℝ) ^ 2))
  have hbaseSubset :
      ∑ _band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
          centralReplacementTailCost shellZeroLocalRatioConstant
            (initialBudget48 m) ≤ q := by
    calc
      ∑ _band ∈ sourceProductEndpointBands m (cap m)
          (externalThreshold m),
          centralReplacementTailCost shellZeroLocalRatioConstant
            (initialBudget48 m) ≤
        (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) *
          centralReplacementTailCost shellZeroLocalRatioConstant
            (initialBudget48 m) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          gcongr
          exact_mod_cast sourceProductEndpointBands_card_le m (cap m)
            (externalThreshold m)
      _ ≤ ENNReal.ofReal (Real.exp
          (-(centralTailRate shellZeroLocalRatioConstant / 2) *
            Real.log (m : ℝ) ^ 2)) := hbaseM
      _ ≤ q := by
        apply ENNReal.ofReal_mono
        apply Real.exp_le_exp.mpr
        have hL : 0 ≤ Real.log (m : ℝ) ^ 2 := sq_nonneg _
        nlinarith [four_mul_fullBetaSourceCorrectRate_le_central,
          centralTailRate_pos shellZeroLocalRatioConstant_pos.le]
  have hpositive' :
      ∑ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
          totalPositiveShellCost (data m band).interfaces ≤ q := by
    refine hpositiveM.trans ?_
    apply ENNReal.ofReal_mono
    apply Real.exp_le_exp.mpr
    have hL : 0 ≤ Real.log (m : ℝ) ^ 2 := sq_nonneg _
    nlinarith [four_mul_fullBetaSourceCorrectRate_le_sharp,
      sharpProductRate_pos]
  have hstage' :
      ∑ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
          totalStageZeroBalanceCost (data m band).interfaces ≤ q := by
    refine hstageM.trans ?_
    apply ENNReal.ofReal_mono
    apply Real.exp_le_exp.mpr
    have hL : 0 ≤ Real.log (m : ℝ) ^ 2 := sq_nonneg _
    nlinarith [four_mul_fullBetaSourceCorrectRate_le_sharp,
      sharpProductRate_pos]
  calc
    ∑ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
        totalSourceCorrectBandOverflowCoefficient (data m band) =
      (∑ _band ∈ sourceProductEndpointBands m (cap m)
          (externalThreshold m),
          centralReplacementTailCost shellZeroLocalRatioConstant
            (initialBudget48 m)) +
        ∑ band ∈ sourceProductEndpointBands m (cap m)
          (externalThreshold m),
          totalPositiveShellCost (data m band).interfaces +
        ∑ band ∈ sourceProductEndpointBands m (cap m)
          (externalThreshold m),
          totalStageZeroBalanceCost (data m band).interfaces := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro band hband
      exact totalSourceCorrectBandOverflowCoefficient_eq_add
        (data m band) (bounds m band) (hstartM band hband) (by omega)
    _ ≤ q + q + q := add_le_add (add_le_add hbaseSubset hpositive') hstage'
    _ = (3 : ℝ≥0∞) * q := by ring
    _ ≤ ENNReal.ofReal (Real.exp
        (-(2 * fullBetaSourceCorrectRate) *
          Real.log (m : ℝ) ^ 2)) := by
      dsimp [q]
      have hfour : -(2 * (2 * fullBetaSourceCorrectRate)) *
          Real.log (m : ℝ) ^ 2 =
          -(4 * fullBetaSourceCorrectRate) *
            Real.log (m : ℝ) ^ 2 := by ring
      rw [hfour] at habsorbM
      exact habsorbM

/-- Numerical tail for the honest eligible-source candidate family.  The
complement of the eligible source is intentionally absent and must be paid
by the separate Proposition 4.5 balance screen. -/
theorem eventually_sum_totalFilteredSourceCorrectBandOverflowCoefficient_le_exp
    (t : TilingLazyDecomposition.DominoTiling)
    (cap externalThreshold : ℕ → ℕ)
    (eligible : ∀ m, RandomClockBand → Set WalkPath)
    (data : ∀ m band,
      AllSixFilteredSourceCorrectBandProductData t m
        (levelCutoffTime upperTailDelta m) band (eligible m band))
    (hstart : ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ sourceProductEndpointBands m
        (cap m) (externalThreshold m),
        (data m band).interfaces.lawStart ≤ m)
    (bounds : ∀ m band,
      SharpPositiveShellBounds (data m band).interfaces) :
    ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
          totalFilteredSourceCorrectBandOverflowCoefficient (data m band) ≤
        ENNReal.ofReal (Real.exp
          (-(2 * fullBetaSourceCorrectRate) *
            Real.log (m : ℝ) ^ 2)) := by
  have hpositive := eventually_sum_totalPositiveShellCost_le_exp t cap
    externalThreshold (fun m band ↦ (data m band).interfaces)
    hstart bounds
  have hbaseAll :=
    eventually_sum_quarterCut_centralReplacementTailCost_le_exp
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
    2 (show 0 < 2 * fullBetaSourceCorrectRate by
      positivity [fullBetaSourceCorrectRate_pos])
  filter_upwards [hstart, hpositive, hbaseAll, habsorb,
      eventually_ge_atTop (2 : ℕ)] with
      m hstartM hpositiveM hbaseM habsorbM hm
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (-(4 * fullBetaSourceCorrectRate) * Real.log (m : ℝ) ^ 2))
  have hbaseSubset :
      ∑ _band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
          centralReplacementTailCost shellZeroLocalRatioConstant
            (sourceCut48 m) ≤ q := by
    calc
      ∑ _band ∈ sourceProductEndpointBands m (cap m)
          (externalThreshold m),
          centralReplacementTailCost shellZeroLocalRatioConstant
            (sourceCut48 m) ≤
        (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) *
          centralReplacementTailCost shellZeroLocalRatioConstant
            (sourceCut48 m) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          gcongr
          exact_mod_cast sourceProductEndpointBands_card_le m (cap m)
            (externalThreshold m)
      _ ≤ ENNReal.ofReal (Real.exp
          (-(quarterCutCentralTailRate shellZeroLocalRatioConstant / 2) *
            Real.log (m : ℝ) ^ 2)) := hbaseM
      _ ≤ q := by
        apply ENNReal.ofReal_mono
        apply Real.exp_le_exp.mpr
        have hL : 0 ≤ Real.log (m : ℝ) ^ 2 := sq_nonneg _
        nlinarith [four_mul_fullBetaSourceCorrectRate_le_quarterCut]
  have hpositive' :
      ∑ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
          totalPositiveShellCost (data m band).interfaces ≤ q := by
    refine hpositiveM.trans ?_
    apply ENNReal.ofReal_mono
    apply Real.exp_le_exp.mpr
    have hL : 0 ≤ Real.log (m : ℝ) ^ 2 := sq_nonneg _
    nlinarith [four_mul_fullBetaSourceCorrectRate_le_sharp,
      sharpProductRate_pos]
  calc
    ∑ band ∈ sourceProductEndpointBands m (cap m) (externalThreshold m),
        totalFilteredSourceCorrectBandOverflowCoefficient (data m band) =
      (∑ _band ∈ sourceProductEndpointBands m (cap m)
          (externalThreshold m),
          centralReplacementTailCost shellZeroLocalRatioConstant
            (sourceCut48 m)) +
        ∑ band ∈ sourceProductEndpointBands m (cap m)
          (externalThreshold m),
          totalPositiveShellCost (data m band).interfaces := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro band hband
      exact totalFilteredSourceCorrectBandOverflowCoefficient_eq_add
        (data m band) (hstartM band hband) (by omega)
    _ ≤ q + q := add_le_add hbaseSubset hpositive'
    _ = (2 : ℝ≥0∞) * q := (two_mul q).symm
    _ ≤ ENNReal.ofReal (Real.exp
        (-(2 * fullBetaSourceCorrectRate) *
          Real.log (m : ℝ) ^ 2)) := by
      dsimp [q]
      have hfour : -(2 * (2 * fullBetaSourceCorrectRate)) *
          Real.log (m : ℝ) ^ 2 =
          -(4 * fullBetaSourceCorrectRate) *
            Real.log (m : ℝ) ^ 2 := by ring
      rw [hfour] at habsorbM
      exact habsorbM

end

end Erdos1165.HLOZSharpPositiveShellNumerics
