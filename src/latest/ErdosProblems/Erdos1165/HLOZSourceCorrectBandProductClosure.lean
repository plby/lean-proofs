/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAllSixBaseProductClosure
import ErdosProblems.Erdos1165.TilingShellZeroFactoredCapScreen

/-!
# Source-correct initial-shell band closure

The first shell in Proposition 4.8 cannot be bounded uniformly on every
retained trace.  This module replaces that invalid step by the global
`B_η` replacement screen.  Adjacent positive shells continue to use the
checked all-six balance/product recurrence.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZSourceCorrectBandProductClosure

open LazyDecomposition

open HLOZAllSixBandProductClosure HLOZAllSixBaseProductClosure
open HLOZDynamicThresholdedScreening HLOZGapEstimate
open HLOZGapRandomClockScreen HLOZLowScaleCandidateOverflow
open HLOZProposition48Candidates HLOZShellZeroExactCountScreen
open HLOZShellZeroReplacementProduct
open HLOZShellZeroReplacementNumerics HLOZShellZeroReplacementWindows
open HLOZShellZeroCentralTail
open HLOZShellZeroExternalWindow
open HLOZThresholdedShellScreening
open HLOZTilingGapRandomClockScreen NearFavoriteShells
open NearFavoriteThresholded ScreeningInstantiation
open TilingShellZeroSourcePartition
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroFactoredCapScreen TilingVariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := TilingLazyDecomposition.DominoTiling

/-- One all-six band with a global, source-correct initial-shell screen and
literal positive-shell interface products. -/
structure AllSixSourceCorrectBandProductData
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) where
  interfaces : AllSixBandProductData t m cutoff band
  sourceOrientation : Orientation
  baseLow : ℕ
  baseExternalLow : ℕ
  baseExternalHigh : ℕ
  base : ∀ (n : ℕ),
    ∀ eta : LiteralShellZeroSupportedTraceIndex t sourceOrientation m
      band.oldRank baseLow
      baseExternalLow baseExternalHigh (initialBudget48 m + 1 + n),
    LiteralShellZeroStoppedCoordinateSpec t sourceOrientation m
      band.oldRank baseLow
      baseExternalLow baseExternalHigh (initialBudget48 m + 1 + n) eta.1
  shellZero_good :
    shellOverflow (tilingBandOccupancy t m cutoff band)
        (geometricShellThreshold (initialBudget48 m) shellGrowth48) 0 ∩
        interfaces.balanced 0 ⊆
      orientedShellZeroSourceEvent t sourceOrientation m band.oldRank
        (shellWidth48 m) baseLow
        baseExternalLow baseExternalHigh (initialBudget48 m)

/-- The correctly filtered first-shell event.  The central replacement is
not applied to the unconditional truncated-clock overflow. -/
def sourceCorrectBandShellZeroEvent
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixSourceCorrectBandProductData t m cutoff band) :
    Set WalkPath :=
  shellOverflow (tilingBandOccupancy t m cutoff band)
      (geometricShellThreshold (initialBudget48 m) shellGrowth48) 0 ∩
    data.interfaces.balanced 0

/-- The source-correct coefficient: the false one-point/Tonelli base term
is replaced by the global fixed-ratio replacement cost. -/
noncomputable def sourceCorrectBandOverflowCoefficient
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixSourceCorrectBandProductData t m cutoff band)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 0 < m) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((centralReplacementTailCost shellZeroLocalRatioConstant
        (initialBudget48 m)).toReal +
      ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
        ((((data.interfaces.balanceLaw hstart hm j).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal
                (Real.exp (-17 * balanceRateScale m)))).toReal +
          data.interfaces.interfaceCost j))

/-- The one additional balance-complement charge needed to pass from the
stage-good shell-zero estimate back to the unconditional band overflow. -/
noncomputable def sourceCorrectStageZeroBalanceCost
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixSourceCorrectBandProductData t m cutoff band)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 0 < m) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((((data.interfaces.balanceLaw hstart hm 0).budget : ℝ≥0∞) *
      (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
        ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal)

/-- Full per-band coefficient after routing the complement of the
stage-zero good predicate to its existing geometric balance law. -/
noncomputable def sourceCorrectUnfilteredBandOverflowCoefficient
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixSourceCorrectBandProductData t m cutoff band)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 0 < m) : ℝ≥0∞ :=
  sourceCorrectBandOverflowCoefficient data hstart hm +
    sourceCorrectStageZeroBalanceCost data hstart hm

lemma measureReal_sourceCorrectBandShellZeroEvent_le
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixSourceCorrectBandProductData t m cutoff band)
    (hm : 1 < m) (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m data.baseExternalLow
      data.baseExternalHigh) :
    simpleRandomWalk.real (sourceCorrectBandShellZeroEvent data) ≤
      (centralReplacementTailCost shellZeroLocalRatioConstant
        (initialBudget48 m)).toReal := by
  have hmeasure : simpleRandomWalk (sourceCorrectBandShellZeroEvent data) ≤
      centralReplacementTailCost shellZeroLocalRatioConstant
        (initialBudget48 m) :=
    (measure_mono data.shellZero_good).trans
      (simpleRandomWalk_shellZeroSourceEvent_le_of_factoredCapData
        t data.sourceOrientation m band.oldRank data.baseLow data.baseExternalLow
          data.baseExternalHigh m hm band.oldRank_pos
            harithmetic
            (fun n eta ↦
              (data.base n eta).toFactoredCapData hexternal))
  have htop : centralReplacementTailCost shellZeroLocalRatioConstant
      (initialBudget48 m) ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (tsum_centralReplacementTailCost_ne_top
        shellZeroLocalRatioConstant_pos)
    exact ENNReal.le_tsum m
  exact ENNReal.toReal_mono htop hmeasure

/-- Restricted shell propagation: only the initial shell is intersected
with the source-correct rank-stage event; all positive-interface failures
remain the already checked unconditional interface costs. -/
theorem measureReal_inter_totalOverflow_le_of_geometricBalance_and_interfaceProduct
    {Omega Site : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (source : Set Omega)
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount m : ℕ)
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1))
    (balanceLaw : ∀ j,
      GeometricBalanceLaw (Site := Site) mu (balanced j) m)
    (productLaw : ThresholdedInterfaceProductLaw mu balanced occupancy
      threshold G shellCount)
    {baseCost : ℝ}
    (hbase : mu.real (shellOverflow occupancy threshold 0 ∩ source) ≤
      baseCost) :
    mu.real (totalOverflow occupancy threshold shellCount ∩ source) ≤
      baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        ((((balanceLaw j).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal +
          productLaw.cost j) := by
  have hsubset : totalOverflow occupancy threshold shellCount ∩ source ⊆
      (shellOverflow occupancy threshold 0 ∩ source) ∪
        someThresholdedInterfaceBad balanced occupancy threshold G
          shellCount := by
    rintro omega ⟨hoverflow, hsource⟩
    rcases totalOverflow_subset_thresholdedGlobalBad balanced occupancy
      threshold G shellCount hstep hoverflow with hzero | hinterface
    · exact Or.inl ⟨hzero, hsource⟩
    · exact Or.inr hinterface
  calc
    mu.real (totalOverflow occupancy threshold shellCount ∩ source) ≤
        mu.real ((shellOverflow occupancy threshold 0 ∩ source) ∪
          someThresholdedInterfaceBad balanced occupancy threshold G
            shellCount) := measureReal_mono hsubset
    _ ≤ mu.real (shellOverflow occupancy threshold 0 ∩ source) +
        mu.real (someThresholdedInterfaceBad balanced occupancy threshold G
          shellCount) := measureReal_union_le _ _
    _ ≤ baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        mu.real (thresholdedInterfaceBad balanced occupancy threshold G j) := by
      gcongr
      exact measureReal_biUnion_finset_le (Finset.range (shellCount - 1)) _
    _ ≤ baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        ((((balanceLaw j).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal +
          productLaw.cost j) := by
      gcongr with j hj
      have hjlt : j < shellCount - 1 := Finset.mem_range.mp hj
      calc
        mu.real (thresholdedInterfaceBad balanced occupancy threshold G j) ≤
            mu.real (balanced j)ᶜ +
              mu.real (balanced j ∩
                thresholdedGrowthFailure occupancy threshold G j) :=
          measureReal_thresholdedInterfaceBad_le mu balanced occupancy
            threshold G j
        _ ≤ (((balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            productLaw.cost j :=
          add_le_add
            (measureReal_compl_le_of_geometricBalanceLaw mu (balanced j) m
              (balanceLaw j))
            (productLaw.interface_bound j hjlt)

/-- Per-band candidate overflow with a globally screened initial shell.
No stopped-trace-uniform shell-zero estimate is used. -/
theorem simpleRandomWalk_filtered_tilingRandomClockBandOverflow_le_of_sourceCorrectData
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (hbudget : CandidateBudgetArithmeticAt m)
    (hbeta : kappaOne ≤ band.beta)
    (data : AllSixSourceCorrectBandProductData t m cutoff band)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 1 < m)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m data.baseExternalLow
      data.baseExternalHigh) :
    simpleRandomWalk
        ({s | candidateBudget48 m band.beta <
          (tilingRandomClockBandSites t m cutoff s band).card} ∩
          data.interfaces.balanced 0) ≤
      sourceCorrectBandOverflowCoefficient data hstart
        (Nat.zero_lt_of_lt hm) := by
  have hm0 : 0 < m := Nat.zero_lt_of_lt hm
  let occupancy := tilingBandOccupancy t m cutoff band
  let threshold := geometricShellThreshold (initialBudget48 m) shellGrowth48
  let source := data.interfaces.balanced 0
  have hbase : simpleRandomWalk.real
      (shellOverflow occupancy threshold 0 ∩ source) ≤
      (centralReplacementTailCost shellZeroLocalRatioConstant
        (initialBudget48 m)).toReal := by
    simpa only [occupancy, threshold, source,
      sourceCorrectBandShellZeroEvent] using
      measureReal_sourceCorrectBandShellZeroEvent_le data hm harithmetic
        hexternal
  have hstep : ∀ j, j + 1 < shellCount48 m band.beta →
      shellGrowth48 * threshold j ≤ threshold (j + 1) := by
    intro j _
    exact (geometricShellThreshold_step (initialBudget48 m)
      shellGrowth48 j).le
  let screen := tilingBandInterfaceScreenOfProductData
    data.interfaces hstart hm0
  have htotal :=
    measureReal_inter_totalOverflow_le_of_geometricBalance_and_interfaceProduct
      simpleRandomWalk source screen.balanced occupancy threshold shellGrowth48
      (shellCount48 m band.beta) m hstep screen.balanceLaw
      screen.interfaceLaw hbase
  have hreal : simpleRandomWalk.real
      ({s | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m cutoff s band).card} ∩ source) ≤
      (centralReplacementTailCost shellZeroLocalRatioConstant
        (initialBudget48 m)).toReal +
        ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
          ((((data.interfaces.balanceLaw hstart hm0 j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            data.interfaces.interfaceCost j) := by
    apply (measureReal_mono ?_).trans htotal
    intro s hs
    refine ⟨?_, hs.2⟩
    dsimp only [occupancy, threshold]
    rw [tilingRandomClockBandOverflow_eq_dynamic] at hs
    exact dynamicStoppedCandidateOverflow48_subset_totalOverflow
      (tilingRandomClockVisitedSites t m cutoff band)
      (tilingRandomClockExternalLargeEvent t m cutoff band)
      (tilingRandomClockDistinguishedSites t m cutoff band)
      (tilingRandomClockTotalLocalTime m cutoff band) m band.beta
      (hbudget band.beta hbeta) hs.1
  rw [← ENNReal.ofReal_toReal (measure_ne_top simpleRandomWalk
    ({s | candidateBudget48 m band.beta <
      (tilingRandomClockBandSites t m cutoff s band).card} ∩ source))]
  exact ENNReal.ofReal_mono hreal

/-- Unconditional band overflow obtained by the literal split into the
stage-good source and the already charged stage-zero balance complement. -/
theorem simpleRandomWalk_tilingRandomClockBandOverflow_le_of_sourceCorrectData
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (hbudget : CandidateBudgetArithmeticAt m)
    (hbeta : kappaOne ≤ band.beta)
    (data : AllSixSourceCorrectBandProductData t m cutoff band)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 1 < m)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m data.baseExternalLow
      data.baseExternalHigh) :
    simpleRandomWalk
        {s | candidateBudget48 m band.beta <
          (tilingRandomClockBandSites t m cutoff s band).card} ≤
      sourceCorrectUnfilteredBandOverflowCoefficient data hstart
        (Nat.zero_lt_of_lt hm) := by
  let bad := {s : WalkPath | candidateBudget48 m band.beta <
    (tilingRandomClockBandSites t m cutoff s band).card}
  let good := data.interfaces.balanced 0
  have hsplit : bad ⊆ (bad ∩ good) ∪ goodᶜ := by
    intro s hs
    by_cases hgood : s ∈ good
    · exact Or.inl ⟨hs, hgood⟩
    · exact Or.inr hgood
  have hfiltered : simpleRandomWalk (bad ∩ good) ≤
      sourceCorrectBandOverflowCoefficient data hstart
        (Nat.zero_lt_of_lt hm) := by
    exact simpleRandomWalk_filtered_tilingRandomClockBandOverflow_le_of_sourceCorrectData
      hbudget hbeta data hstart hm
      harithmetic hexternal
  have hbalanceReal : simpleRandomWalk.real goodᶜ ≤
      ((((data.interfaces.balanceLaw hstart (Nat.zero_lt_of_lt hm) 0).budget :
          ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
          ENNReal.ofReal
            (Real.exp (-17 * balanceRateScale m)))).toReal) :=
    measureReal_compl_le_of_geometricBalanceLaw simpleRandomWalk good m
      (data.interfaces.balanceLaw hstart (Nat.zero_lt_of_lt hm) 0)
  have hbalance : simpleRandomWalk goodᶜ ≤
      sourceCorrectStageZeroBalanceCost data hstart
        (Nat.zero_lt_of_lt hm) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top simpleRandomWalk goodᶜ)]
    exact ENNReal.ofReal_mono hbalanceReal
  exact (measure_mono hsplit).trans <|
    (measure_union_le _ _).trans <|
      add_le_add hfiltered hbalance

/-- Totalized source-correct coefficient for eventual finite-band
statements.  Only the finite prefix below the positive-tail law start is
assigned the trivial value one. -/
noncomputable def totalSourceCorrectBandOverflowCoefficient
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixSourceCorrectBandProductData t m cutoff band) : ℝ≥0∞ :=
  if htail : data.interfaces.lawStart ≤ m ∧ 1 < m then
    sourceCorrectUnfilteredBandOverflowCoefficient data htail.1
      (Nat.zero_lt_of_lt htail.2)
  else 1

/-- Finite-band estimate after the stage-good/balance-complement split has
been performed separately in every band. -/
theorem eventually_simpleRandomWalk_tilingRandomClockCandidateOverflow_le_sum_of_sourceCorrectData
    (t : DominoTiling)
    (cutoff : ℕ → ℕ) (bands : ℕ → Finset RandomClockBand)
    (hbeta : ∀ m band, band ∈ bands m → kappaOne ≤ band.beta)
    (data : ∀ m band,
      AllSixSourceCorrectBandProductData t m (cutoff m) band)
    (hstart : ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ bands m, (data m band).interfaces.lawStart ≤ m)
    (hexternal : ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ bands m,
        ShellZeroExternalWindowArithmeticAt m
          (data m band).baseExternalLow
          (data m band).baseExternalHigh) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (tilingRandomClockCandidateOverflow t m (cutoff m) (bands m)) ≤
        ∑ band ∈ bands m,
          totalSourceCorrectBandOverflowCoefficient (data m band) := by
  filter_upwards [eventually_candidateBudgetArithmeticAt,
      eventually_shellZeroWindowArithmeticAt, hstart, hexternal,
      eventually_ge_atTop (2 : ℕ)] with m hbudget harithmetic hstartM
        hexternalM hm
  unfold tilingRandomClockCandidateOverflow candidateOverflow
  refine (Screening.measure_someCandidateBad_le_sum simpleRandomWalk
    (bands m) (fun band ↦
      {s | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m (cutoff m) s band).card})).trans ?_
  apply Finset.sum_le_sum
  intro band hband
  rw [totalSourceCorrectBandOverflowCoefficient,
    dif_pos ⟨hstartM band hband, by omega⟩]
  exact simpleRandomWalk_tilingRandomClockBandOverflow_le_of_sourceCorrectData
    hbudget (hbeta m band hband) (data m band)
      (hstartM band hband) (by omega) harithmetic
        (hexternalM band hband)

end

end Erdos1165.HLOZSourceCorrectBandProductClosure
