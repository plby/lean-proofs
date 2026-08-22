/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAllSixBandProductClosure
import ErdosProblems.Erdos1165.HLOZQuarterCutCentralTail
import ErdosProblems.Erdos1165.TilingShellZeroCutFactoredCapScreen

/-!
# Stage-filtered source-correct Proposition 4.8 screen

The fixed-count shell-zero replacement applies only on the literal
`D_eta ∩ {Theta_eta = ∅}` source region.  In particular it does not bound an
unconditional first-shell overflow.  This file keeps the required source
restriction visible: the candidate overflow is intersected with an eligible
old-history region, and only its first-shell part is routed to the literal
shell-zero source event.  The adjacent positive shells retain the checked
all-six balance/product recurrence.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZFilteredSourceCorrectBandProductClosure

open LazyDecomposition

open HLOZAllSixBandProductClosure HLOZDynamicThresholdedScreening
open HLOZGapEstimate HLOZGapRandomClockScreen
open HLOZLowScaleCandidateOverflow HLOZPathEvents
open HLOZProposition48Candidates HLOZShellZeroCentralTail
open HLOZQuarterCutCentralTail
open HLOZShellZeroExternalWindow
open HLOZShellZeroReplacementWindows HLOZTilingGapRandomClockScreen
open HLOZThresholdedShellScreening
open NearFavoriteShells NearFavoriteThresholded ScreeningInstantiation
open TilingShellZeroFactoredCapScreen TilingShellZeroLiteralScreen
open TilingShellZeroCutFactoredCapScreen
open TilingShellZeroSourcePartition
open TilingOrientedShellZeroSourcePartition
open TilingVariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := TilingLazyDecomposition.DominoTiling

/-- A finite shell recurrence with its initial shell restricted to an
eligible source region.  No restriction is placed on the already screened
positive-shell interface failures. -/
theorem measureReal_inter_totalOverflow_le_of_geometricBalance_and_interfaceProduct
    {Omega Site : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (eligible : Set Omega)
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount m : ℕ)
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1))
    (balanceLaw : ∀ j,
      GeometricBalanceLaw (Site := Site) mu (balanced j) m)
    (productLaw : ThresholdedInterfaceProductLaw mu balanced occupancy
      threshold G shellCount)
    {baseCost : ℝ}
    (hbase : mu.real (eligible ∩ shellOverflow occupancy threshold 0) ≤
      baseCost) :
    mu.real (eligible ∩ totalOverflow occupancy threshold shellCount) ≤
      baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        ((((balanceLaw j).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal +
          productLaw.cost j) := by
  have hsubset : eligible ∩ totalOverflow occupancy threshold shellCount ⊆
      (eligible ∩ shellOverflow occupancy threshold 0) ∪
        someThresholdedInterfaceBad balanced occupancy threshold G
          shellCount := by
    rintro omega ⟨heligible, hoverflow⟩
    have hbad := totalOverflow_subset_thresholdedGlobalBad balanced occupancy
      threshold G shellCount hstep hoverflow
    rcases hbad with hzero | hinterface
    · exact Or.inl ⟨heligible, hzero⟩
    · exact Or.inr hinterface
  calc
    mu.real (eligible ∩ totalOverflow occupancy threshold shellCount) ≤
        mu.real (eligible ∩ shellOverflow occupancy threshold 0) +
          mu.real (someThresholdedInterfaceBad balanced occupancy threshold
            G shellCount) :=
      (measureReal_mono hsubset).trans (measureReal_union_le _ _)
    _ ≤ baseCost +
        ∑ j ∈ Finset.range (shellCount - 1),
          mu.real (thresholdedInterfaceBad balanced occupancy threshold G j) := by
      exact add_le_add hbase
        (measureReal_biUnion_finset_le (Finset.range (shellCount - 1)) _)
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
        _ ≤ ((((balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            productLaw.cost j) :=
          add_le_add
            (measureReal_compl_le_of_geometricBalanceLaw mu (balanced j) m
              (balanceLaw j))
            (productLaw.interface_bound j hjlt)

/-- Literal data for one eligible all-six band.  The base input is the
stopped-fibre product identity at every exact source count, rather than an
assumed exact-count screen or a probability estimate.  `base_subset` is the
deterministic source-identification seam: it is deliberately restricted by
`eligible`, since the corresponding unconditional inclusion is false. -/
structure AllSixFilteredSourceCorrectBandProductData
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (eligible : Set WalkPath) where
  interfaces : AllSixBandProductData t m cutoff band
  sourceOrientation : Orientation
  low : ℕ
  externalLow : ℕ
  externalHigh : ℕ
  baseFibers : ∀ (n : ℕ),
    ∀ eta : LiteralShellZeroSupportedTraceIndex t sourceOrientation m
      band.oldRank low
      externalLow externalHigh (sourceCut48 m + 1 + n),
    LiteralShellZeroStoppedCoordinateSpec t sourceOrientation m
      band.oldRank low externalLow
      externalHigh (sourceCut48 m + 1 + n) eta.1
  base_subset :
    eligible ∩ shellOverflow (tilingBandOccupancy t m cutoff band)
      (geometricShellThreshold (initialBudget48 m) shellGrowth48) 0 ⊆
        orientedShellZeroSourceEvent t sourceOrientation m band.oldRank
          (shellWidth48 m) low
          externalLow externalHigh (sourceCut48 m)

/-- Build the filtered band package on the literal shell-zero source itself.
This constructor removes the arbitrary pathwise `base_subset` seam: source
identification is true by construction, while an upstream stage split must
pay the complement of this exact source separately. -/
noncomputable def literalSourceFilteredBandProductData
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (preliminary : Set WalkPath)
    (interfaces : AllSixBandProductData t m cutoff band)
    (sourceOrientation : Orientation)
    (low externalLow externalHigh : ℕ)
    (baseFibers : ∀ (n : ℕ),
      ∀ eta : LiteralShellZeroSupportedTraceIndex t sourceOrientation m
        band.oldRank low
        externalLow externalHigh (sourceCut48 m + 1 + n),
      LiteralShellZeroStoppedCoordinateSpec t sourceOrientation m
        band.oldRank low externalLow
        externalHigh (sourceCut48 m + 1 + n) eta.1) :
    AllSixFilteredSourceCorrectBandProductData t m cutoff band
      (orientedFilteredShellZeroSourceEvent preliminary t sourceOrientation m
        band.oldRank (shellWidth48 m) low externalLow externalHigh
          (sourceCut48 m)) where
  interfaces := interfaces
  sourceOrientation := sourceOrientation
  low := low
  externalLow := externalLow
  externalHigh := externalHigh
  baseFibers := baseFibers
  base_subset := by
    rintro s ⟨hsource, _hoverflow⟩
    exact hsource.2

/-- Explicit coefficient for one stage-filtered source-correct band. -/
noncomputable def filteredSourceCorrectBandOverflowCoefficient
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    {eligible : Set WalkPath}
    (data : AllSixFilteredSourceCorrectBandProductData t m cutoff band
      eligible)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 0 < m) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((centralReplacementTailCost shellZeroLocalRatioConstant
        (sourceCut48 m)).toReal +
      ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
        ((((data.interfaces.balanceLaw hstart hm j).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal
                (Real.exp (-17 * balanceRateScale m)))).toReal +
          data.interfaces.interfaceCost j))

lemma centralReplacementTailCost_ne_top (m : ℕ) :
    centralReplacementTailCost shellZeroLocalRatioConstant
      (sourceCut48 m) ≠ ∞ :=
  centralReplacementTailCost_ne_top_at_cut
    shellZeroLocalRatioConstant_pos _

/-- The correct per-band estimate: only the eligible part of the candidate
overflow is charged to the literal fixed-count shell-zero source. -/
theorem simpleRandomWalk_tilingRandomClockBandOverflow_inter_le_of_filteredSourceCorrectData
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    {eligible : Set WalkPath}
    (hbudget : CandidateBudgetArithmeticAt m)
    (hbeta : kappaOne ≤ band.beta)
    (data : AllSixFilteredSourceCorrectBandProductData t m cutoff band
      eligible)
    (hstart : data.interfaces.lawStart ≤ m) (hm : 1 < m)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m data.externalLow
      data.externalHigh) :
    simpleRandomWalk
        ({s | candidateBudget48 m band.beta <
          (tilingRandomClockBandSites t m cutoff s band).card} ∩ eligible) ≤
      filteredSourceCorrectBandOverflowCoefficient data hstart (by omega) := by
  let occupancy := tilingBandOccupancy t m cutoff band
  let threshold := geometricShellThreshold (initialBudget48 m) shellGrowth48
  have hsource :=
    simpleRandomWalk_shellZeroSourceEvent_le_of_factoredCapDataAtCut
      t data.sourceOrientation m band.oldRank data.low data.externalLow data.externalHigh
      (sourceCut48 m) hm
      band.oldRank_pos
        harithmetic
        (fun n eta ↦
          (data.baseFibers n eta).toFactoredCapData hexternal)
  have hbaseENN : simpleRandomWalk
      (eligible ∩ shellOverflow occupancy threshold 0) ≤
        centralReplacementTailCost shellZeroLocalRatioConstant
          (sourceCut48 m) := by
    exact (measure_mono data.base_subset).trans hsource
  have hbase : simpleRandomWalk.real
      (eligible ∩ shellOverflow occupancy threshold 0) ≤
        (centralReplacementTailCost shellZeroLocalRatioConstant
          (sourceCut48 m)).toReal := by
    exact ENNReal.toReal_mono (centralReplacementTailCost_ne_top m) hbaseENN
  have hstep : ∀ j, j + 1 < shellCount48 m band.beta →
      shellGrowth48 * threshold j ≤ threshold (j + 1) := by
    intro j _
    exact (geometricShellThreshold_step (initialBudget48 m)
      shellGrowth48 j).le
  let screen := tilingBandInterfaceScreenOfProductData
    data.interfaces hstart (by omega)
  have htotal :=
    measureReal_inter_totalOverflow_le_of_geometricBalance_and_interfaceProduct
      simpleRandomWalk eligible screen.balanced occupancy threshold shellGrowth48
      (shellCount48 m band.beta) m hstep screen.balanceLaw
      screen.interfaceLaw hbase
  have hreal : simpleRandomWalk.real
      ({s | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m cutoff s band).card} ∩ eligible) ≤
      (centralReplacementTailCost shellZeroLocalRatioConstant
        (sourceCut48 m)).toReal +
        ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
          ((((screen.balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            screen.interfaceLaw.cost j) := by
    apply (measureReal_mono ?_).trans htotal
    rintro s ⟨hs, heligible⟩
    refine ⟨heligible, ?_⟩
    rw [tilingRandomClockBandOverflow_eq_dynamic] at hs
    exact dynamicStoppedCandidateOverflow48_subset_totalOverflow
      (tilingRandomClockVisitedSites t m cutoff band)
      (tilingRandomClockExternalLargeEvent t m cutoff band)
      (tilingRandomClockDistinguishedSites t m cutoff band)
      (tilingRandomClockTotalLocalTime m cutoff band) m band.beta
      (hbudget band.beta hbeta) hs
  rw [← ENNReal.ofReal_toReal (measure_ne_top simpleRandomWalk
    ({s | candidateBudget48 m band.beta <
      (tilingRandomClockBandSites t m cutoff s band).card} ∩ eligible))]
  exact ENNReal.ofReal_mono hreal

/-- Totalized coefficient for eventual finite-band statements. -/
noncomputable def totalFilteredSourceCorrectBandOverflowCoefficient
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    {eligible : Set WalkPath}
    (data : AllSixFilteredSourceCorrectBandProductData t m cutoff band
      eligible) : ℝ≥0∞ :=
  if htail : data.interfaces.lawStart ≤ m ∧ 1 < m then
    filteredSourceCorrectBandOverflowCoefficient data htail.1 (by omega)
  else 1

/-- Finite union of band overflows, with the source-eligible old histories
kept separately for each band. -/
def tilingFilteredRandomClockCandidateOverflow
    (t : DominoTiling) (m cutoff : ℕ) (bands : Finset RandomClockBand)
    (eligible : RandomClockBand → Set WalkPath) : Set WalkPath :=
  Screening.someCandidateBad bands fun band ↦
    {s | candidateBudget48 m band.beta <
      (tilingRandomClockBandSites t m cutoff s band).card} ∩ eligible band

/-- Eventual finite-band bound for the exact same filtered candidate family
that must be paid by the full-gap and upper-transition assemblies. -/
theorem eventually_simpleRandomWalk_tilingFilteredRandomClockCandidateOverflow_le_sum
    (t : DominoTiling)
    (cutoff : ℕ → ℕ) (bands : ℕ → Finset RandomClockBand)
    (eligible : ∀ m, RandomClockBand → Set WalkPath)
    (hbeta : ∀ m band, band ∈ bands m → kappaOne ≤ band.beta)
    (data : ∀ m band,
      AllSixFilteredSourceCorrectBandProductData t m (cutoff m) band
        (eligible m band))
    (hstart : ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ bands m, (data m band).interfaces.lawStart ≤ m)
    (hexternal : ∀ᶠ m : ℕ in atTop,
      ∀ band ∈ bands m,
        ShellZeroExternalWindowArithmeticAt m
          (data m band).externalLow (data m band).externalHigh) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (tilingFilteredRandomClockCandidateOverflow t m (cutoff m)
            (bands m) (eligible m)) ≤
        ∑ band ∈ bands m,
          totalFilteredSourceCorrectBandOverflowCoefficient (data m band) := by
  filter_upwards [eventually_candidateBudgetArithmeticAt,
      eventually_shellZeroWindowArithmeticAt, hstart, hexternal,
      eventually_ge_atTop (2 : ℕ)] with m hbudget harithmetic hstartM
        hexternalM hm
  refine (Screening.measure_someCandidateBad_le_sum simpleRandomWalk
    (bands m) (fun band ↦
      {s | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m (cutoff m) s band).card} ∩
          eligible m band)).trans ?_
  apply Finset.sum_le_sum
  intro band hband
  rw [totalFilteredSourceCorrectBandOverflowCoefficient,
    dif_pos ⟨hstartM band hband, hm⟩]
  exact
    simpleRandomWalk_tilingRandomClockBandOverflow_inter_le_of_filteredSourceCorrectData
      hbudget (hbeta m band hband) (data m band)
        (hstartM band hband) hm harithmetic (hexternalM band hband)

end

end Erdos1165.HLOZFilteredSourceCorrectBandProductClosure
