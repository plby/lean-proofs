/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZSourceCorrectFullGapClosure
import ErdosProblems.Erdos1165.HLOZSourceEndpointTransportTable
import ErdosProblems.Erdos1165.HLOZOrientedSourceCentralTail
import ErdosProblems.Erdos1165.HLOZShellZeroRankUnionCentralTail
import ErdosProblems.Erdos1165.HLOZThetaOneSourceShift
import ErdosProblems.Erdos1165.TilingShellZeroConcreteDeltaIndexedSourceBound

/-!
# Uniform source screens after the all-six spatial transports

The checker one-step recentering and the paired-column reflection preserve
simple random walk, but send a source event to a different tiling.  The
all-tiling product package stores the numerical source windows once and the
literal stopped-coordinate data for every target tiling.  This file applies
the four-class eighth-cut shell-zero screen after each transport and records
a uniform finite-band tail.

Only genuine source events are treated here.  The checker-origin obstruction
and the restricted-`Theta` complements remain separate named events; no raw
candidate or Harnack conclusion is asserted.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZAllTilingSourceTransportScreen

open HLOZFullBetaRegimeSplit HLOZGapBetaNumerics HLOZGapRandomClockScreen
open HLOZCandidateLocalLazyCap
open HLOZProposition48Candidates
open HLOZShellZeroExternalWindow
open HLOZOrientedSourceCentralTail
open HLOZShellZeroRankUnionCentralTail
open HLOZShellZeroCentralTail HLOZShellZeroReplacementWindows
open HLOZSharpPositiveShellNumerics HLOZSourceCorrectFilteredTransitions
open HLOZSourceCorrectFullGapClosure HLOZThetaOneSourceShift
open HLOZSourceEndpointTransportTable
open HLOZThetaSourceBalance
open HLOZTilingEndpointBandExtraction
open LazyDecomposition
open ScreeningInstantiation TilingShellZeroCutFactoredCapScreen
open TilingShellZeroFactoredCapScreen TilingShellZeroLiteralScreen
open TilingShellZeroSourcePartition
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroConcreteDeltaIndexedSourceBound

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A shell-zero source pulled back along one row of the finite endpoint
transport table.  The input `oDom` is the orientation of the normalized
dominant endpoint on the original path; the source atom itself uses the
table's target orientation. -/
def transportedBandSourceEvent
    (t : DominoTiling) (oDom : Orientation)
    (cls : DominantEndpointClass) (m : ℕ)
    (band : RandomClockBand) : Set WalkPath :=
  transportedEndpointSourceEvent orientedShellZeroSourceEvent t oDom cls m
    band.oldRank (shellWidth48 m) (m - shellWidth48 m)
    (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
    (orientedSourceCut48 m)

/-- The literal canonical shell-zero source attached to one endpoint band. -/
def canonicalBandSourceEvent
    (t : DominoTiling) (oDom : Orientation) (m : ℕ)
    (band : RandomClockBand) : Set WalkPath :=
  transportedBandSourceEvent t oDom .canonical m band

/-- The non-base checker source, pulled back by the genuine one-step
recentering. -/
def shiftedCheckerBandSourceEvent
    (d : Tilings.CheckerDirection) (oDom : Orientation) (m : ℕ)
    (band : RandomClockBand) : Set WalkPath :=
  transportedBandSourceEvent (.checker d) oDom .opposite m band

/-- The non-base column source, pulled back from the paired column tiling by
horizontal reflection. -/
def reflectedColumnBandSourceEvent
    (t : DominoTiling) (oDom : Orientation) (m : ℕ)
    (band : RandomClockBand) : Set WalkPath :=
  transportedBandSourceEvent t oDom .opposite m band

theorem measurableSet_transportedBandSourceEvent
    (t : DominoTiling) (oDom : Orientation)
    (cls : DominantEndpointClass) (m : ℕ) (band : RandomClockBand) :
    MeasurableSet (transportedBandSourceEvent t oDom cls m band) :=
  (measurableSet_orientedShellZeroSourceEvent
    (sourceTransportTargetTiling t cls)
    (sourceTransportTargetOrientation t oDom cls) m band.oldRank
    (shellWidth48 m) (m - shellWidth48 m) (shellZeroExternalLow48 m)
    (shellZeroExternalHigh48 m) (orientedSourceCut48 m)).preimage
      (measurable_sourceTransportPath t cls)

theorem measurableSet_canonicalBandSourceEvent
    (t : DominoTiling) (oDom : Orientation) (m : ℕ)
    (band : RandomClockBand) :
    MeasurableSet (canonicalBandSourceEvent t oDom m band) :=
  measurableSet_transportedBandSourceEvent t oDom .canonical m band

theorem measurableSet_shiftedCheckerBandSourceEvent
    (d : Tilings.CheckerDirection) (oDom : Orientation) (m : ℕ)
    (band : RandomClockBand) :
    MeasurableSet (shiftedCheckerBandSourceEvent d oDom m band) :=
  measurableSet_transportedBandSourceEvent (.checker d) oDom .opposite
    m band

theorem measurableSet_reflectedColumnBandSourceEvent
    (t : DominoTiling) (oDom : Orientation) (m : ℕ)
    (band : RandomClockBand) :
    MeasurableSet (reflectedColumnBandSourceEvent t oDom m band) :=
  measurableSet_transportedBandSourceEvent t oDom .opposite m band

/-- Every admissible table row is charged by the same actual-rank-union
oriented-source tail.  The delta-indexed stopped fibers are constructed at
the table's target tiling and orientation, while all scalar thresholds remain
definitionally unchanged. -/
theorem simpleRandomWalk_transportedBandSourceEvent_le
    (_data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (oDom : Orientation)
    (cls : DominantEndpointClass) (m : ℕ) (band : RandomClockBand)
    (hm : 1 < m) (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    simpleRandomWalk (transportedBandSourceEvent t oDom cls m band) ≤
      centralReplacementRankUnionTailCost shellZeroLocalRatioConstant
        (orientedSourceCut48 m) := by
  rw [transportedBandSourceEvent,
    simpleRandomWalk_transportedEndpointSourceEvent
      orientedShellZeroSourceEvent t oDom cls m band.oldRank
      (shellWidth48 m) (m - shellWidth48 m) (shellZeroExternalLow48 m)
      (shellZeroExternalHigh48 m) (orientedSourceCut48 m)
      (measurableSet_orientedShellZeroSourceEvent
        (sourceTransportTargetTiling t cls)
        (sourceTransportTargetOrientation t oDom cls) m band.oldRank
        (shellWidth48 m) (m - shellWidth48 m) (shellZeroExternalLow48 m)
        (shellZeroExternalHigh48 m) (orientedSourceCut48 m))]
  have hlow : m - shellWidth48 m < m :=
    Nat.sub_lt (by omega) (lt_of_lt_of_le (by norm_num) harithmetic.1)
  exact simpleRandomWalk_orientedShellZeroSourceEvent_le_rankUnionTail
    (sourceTransportTargetTiling t cls)
    (sourceTransportTargetOrientation t oDom cls) m band.oldRank
    (m - shellWidth48 m) (shellZeroExternalLow48 m)
    (shellZeroExternalHigh48 m) (orientedSourceCut48 m)
    band.oldRank_pos hlow
    harithmetic hexternal

/-- Every canonical band source is charged by the same oriented-source central
tail, directly from the literal stopped-coordinate data. -/
theorem simpleRandomWalk_canonicalBandSourceEvent_le
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (oDom : Orientation) (m : ℕ)
    (band : RandomClockBand)
    (hm : 1 < m) (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    simpleRandomWalk (canonicalBandSourceEvent t oDom m band) ≤
      centralReplacementRankUnionTailCost shellZeroLocalRatioConstant
        (orientedSourceCut48 m) := by
  simpa only [canonicalBandSourceEvent] using
    simpleRandomWalk_transportedBandSourceEvent_le data t oDom .canonical m
      band hm harithmetic hexternal

/-- The exact checker law transport introduces no multiplicative loss. -/
theorem simpleRandomWalk_shiftedCheckerBandSourceEvent_le
    (data : FullBetaSourceCorrectAllTilingProductData)
    (d : Tilings.CheckerDirection) (oDom : Orientation) (m : ℕ)
    (band : RandomClockBand)
    (hm : 1 < m) (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    simpleRandomWalk (shiftedCheckerBandSourceEvent d oDom m band) ≤
      centralReplacementRankUnionTailCost shellZeroLocalRatioConstant
        (orientedSourceCut48 m) := by
  simpa only [shiftedCheckerBandSourceEvent] using
    simpleRandomWalk_transportedBandSourceEvent_le data (.checker d) oDom
      .opposite m band hm harithmetic hexternal

/-- The exact column-reflection law transport also introduces no loss. -/
theorem simpleRandomWalk_reflectedColumnBandSourceEvent_le
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (oDom : Orientation) (m : ℕ)
    (band : RandomClockBand)
    (hm : 1 < m) (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    simpleRandomWalk (reflectedColumnBandSourceEvent t oDom m band) ≤
      centralReplacementRankUnionTailCost shellZeroLocalRatioConstant
        (orientedSourceCut48 m) := by
  simpa only [reflectedColumnBandSourceEvent] using
    simpleRandomWalk_transportedBandSourceEvent_le data t oDom .opposite m
      band hm harithmetic hexternal

/-- Finite union of canonical source events at one old-favorite rank. -/
def canonicalSourceUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (oDom : Orientation) (rank m : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (canonicalBandSourceEvent t oDom m)

/-- Finite union of shifted checker source events at one rank. -/
def shiftedCheckerSourceUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (d : Tilings.CheckerDirection) (oDom : Orientation)
    (rank m : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (shiftedCheckerBandSourceEvent d oDom m)

/-- Finite union of reflected column source events at one rank. -/
def reflectedColumnSourceUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (oDom : Orientation) (rank m : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (reflectedColumnBandSourceEvent t oDom m)

theorem canonicalBandSourceEvent_subset_unionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (oDom : Orientation) (rank m : ℕ)
    (band : RandomClockBand)
    (hband : band ∈ sourceProductEndpointBandsAtRank m
      (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank) :
    canonicalBandSourceEvent t oDom m band ⊆
      canonicalSourceUnionAtRank data t oDom rank m := by
  intro s hs
  exact ⟨band, hband, hs⟩

theorem shiftedCheckerBandSourceEvent_subset_unionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (d : Tilings.CheckerDirection) (oDom : Orientation) (rank m : ℕ)
    (band : RandomClockBand)
    (hband : band ∈ sourceProductEndpointBandsAtRank m
      (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank) :
    shiftedCheckerBandSourceEvent d oDom m band ⊆
      shiftedCheckerSourceUnionAtRank data d oDom rank m := by
  intro s hs
  exact ⟨band, hband, hs⟩

theorem reflectedColumnBandSourceEvent_subset_unionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (oDom : Orientation) (rank m : ℕ)
    (band : RandomClockBand)
    (hband : band ∈ sourceProductEndpointBandsAtRank m
      (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank) :
    reflectedColumnBandSourceEvent t oDom m band ⊆
      reflectedColumnSourceUnionAtRank data t oDom rank m := by
  intro s hs
  exact ⟨band, hband, hs⟩

private theorem measurableSet_someCandidateBad
    {Candidate : Type*}
    (candidates : Finset Candidate) (bad : Candidate → Set WalkPath)
    (hbad : ∀ x ∈ candidates, MeasurableSet (bad x)) :
    MeasurableSet (Screening.someCandidateBad candidates bad) := by
  classical
  induction candidates using Finset.induction_on with
  | empty => simp [Screening.someCandidateBad]
  | @insert x candidates hx ih =>
      rw [show Screening.someCandidateBad (insert x candidates) bad =
          bad x ∪ Screening.someCandidateBad candidates bad by
        ext s
        simp [Screening.someCandidateBad]]
      exact (hbad x (Finset.mem_insert_self x candidates)).union
        (ih fun y hy ↦ hbad y (Finset.mem_insert_of_mem hy))

theorem measurableSet_canonicalSourceUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (oDom : Orientation) (rank m : ℕ) :
    MeasurableSet (canonicalSourceUnionAtRank data t oDom rank m) :=
  measurableSet_someCandidateBad _ _ fun band _ ↦
    measurableSet_canonicalBandSourceEvent t oDom m band

theorem measurableSet_shiftedCheckerSourceUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (d : Tilings.CheckerDirection) (oDom : Orientation) (rank m : ℕ) :
    MeasurableSet (shiftedCheckerSourceUnionAtRank data d oDom rank m) :=
  measurableSet_someCandidateBad _ _ fun band _ ↦
    measurableSet_shiftedCheckerBandSourceEvent d oDom m band

theorem measurableSet_reflectedColumnSourceUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (oDom : Orientation) (rank m : ℕ) :
    MeasurableSet (reflectedColumnSourceUnionAtRank data t oDom rank m) :=
  measurableSet_someCandidateBad _ _ fun band _ ↦
    measurableSet_reflectedColumnBandSourceEvent t oDom m band

private theorem sourceProductEndpointBandsAtRank_card_le
    (m cap externalThreshold rank : ℕ) :
    (sourceProductEndpointBandsAtRank m cap externalThreshold rank).card ≤
      Nat.card CanonicalEndpointLowGapBandTag := by
  exact (Finset.card_filter_le _ _).trans
    (sourceProductEndpointBands_card_le m cap externalThreshold)

private theorem eventually_sourceUnion_le_exp
    (event : ℕ → Set WalkPath)
    (bands : ℕ → Finset RandomClockBand)
    (piece : ℕ → RandomClockBand → Set WalkPath)
    (hevent : ∀ m, event m = Screening.someCandidateBad (bands m) (piece m))
    (hcard : ∀ m, (bands m).card ≤ Nat.card CanonicalEndpointLowGapBandTag)
    (hpiece : ∀ m band, 1 < m → ShellZeroWindowArithmeticAt m →
      ShellZeroExternalWindowArithmeticAt m (shellZeroExternalLow48 m)
        (shellZeroExternalHigh48 m) →
      simpleRandomWalk (piece m band) ≤
        centralReplacementRankUnionTailCost shellZeroLocalRatioConstant
          (orientedSourceCut48 m)) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (event m) ≤
        ENNReal.ofReal (Real.exp
          (-(orientedRankUnionCentralTailRate shellZeroLocalRatioConstant / 2) *
            Real.log (m : ℝ) ^ 2)) := by
  have hbase :=
    eventually_centralReplacementRankUnionTailCost_orientedSourceCut48_le_exp
      shellZeroLocalRatioConstant_pos
  have hr : 0 < orientedRankUnionCentralTailRate
      shellZeroLocalRatioConstant / 2 := by
    positivity [orientedRankUnionCentralTailRate_pos
      shellZeroLocalRatioConstant_pos.le]
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
    (Nat.card CanonicalEndpointLowGapBandTag) hr
  have htail : ∀ᶠ m : ℕ in atTop,
      (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) *
          centralReplacementRankUnionTailCost shellZeroLocalRatioConstant
            (orientedSourceCut48 m) ≤
        ENNReal.ofReal (Real.exp
          (-(orientedRankUnionCentralTailRate shellZeroLocalRatioConstant / 2) *
            Real.log (m : ℝ) ^ 2)) := by
    filter_upwards [hbase, habsorb] with m hbaseM habsorbM
    calc
      (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) *
          centralReplacementRankUnionTailCost shellZeroLocalRatioConstant
            (orientedSourceCut48 m) ≤
        (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp
            (-orientedRankUnionCentralTailRate shellZeroLocalRatioConstant *
              Real.log (m : ℝ) ^ 2)) := by gcongr
      _ ≤ ENNReal.ofReal (Real.exp
          (-(orientedRankUnionCentralTailRate shellZeroLocalRatioConstant / 2) *
            Real.log (m : ℝ) ^ 2)) := by
        simpa only [show 2 *
          (orientedRankUnionCentralTailRate shellZeroLocalRatioConstant / 2) =
            orientedRankUnionCentralTailRate shellZeroLocalRatioConstant by ring]
          using habsorbM
  filter_upwards [htail, eventually_shellZeroWindowArithmeticAt,
      eventually_shellZeroExternalWindowArithmetic48,
      eventually_ge_atTop (2 : ℕ)] with
      m htailM harithmetic hexternal hm
  rw [hevent]
  calc
    simpleRandomWalk (Screening.someCandidateBad (bands m) (piece m)) ≤
        ((bands m).card : ℝ≥0∞) *
          centralReplacementRankUnionTailCost shellZeroLocalRatioConstant
            (orientedSourceCut48 m) :=
      Screening.measure_someCandidateBad_le_card_mul simpleRandomWalk
        (bands m) (piece m) _
          (fun band _ ↦ hpiece m band hm harithmetic hexternal)
    _ ≤ (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) *
          centralReplacementRankUnionTailCost shellZeroLocalRatioConstant
            (orientedSourceCut48 m) := by
      gcongr
      exact_mod_cast hcard m
    _ ≤ _ := htailM

theorem eventually_simpleRandomWalk_canonicalSourceUnionAtRank_le_exp
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (oDom : Orientation) (rank : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (canonicalSourceUnionAtRank data t oDom rank m) ≤
        ENNReal.ofReal (Real.exp
          (-(orientedRankUnionCentralTailRate shellZeroLocalRatioConstant / 2) *
            Real.log (m : ℝ) ^ 2)) :=
  eventually_sourceUnion_le_exp
    (canonicalSourceUnionAtRank data t oDom rank)
    (fun m ↦ sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (fun m ↦ canonicalBandSourceEvent t oDom m)
    (fun _ ↦ rfl)
    (fun m ↦ sourceProductEndpointBandsAtRank_card_le m
      (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (fun m band hm harithmetic hexternal ↦
      simpleRandomWalk_canonicalBandSourceEvent_le data t oDom m band hm
        harithmetic hexternal)

theorem eventually_simpleRandomWalk_shiftedCheckerSourceUnionAtRank_le_exp
    (data : FullBetaSourceCorrectAllTilingProductData)
    (d : Tilings.CheckerDirection) (oDom : Orientation) (rank : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (shiftedCheckerSourceUnionAtRank data d oDom rank m) ≤
        ENNReal.ofReal (Real.exp
          (-(orientedRankUnionCentralTailRate shellZeroLocalRatioConstant / 2) *
            Real.log (m : ℝ) ^ 2)) :=
  eventually_sourceUnion_le_exp
    (shiftedCheckerSourceUnionAtRank data d oDom rank)
    (fun m ↦ sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (fun m ↦ shiftedCheckerBandSourceEvent d oDom m)
    (fun _ ↦ rfl)
    (fun m ↦ sourceProductEndpointBandsAtRank_card_le m
      (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (fun m band hm harithmetic hexternal ↦
      simpleRandomWalk_shiftedCheckerBandSourceEvent_le data d oDom m band hm
        harithmetic hexternal)

theorem eventually_simpleRandomWalk_reflectedColumnSourceUnionAtRank_le_exp
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (oDom : Orientation) (rank : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk (reflectedColumnSourceUnionAtRank data t oDom rank m) ≤
        ENNReal.ofReal (Real.exp
          (-(orientedRankUnionCentralTailRate shellZeroLocalRatioConstant / 2) *
            Real.log (m : ℝ) ^ 2)) :=
  eventually_sourceUnion_le_exp
    (reflectedColumnSourceUnionAtRank data t oDom rank)
    (fun m ↦ sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (fun m ↦ reflectedColumnBandSourceEvent t oDom m)
    (fun _ ↦ rfl)
    (fun m ↦ sourceProductEndpointBandsAtRank_card_le m
      (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (fun m band hm harithmetic hexternal ↦
      simpleRandomWalk_reflectedColumnBandSourceEvent_le data t oDom m band hm
        harithmetic hexternal)

theorem simpleRandomWalk_canonicalSourceUnionAtRank_series_ne_top
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (oDom : Orientation) (rank : ℕ) :
    ∑' m, simpleRandomWalk
        (canonicalSourceUnionAtRank data t oDom rank m) ≠ ∞ :=
  HLOZUpperEstimates.measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    simpleRandomWalk (canonicalSourceUnionAtRank data t oDom rank)
    (div_pos (orientedRankUnionCentralTailRate_pos
      shellZeroLocalRatioConstant_pos.le) (by norm_num))
    (eventually_simpleRandomWalk_canonicalSourceUnionAtRank_le_exp
      data t oDom rank)

theorem simpleRandomWalk_shiftedCheckerSourceUnionAtRank_series_ne_top
    (data : FullBetaSourceCorrectAllTilingProductData)
    (d : Tilings.CheckerDirection) (oDom : Orientation) (rank : ℕ) :
    ∑' m, simpleRandomWalk
        (shiftedCheckerSourceUnionAtRank data d oDom rank m) ≠ ∞ :=
  HLOZUpperEstimates.measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    simpleRandomWalk (shiftedCheckerSourceUnionAtRank data d oDom rank)
    (div_pos (orientedRankUnionCentralTailRate_pos
      shellZeroLocalRatioConstant_pos.le) (by norm_num))
    (eventually_simpleRandomWalk_shiftedCheckerSourceUnionAtRank_le_exp
      data d oDom rank)

theorem simpleRandomWalk_reflectedColumnSourceUnionAtRank_series_ne_top
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (oDom : Orientation) (rank : ℕ) :
    ∑' m, simpleRandomWalk
        (reflectedColumnSourceUnionAtRank data t oDom rank m) ≠ ∞ :=
  HLOZUpperEstimates.measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    simpleRandomWalk (reflectedColumnSourceUnionAtRank data t oDom rank)
    (div_pos (orientedRankUnionCentralTailRate_pos
      shellZeroLocalRatioConstant_pos.le) (by norm_num))
    (eventually_simpleRandomWalk_reflectedColumnSourceUnionAtRank_le_exp
      data t oDom rank)

end

end Erdos1165.HLOZAllTilingSourceTransportScreen
