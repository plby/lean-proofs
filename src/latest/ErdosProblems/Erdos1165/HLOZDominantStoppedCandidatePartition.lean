/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZThetaOneSourceShift
import ErdosProblems.Erdos1165.HLOZTypedStoppedCandidateFamily

/-!
# The stopped dominant-source candidate partition

The raw Proposition 4.8 candidate set consists of endpoints, whereas the
source screen is applied after normalizing every endpoint to the endpoint of
its domino with larger stopped local time.  This file performs that
normalization before forming stopped-history atoms and then splits the result
into the two spatial sources used in the paper:

* `canonical`: the dominant endpoint is the designated base of the tiling;
* `thetaOneShiftedOpposite`: the other endpoint dominates and its source
  screen is pulled back through the genuine one-step recentering.

This is not the checkerboard-orientation split.  The exact cardinality loss is
kept visible: a raw overflow above `J` forces one of the two spatial sources
to have more than `J / 4` candidates.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZDominantStoppedCandidatePartition

open HLOZGapRandomClockScreen HLOZPathEvents HLOZThetaOneSourceShift
open HLOZProposition48Candidates
open HLOZThetaSourceBalance HLOZTilingGapRandomClockScreen
open HLOZTypedStoppedCandidateFamily TilingLazyDecomposition
open TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber TilingTypedFavoriteTrace
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The two genuine spatial sources.  The second constructor records that the
opposite endpoint is screened only after the paper's one-step shift. -/
inductive DominantSpatialSource where
  | canonical
  | thetaOneShiftedOpposite
  deriving DecidableEq, Countable

/-- The literal source carrier for all six tilings.  The carrier records not
only whether the dominant endpoint is the designated base, but also the
actual measure-preserving normalization used for a non-base endpoint:
one-step recentering for a checker tiling and horizontal reflection for a
column tiling.  Thus an opposite endpoint is never silently regarded as a
canonical endpoint on the original path. -/
inductive AllTilingDominantSource where
  | canonical (t : DominoTiling)
  | shiftedCheckerOpposite (d : Tilings.CheckerDirection)
  | reflectedEvenColumnsOpposite
  | reflectedOddColumnsOpposite
  deriving DecidableEq, Countable

/-- The tiling in which the stopped endpoint was observed. -/
def AllTilingDominantSource.originalTiling :
    AllTilingDominantSource → DominoTiling
  | .canonical t => t
  | .shiftedCheckerOpposite d => .checker d
  | .reflectedEvenColumnsOpposite => .evenColumns
  | .reflectedOddColumnsOpposite => .oddColumns

/-- The canonical source tiling after the genuine source normalization. -/
def AllTilingDominantSource.sourceTiling :
    AllTilingDominantSource → DominoTiling
  | .canonical t => t
  | .shiftedCheckerOpposite d => shiftedCheckerTiling d
  | .reflectedEvenColumnsOpposite => reflectedColumnTiling .evenColumns
  | .reflectedOddColumnsOpposite => reflectedColumnTiling .oddColumns

/-- The spatial half selected on the original stopped path. -/
def AllTilingDominantSource.spatialSource :
    AllTilingDominantSource → DominantSpatialSource
  | .canonical _ => .canonical
  | .shiftedCheckerOpposite _ => .thetaOneShiftedOpposite
  | .reflectedEvenColumnsOpposite => .thetaOneShiftedOpposite
  | .reflectedOddColumnsOpposite => .thetaOneShiftedOpposite

/-- The path normalization attached to a literal source carrier. -/
def AllTilingDominantSource.normalizePath
    (source : AllTilingDominantSource) : WalkPath → WalkPath :=
  match source with
  | .canonical _ => id
  | .shiftedCheckerOpposite _ => oneStepRecenter
  | .reflectedEvenColumnsOpposite => horizontalReflectPath
  | .reflectedOddColumnsOpposite => horizontalReflectPath

/-- The corresponding normalization of an endpoint.  In the checker case
the translation depends on the first increment of the realized path. -/
def AllTilingDominantSource.normalizePoint
    (source : AllTilingDominantSource) (s : WalkPath) : Point → Point :=
  match source with
  | .canonical _ => id
  | .shiftedCheckerOpposite _ => fun x => x - s 1
  | .reflectedEvenColumnsOpposite => horizontalReflectPoint
  | .reflectedOddColumnsOpposite => horizontalReflectPoint

/-- The exact source event attached to a literal carrier.  The non-base
cases are definitionally the named pullback events from
`HLOZThetaOneSourceShift`. -/
def allTilingDominantSourceEvent (source : AllTilingDominantSource)
    (m k w low externalLow externalHigh cut : ℕ) : Set WalkPath :=
  match source with
  | .canonical t =>
      shellZeroSourceEvent t m k w low externalLow externalHigh cut
  | .shiftedCheckerOpposite d =>
      shiftedCheckerSourceEvent d m k w low externalLow externalHigh cut
  | .reflectedEvenColumnsOpposite =>
      reflectedColumnSourceEvent .evenColumns m k w low externalLow
        externalHigh cut
  | .reflectedOddColumnsOpposite =>
      reflectedColumnSourceEvent .oddColumns m k w low externalLow
        externalHigh cut

theorem measurableSet_allTilingDominantSourceEvent
    (source : AllTilingDominantSource)
    (m k w low externalLow externalHigh cut : ℕ) :
    MeasurableSet (allTilingDominantSourceEvent source m k w low
      externalLow externalHigh cut) := by
  cases source with
  | canonical t =>
      exact measurableSet_shellZeroSourceEvent t m k w low externalLow
        externalHigh cut
  | shiftedCheckerOpposite d =>
      exact measurableSet_shiftedCheckerSourceEvent d m k w low externalLow
        externalHigh cut
  | reflectedEvenColumnsOpposite =>
      exact measurableSet_reflectedColumnSourceEvent .evenColumns m k w low
        externalLow externalHigh cut
  | reflectedOddColumnsOpposite =>
      exact measurableSet_reflectedColumnSourceEvent .oddColumns m k w low
        externalLow externalHigh cut

/-- Canonical-base dominant endpoints at the stopped old clock. -/
noncomputable def tilingCanonicalDominantRandomClockBandSites
    (t : DominoTiling) (m cutoff : ℕ) (s : WalkPath)
    (band : RandomClockBand) : Finset Point :=
  (tilingDominantRandomClockBandSites t m cutoff s band).filter
    (IsTilingBase t)

/-- Opposite dominant endpoints at the stopped old clock.  These are not
same-path `V₂` bases. -/
noncomputable def tilingOppositeDominantRandomClockBandSites
    (t : DominoTiling) (m cutoff : ℕ) (s : WalkPath)
    (band : RandomClockBand) : Finset Point :=
  (tilingDominantRandomClockBandSites t m cutoff s band).filter
    (fun x ↦ ¬IsTilingBase t x)

/-- Candidate set selected by one spatial source. -/
noncomputable def tilingDominantSourceRandomClockBandSites
    (source : DominantSpatialSource) (t : DominoTiling)
    (m cutoff : ℕ) (s : WalkPath) (band : RandomClockBand) : Finset Point :=
  match source with
  | .canonical => tilingCanonicalDominantRandomClockBandSites t m cutoff s band
  | .thetaOneShiftedOpposite =>
      tilingOppositeDominantRandomClockBandSites t m cutoff s band

/-- The stopped candidate set belonging to a literal all-tiling carrier.
This is always a normalized dominant set; it is never the raw band set. -/
noncomputable def tilingAllTilingDominantSourceRandomClockBandSites
    (source : AllTilingDominantSource) (m cutoff : ℕ) (s : WalkPath)
    (band : RandomClockBand) : Finset Point :=
  tilingDominantSourceRandomClockBandSites source.spatialSource
    source.originalTiling m cutoff s band

theorem tilingDominantRandomClockBandSites_eq_canonical_union_opposite
    (t : DominoTiling) (m cutoff : ℕ) (s : WalkPath)
    (band : RandomClockBand) :
    tilingDominantRandomClockBandSites t m cutoff s band =
      tilingCanonicalDominantRandomClockBandSites t m cutoff s band ∪
        tilingOppositeDominantRandomClockBandSites t m cutoff s band := by
  classical
  ext x
  simp only [tilingCanonicalDominantRandomClockBandSites,
    tilingOppositeDominantRandomClockBandSites, Finset.mem_union,
    Finset.mem_filter]
  by_cases hx : IsTilingBase t x <;> simp [hx]

/-- Literal stopped-clock version of `#M ≤ 2 (#Mₑ + #Mₒ)`. -/
theorem tilingRandomClockBandSites_card_le_two_spatialSources
    (t : DominoTiling) (m cutoff : ℕ) (s : WalkPath)
    (band : RandomClockBand) :
    (tilingRandomClockBandSites t m cutoff s band).card ≤
      2 * ((tilingCanonicalDominantRandomClockBandSites
          t m cutoff s band).card +
        (tilingOppositeDominantRandomClockBandSites
          t m cutoff s band).card) := by
  have hnormalize := card_le_two_mul_card_image_tilingDominantEndpointAt
    t s (pathTruncatedLevelTime m band.oldRank cutoff s)
      (tilingRandomClockBandSites t m cutoff s band)
  have hunion : (tilingDominantRandomClockBandSites
      t m cutoff s band).card ≤
      (tilingCanonicalDominantRandomClockBandSites
          t m cutoff s band).card +
        (tilingOppositeDominantRandomClockBandSites
          t m cutoff s band).card := by
    rw [tilingDominantRandomClockBandSites_eq_canonical_union_opposite]
    exact Finset.card_union_le _ _
  exact hnormalize.trans (Nat.mul_le_mul_left 2 hunion)

/-- Exact integer pigeonhole after dominant-endpoint normalization.  The
quarter cut is intentional and is not replaced by the raw cut. -/
theorem quarter_cut_lt_canonical_or_opposite_of_lt_randomClockBand
    (t : DominoTiling) (m cutoff J : ℕ) (s : WalkPath)
    (band : RandomClockBand)
    (hJ : J < (tilingRandomClockBandSites t m cutoff s band).card) :
    J / 4 < (tilingCanonicalDominantRandomClockBandSites
        t m cutoff s band).card ∨
      J / 4 < (tilingOppositeDominantRandomClockBandSites
        t m cutoff s band).card := by
  have hbound := tilingRandomClockBandSites_card_le_two_spatialSources
    t m cutoff s band
  by_contra h
  simp only [not_or, not_lt] at h
  have hfour : 4 * (J / 4) ≤ J := Nat.mul_div_le J 4
  omega

/-- The source-side Proposition 4.9 budget after dominant normalization and
the exact factor-four pigeonhole loss. -/
def dominantSourceCandidateBudget48 (m : ℕ) (beta : ℝ) : ℕ :=
  candidateBudget48 m beta / 4

theorem dominantSourceCandidateBudget48_lt_canonical_or_opposite
    (t : DominoTiling) (m cutoff : ℕ) (s : WalkPath)
    (band : RandomClockBand)
    (hoverflow : candidateBudget48 m band.beta <
      (tilingRandomClockBandSites t m cutoff s band).card) :
    dominantSourceCandidateBudget48 m band.beta <
        (tilingCanonicalDominantRandomClockBandSites
          t m cutoff s band).card ∨
      dominantSourceCandidateBudget48 m band.beta <
        (tilingOppositeDominantRandomClockBandSites
          t m cutoff s band).card := by
  exact quarter_cut_lt_canonical_or_opposite_of_lt_randomClockBand
    t m cutoff (candidateBudget48 m band.beta) s band hoverflow

/-! ## Finite-prefix observability -/

/-- Dominant normalization of a raw band set, evaluated on a finite prefix. -/
noncomputable def tilingPrefixDominantBandSites
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) {n : ℕ}
    (u : Fin (n + 1) → Point) : Finset Point := by
  classical
  exact (tilingPrefixBandSites t band.orientation band.vertexPhase
      band.externalThreshold m band.beta u).image fun y ↦
    if localTimePrefix u (tilingPartner t y) ≤ localTimePrefix u y then y
    else tilingPartner t y

/-- Prefix form of one spatial source. -/
noncomputable def tilingPrefixDominantSourceBandSites
    (source : DominantSpatialSource) (t : DominoTiling)
    (m : ℕ) (band : RandomClockBand) {n : ℕ}
    (u : Fin (n + 1) → Point) : Finset Point :=
  match source with
  | .canonical =>
      (tilingPrefixDominantBandSites t m band u).filter (IsTilingBase t)
  | .thetaOneShiftedOpposite =>
      (tilingPrefixDominantBandSites t m band u).filter
        (fun x ↦ ¬IsTilingBase t x)

theorem tilingDominantRandomClockBandSites_eq_prefix_of_clock
    {t : DominoTiling} {m cutoff n : ℕ} {s : WalkPath}
    {band : RandomClockBand}
    (hn : pathTruncatedLevelTime m band.oldRank cutoff s = n) :
    tilingDominantRandomClockBandSites t m cutoff s band =
      tilingPrefixDominantBandSites t m band (pathPrefix s n) := by
  classical
  unfold tilingDominantRandomClockBandSites tilingPrefixDominantBandSites
  rw [tilingRandomClockBandSites_eq_prefix_of_clock hn, hn]
  rfl

theorem tilingDominantSourceRandomClockBandSites_eq_prefix_of_clock
    {source : DominantSpatialSource} {t : DominoTiling}
    {m cutoff n : ℕ} {s : WalkPath} {band : RandomClockBand}
    (hn : pathTruncatedLevelTime m band.oldRank cutoff s = n) :
    tilingDominantSourceRandomClockBandSites source t m cutoff s band =
      tilingPrefixDominantSourceBandSites source t m band (pathPrefix s n) := by
  classical
  cases source <;>
    simp only [tilingDominantSourceRandomClockBandSites,
      tilingCanonicalDominantRandomClockBandSites,
      tilingOppositeDominantRandomClockBandSites,
      tilingPrefixDominantSourceBandSites,
      tilingDominantRandomClockBandSites_eq_prefix_of_clock hn]

theorem measurable_fixed_tilingPrefixDominantSourceBandSites
    (source : DominantSpatialSource) (t : DominoTiling)
    (n m : ℕ) (band : RandomClockBand) :
    Measurable fun s : WalkPath ↦
      tilingPrefixDominantSourceBandSites source t m band (pathPrefix s n) := by
  exact (measurable_of_countable
    (tilingPrefixDominantSourceBandSites source t m band)).comp
      (measurable_pathPrefix n)

/-- Equality with a concrete spatial-source candidate Finset is observable at
the stopped old clock. -/
theorem measurableSet_tilingDominantSourceRandomClockBandSites_eq
    (source : DominantSpatialSource) (t : DominoTiling)
    (m cutoff : ℕ) (band : RandomClockBand) (S : Finset Point) :
    MeasurableSet {s : WalkPath |
      tilingDominantSourceRandomClockBandSites source t m cutoff s band = S} := by
  have heq :
      {s : WalkPath |
          tilingDominantSourceRandomClockBandSites
            source t m cutoff s band = S} =
        ⋃ n : ℕ,
          {s | pathTruncatedLevelTime m band.oldRank cutoff s = n} ∩
            {s | tilingPrefixDominantSourceBandSites source t m band
              (pathPrefix s n) = S} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hs
      refine ⟨pathTruncatedLevelTime m band.oldRank cutoff s, rfl, ?_⟩
      simpa only [tilingDominantSourceRandomClockBandSites_eq_prefix_of_clock
        rfl] using hs
    · rintro ⟨n, hn, hs⟩
      simpa only [tilingDominantSourceRandomClockBandSites_eq_prefix_of_clock
        hn] using hs
  rw [heq]
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_pathTruncatedLevelTime_eq
      m band.oldRank cutoff n).inter
      (measurableSet_eq_fun
        (measurable_fixed_tilingPrefixDominantSourceBandSites
          source t n m band) measurable_const)

/-- Prefix description for a literal all-tiling source carrier. -/
theorem tilingAllTilingDominantSourceRandomClockBandSites_eq_prefix_of_clock
    {source : AllTilingDominantSource} {m cutoff n : ℕ} {s : WalkPath}
    {band : RandomClockBand}
    (hn : pathTruncatedLevelTime m band.oldRank cutoff s = n) :
    tilingAllTilingDominantSourceRandomClockBandSites
        source m cutoff s band =
      tilingPrefixDominantSourceBandSites source.spatialSource
        source.originalTiling m band (pathPrefix s n) := by
  exact tilingDominantSourceRandomClockBandSites_eq_prefix_of_clock hn

/-- Exact candidate-Finset observability for every literal source carrier. -/
theorem measurableSet_tilingAllTilingDominantSourceRandomClockBandSites_eq
    (source : AllTilingDominantSource) (m cutoff : ℕ)
    (band : RandomClockBand) (S : Finset Point) :
    MeasurableSet {s : WalkPath |
      tilingAllTilingDominantSourceRandomClockBandSites
        source m cutoff s band = S} := by
  exact measurableSet_tilingDominantSourceRandomClockBandSites_eq
    source.spatialSource source.originalTiling m cutoff band S

/-! ## Exact stopped histories -/

/-- A dominant-source stopped history fixes the retained typed trace and the
exact normalized candidate Finset.  `none` is the explicit invalid/outside
atom. -/
abbrev DominantStoppedCandidateHistory (t : DominoTiling) (_budget : ℕ) :=
  Option (TypedFavoriteTilingTraceCode t × Finset Point)

def dominantStoppedCandidatePiece
    (source : DominantSpatialSource) (t : DominoTiling)
    (m k cutoff budget : ℕ) (stage previous : Set WalkPath)
    (band : RandomClockBand) :
    DominantStoppedCandidateHistory t budget → Set WalkPath
  | none => previous \ (stage ∩ validStepWalk)
  | some (z, S) =>
      (previous ∩ typedFavoriteTilingStagePiece t m k stage z) ∩
        {s | tilingDominantSourceRandomClockBandSites
          source t m cutoff s band = S}

def dominantStoppedCandidates
    {t : DominoTiling} {budget : ℕ} :
    DominantStoppedCandidateHistory t budget → Finset Point
  | none => ∅
  | some (_, S) => if S.card ≤ budget then S else ∅

@[simp] theorem dominantStoppedCandidates_none
    {t : DominoTiling} {budget : ℕ} :
    dominantStoppedCandidates (t := t) (budget := budget) none = ∅ := rfl

@[simp] theorem dominantStoppedCandidates_some_of_card_le
    {t : DominoTiling} {budget : ℕ}
    (z : TypedFavoriteTilingTraceCode t) (S : Finset Point)
    (hS : S.card ≤ budget) :
    dominantStoppedCandidates (t := t) (budget := budget) (some (z, S)) = S := by
  simp [dominantStoppedCandidates, hS]

theorem dominantStoppedCandidates_card_le
    {t : DominoTiling} {budget : ℕ}
    (h : DominantStoppedCandidateHistory t budget) :
    (dominantStoppedCandidates h).card ≤ budget := by
  cases h with
  | none => simp [dominantStoppedCandidates]
  | some h =>
      by_cases hcard : h.2.card ≤ budget
      · rw [dominantStoppedCandidates, if_pos hcard]
        exact hcard
      · simp [dominantStoppedCandidates, hcard]

theorem measurableSet_dominantStoppedCandidatePiece
    (source : DominantSpatialSource) (t : DominoTiling)
    (m k cutoff budget : ℕ) {stage previous : Set WalkPath}
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (band : RandomClockBand)
    (h : DominantStoppedCandidateHistory t budget) :
    MeasurableSet (dominantStoppedCandidatePiece source t m k cutoff budget
      stage previous band h) := by
  cases h with
  | none =>
      exact hpreviousMeasurable.diff
        (hstageMeasurable.inter measurableSet_validStepWalk)
  | some h =>
      exact (hpreviousMeasurable.inter
        (measurableSet_typedFavoriteTilingStagePiece
          t m k hstageMeasurable h.1)).inter
        (measurableSet_tilingDominantSourceRandomClockBandSites_eq
          source t m cutoff band h.2)

theorem pairwise_disjoint_dominantStoppedCandidatePiece
    (source : DominantSpatialSource) (t : DominoTiling)
    (m k cutoff budget : ℕ) {stage : Set WalkPath}
    (hstage : stage ⊆ thresholdReachStage m k)
    (previous : Set WalkPath) (band : RandomClockBand) :
    Pairwise fun h h' : DominantStoppedCandidateHistory t budget ↦
      Disjoint
        (dominantStoppedCandidatePiece source t m k cutoff budget
          stage previous band h)
        (dominantStoppedCandidatePiece source t m k cutoff budget
          stage previous band h') := by
  classical
  intro h h' hne
  cases h with
  | none =>
      rcases h' with _ | ⟨z, S⟩
      · exact (hne rfl).elim
      · refine Set.disjoint_left.2 fun s hs hs' ↦ ?_
        exact hs.2
          (typedFavoriteTilingStagePiece_subset_stage_inter_validStepWalk
            t m k hstage z hs'.1.2)
  | some h =>
      rcases h with ⟨z, S⟩
      rcases h' with _ | ⟨w, T⟩
      · refine Set.disjoint_left.2 fun s hs hs' ↦ ?_
        exact hs'.2
          (typedFavoriteTilingStagePiece_subset_stage_inter_validStepWalk
            t m k hstage z hs.1.2)
      · by_cases hzw : z = w
        · subst w
          have hST : S ≠ T := by
            intro hEq
            apply hne
            simp [hEq]
          refine Set.disjoint_left.2 fun s hs hs' ↦ ?_
          exact hST (hs.2.symm.trans hs'.2)
        · exact (disjoint_typedFavoriteTilingStagePiece_of_ne
            t m k stage hzw).mono
              (fun _ hs ↦ hs.1.2) (fun _ hs ↦ hs.1.2)

/-- Exact partition of `previous`, including invalid support and overflowing
candidate atoms. -/
theorem iUnion_dominantStoppedCandidatePiece
    (source : DominantSpatialSource) (t : DominoTiling)
    (m k cutoff budget : ℕ) {stage previous : Set WalkPath}
    (hstage : stage ⊆ thresholdReachStage m k)
    (band : RandomClockBand) :
    (⋃ h : DominantStoppedCandidateHistory t budget,
      dominantStoppedCandidatePiece source t m k cutoff budget
        stage previous band h) = previous := by
  classical
  ext s
  constructor
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨h, hh⟩
    cases h with
    | none => exact hh.1
    | some h => exact hh.1.1
  · intro hs
    by_cases hcanonical : s ∈ stage ∩ validStepWalk
    · have hu : s ∈ ⋃ z : TypedFavoriteTilingTraceCode t,
          typedFavoriteTilingStagePiece t m k stage z := by
        rw [iUnion_typedFavoriteTilingStagePiece t m k hstage]
        exact hcanonical
      rcases Set.mem_iUnion.mp hu with ⟨z, hz⟩
      let S := tilingDominantSourceRandomClockBandSites
        source t m cutoff s band
      exact Set.mem_iUnion.mpr ⟨some (z, S), ⟨⟨hs, hz⟩, rfl⟩⟩
    · exact Set.mem_iUnion.mpr ⟨none, ⟨hs, hcanonical⟩⟩

/-- A raw no-overflow witness controls either normalized spatial source. -/
theorem dominantSourceRandomClockBandSites_card_le_of_raw
    (source : DominantSpatialSource) (t : DominoTiling)
    (m cutoff budget : ℕ) (s : WalkPath) (band : RandomClockBand)
    (hraw : (tilingRandomClockBandSites t m cutoff s band).card ≤ budget) :
    (tilingDominantSourceRandomClockBandSites
      source t m cutoff s band).card ≤ budget := by
  have hsub : tilingDominantSourceRandomClockBandSites
      source t m cutoff s band ⊆
      tilingDominantRandomClockBandSites t m cutoff s band := by
    cases source <;> exact Finset.filter_subset _ _
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans hraw)

/-! ## Literal all-tiling history adapters -/

/-- A stopped history for a literal carrier uses the typed trace of the
original tiling and fixes its exact normalized dominant candidate set. -/
abbrev AllTilingDominantStoppedCandidateHistory
    (source : AllTilingDominantSource) (_budget : ℕ) :=
  DominantStoppedCandidateHistory source.originalTiling _budget

def allTilingDominantStoppedCandidatePiece
    (source : AllTilingDominantSource)
    (m k cutoff budget : ℕ) (stage previous : Set WalkPath)
    (band : RandomClockBand) :
    AllTilingDominantStoppedCandidateHistory source budget → Set WalkPath :=
  dominantStoppedCandidatePiece source.spatialSource source.originalTiling
    m k cutoff budget stage previous band

theorem measurableSet_allTilingDominantStoppedCandidatePiece
    (source : AllTilingDominantSource)
    (m k cutoff budget : ℕ) {stage previous : Set WalkPath}
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (band : RandomClockBand)
    (h : AllTilingDominantStoppedCandidateHistory source budget) :
    MeasurableSet (allTilingDominantStoppedCandidatePiece source m k cutoff
      budget stage previous band h) := by
  exact measurableSet_dominantStoppedCandidatePiece source.spatialSource
    source.originalTiling m k cutoff budget hstageMeasurable
    hpreviousMeasurable band h

theorem pairwise_disjoint_allTilingDominantStoppedCandidatePiece
    (source : AllTilingDominantSource)
    (m k cutoff budget : ℕ) {stage : Set WalkPath}
    (hstage : stage ⊆ thresholdReachStage m k)
    (previous : Set WalkPath) (band : RandomClockBand) :
    Pairwise fun h h' : AllTilingDominantStoppedCandidateHistory source budget ↦
      Disjoint
        (allTilingDominantStoppedCandidatePiece source m k cutoff budget
          stage previous band h)
        (allTilingDominantStoppedCandidatePiece source m k cutoff budget
          stage previous band h') := by
  exact pairwise_disjoint_dominantStoppedCandidatePiece source.spatialSource
    source.originalTiling m k cutoff budget hstage previous band

theorem iUnion_allTilingDominantStoppedCandidatePiece
    (source : AllTilingDominantSource)
    (m k cutoff budget : ℕ) {stage previous : Set WalkPath}
    (hstage : stage ⊆ thresholdReachStage m k)
    (band : RandomClockBand) :
    (⋃ h : AllTilingDominantStoppedCandidateHistory source budget,
      allTilingDominantStoppedCandidatePiece source m k cutoff budget
        stage previous band h) = previous := by
  exact iUnion_dominantStoppedCandidatePiece source.spatialSource
    source.originalTiling m k cutoff budget hstage band

theorem allTilingDominantSourceRandomClockBandSites_card_le_of_raw
    (source : AllTilingDominantSource)
    (m cutoff budget : ℕ) (s : WalkPath) (band : RandomClockBand)
    (hraw : (tilingRandomClockBandSites source.originalTiling
      m cutoff s band).card ≤ budget) :
    (tilingAllTilingDominantSourceRandomClockBandSites
      source m cutoff s band).card ≤ budget := by
  exact dominantSourceRandomClockBandSites_card_le_of_raw source.spatialSource
    source.originalTiling m cutoff budget s band hraw

/-! ## The joint canonical/opposite stopped-history partition -/

/-- Literal canonical carrier for a selected tiling. -/
def canonicalDominantSource (t : DominoTiling) : AllTilingDominantSource :=
  .canonical t

/-- Literal non-base carrier for a selected tiling.  Its cases are exactly
the checker shift and the two column reflections exported upstream. -/
def oppositeDominantSource : DominoTiling → AllTilingDominantSource
  | .checker d => .shiftedCheckerOpposite d
  | .evenColumns => .reflectedEvenColumnsOpposite
  | .oddColumns => .reflectedOddColumnsOpposite

@[simp] theorem canonicalDominantSource_originalTiling
    (t : DominoTiling) :
    (canonicalDominantSource t).originalTiling = t := rfl

@[simp] theorem oppositeDominantSource_originalTiling
    (t : DominoTiling) :
    (oppositeDominantSource t).originalTiling = t := by
  cases t <;> rfl

/-- A joint atom fixes one retained typed trace and both exact normalized
candidate Finsets.  This avoids duplicating the stopped past when the whole
low transition is the union of the canonical and transported sources. -/
abbrev JointDominantStoppedCandidateHistory
    (t : DominoTiling) (_canonicalBudget _oppositeBudget : ℕ) :=
  Option (TypedFavoriteTilingTraceCode t × Finset Point × Finset Point)

/-- A candidate tagged by the source normalization under which it will be
screened. -/
abbrev TaggedDominantCandidate := DominantSpatialSource × Point

def jointDominantStoppedCandidatePiece
    (t : DominoTiling) (m k cutoff canonicalBudget oppositeBudget : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand) :
    JointDominantStoppedCandidateHistory
      t canonicalBudget oppositeBudget → Set WalkPath
  | none => previous \ (stage ∩ validStepWalk)
  | some (z, canonicalSites, oppositeSites) =>
      (((previous ∩ typedFavoriteTilingStagePiece t m k stage z) ∩
        {s | tilingAllTilingDominantSourceRandomClockBandSites
          (canonicalDominantSource t) m cutoff s band = canonicalSites}) ∩
        {s | tilingAllTilingDominantSourceRandomClockBandSites
          (oppositeDominantSource t) m cutoff s band = oppositeSites})

noncomputable def jointDominantStoppedCandidates
    {t : DominoTiling} {canonicalBudget oppositeBudget : ℕ} :
    JointDominantStoppedCandidateHistory
      t canonicalBudget oppositeBudget → Finset TaggedDominantCandidate
  | none => ∅
  | some (_, canonicalSites, oppositeSites) =>
      if canonicalSites.card ≤ canonicalBudget ∧
          oppositeSites.card ≤ oppositeBudget then
        canonicalSites.image (fun x => (.canonical, x)) ∪
          oppositeSites.image (fun x => (.thetaOneShiftedOpposite, x))
      else ∅

theorem jointDominantStoppedCandidates_card_le
    {t : DominoTiling} {canonicalBudget oppositeBudget : ℕ}
    (h : JointDominantStoppedCandidateHistory
      t canonicalBudget oppositeBudget) :
    (jointDominantStoppedCandidates h).card ≤
      canonicalBudget + oppositeBudget := by
  classical
  cases h with
  | none => simp [jointDominantStoppedCandidates]
  | some h =>
      rcases h with ⟨z, canonicalSites, oppositeSites⟩
      by_cases hcard : canonicalSites.card ≤ canonicalBudget ∧
          oppositeSites.card ≤ oppositeBudget
      · rw [jointDominantStoppedCandidates, if_pos hcard]
        exact (Finset.card_union_le _ _).trans <|
          add_le_add
            ((Finset.card_image_le.trans hcard.1))
            ((Finset.card_image_le.trans hcard.2))
      · simp [jointDominantStoppedCandidates, hcard]

theorem measurableSet_jointDominantStoppedCandidatePiece
    (t : DominoTiling) (m k cutoff canonicalBudget oppositeBudget : ℕ)
    {stage previous : Set WalkPath}
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (band : RandomClockBand)
    (h : JointDominantStoppedCandidateHistory
      t canonicalBudget oppositeBudget) :
    MeasurableSet (jointDominantStoppedCandidatePiece t m k cutoff
      canonicalBudget oppositeBudget stage previous band h) := by
  cases h with
  | none =>
      exact hpreviousMeasurable.diff
        (hstageMeasurable.inter measurableSet_validStepWalk)
  | some h =>
      exact ((hpreviousMeasurable.inter
        (measurableSet_typedFavoriteTilingStagePiece
          t m k hstageMeasurable h.1)).inter
        (measurableSet_tilingAllTilingDominantSourceRandomClockBandSites_eq
          (canonicalDominantSource t) m cutoff band h.2.1)).inter
        (measurableSet_tilingAllTilingDominantSourceRandomClockBandSites_eq
          (oppositeDominantSource t) m cutoff band h.2.2)

theorem pairwise_disjoint_jointDominantStoppedCandidatePiece
    (t : DominoTiling) (m k cutoff canonicalBudget oppositeBudget : ℕ)
    {stage : Set WalkPath} (hstage : stage ⊆ thresholdReachStage m k)
    (previous : Set WalkPath) (band : RandomClockBand) :
    Pairwise fun h h' : JointDominantStoppedCandidateHistory
        t canonicalBudget oppositeBudget ↦
      Disjoint
        (jointDominantStoppedCandidatePiece t m k cutoff canonicalBudget
          oppositeBudget stage previous band h)
        (jointDominantStoppedCandidatePiece t m k cutoff canonicalBudget
          oppositeBudget stage previous band h') := by
  classical
  intro h h' hne
  cases h with
  | none =>
      rcases h' with _ | ⟨z, canonicalSites, oppositeSites⟩
      · exact (hne rfl).elim
      · refine Set.disjoint_left.2 fun s hs hs' ↦ ?_
        exact hs.2
          (typedFavoriteTilingStagePiece_subset_stage_inter_validStepWalk
            t m k hstage z hs'.1.1.2)
  | some h =>
      rcases h with ⟨z, canonicalSites, oppositeSites⟩
      rcases h' with _ | ⟨w, canonicalSites', oppositeSites'⟩
      · refine Set.disjoint_left.2 fun s hs hs' ↦ ?_
        exact hs'.2
          (typedFavoriteTilingStagePiece_subset_stage_inter_validStepWalk
            t m k hstage z hs.1.1.2)
      · by_cases hzw : z = w
        · subst w
          by_cases hcanonical : canonicalSites = canonicalSites'
          · subst canonicalSites'
            have hopposite : oppositeSites ≠ oppositeSites' := by
              intro heq
              apply hne
              simp [heq]
            refine Set.disjoint_left.2 fun s hs hs' ↦ ?_
            exact hopposite (hs.2.symm.trans hs'.2)
          · refine Set.disjoint_left.2 fun s hs hs' ↦ ?_
            exact hcanonical (hs.1.2.symm.trans hs'.1.2)
        · exact (disjoint_typedFavoriteTilingStagePiece_of_ne
            t m k stage hzw).mono
              (fun _ hs ↦ hs.1.1.2) (fun _ hs ↦ hs.1.1.2)

theorem iUnion_jointDominantStoppedCandidatePiece
    (t : DominoTiling) (m k cutoff canonicalBudget oppositeBudget : ℕ)
    {stage previous : Set WalkPath}
    (hstage : stage ⊆ thresholdReachStage m k)
    (band : RandomClockBand) :
    (⋃ h : JointDominantStoppedCandidateHistory
        t canonicalBudget oppositeBudget,
      jointDominantStoppedCandidatePiece t m k cutoff canonicalBudget
        oppositeBudget stage previous band h) = previous := by
  classical
  ext s
  constructor
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨h, hh⟩
    cases h with
    | none => exact hh.1
    | some h => exact hh.1.1.1
  · intro hs
    by_cases hvalid : s ∈ stage ∩ validStepWalk
    · have hu : s ∈ ⋃ z : TypedFavoriteTilingTraceCode t,
          typedFavoriteTilingStagePiece t m k stage z := by
        rw [iUnion_typedFavoriteTilingStagePiece t m k hstage]
        exact hvalid
      rcases Set.mem_iUnion.mp hu with ⟨z, hz⟩
      let canonicalSites :=
        tilingAllTilingDominantSourceRandomClockBandSites
          (canonicalDominantSource t) m cutoff s band
      let oppositeSites :=
        tilingAllTilingDominantSourceRandomClockBandSites
          (oppositeDominantSource t) m cutoff s band
      exact Set.mem_iUnion.mpr
        ⟨some (z, canonicalSites, oppositeSites),
          ⟨⟨⟨hs, hz⟩, rfl⟩, rfl⟩⟩
    · exact Set.mem_iUnion.mpr ⟨none, ⟨hs, hvalid⟩⟩

theorem canonical_mem_jointDominantStoppedCandidates
    {t : DominoTiling} {canonicalBudget oppositeBudget : ℕ}
    {z : TypedFavoriteTilingTraceCode t}
    {canonicalSites oppositeSites : Finset Point} {x : Point}
    (hcanonicalCard : canonicalSites.card ≤ canonicalBudget)
    (hoppositeCard : oppositeSites.card ≤ oppositeBudget)
    (hx : x ∈ canonicalSites) :
    (.canonical, x) ∈ jointDominantStoppedCandidates
      (t := t) (canonicalBudget := canonicalBudget)
      (oppositeBudget := oppositeBudget)
      (some (z, canonicalSites, oppositeSites)) := by
  classical
  simp [jointDominantStoppedCandidates, hcanonicalCard, hoppositeCard, hx]

theorem opposite_mem_jointDominantStoppedCandidates
    {t : DominoTiling} {canonicalBudget oppositeBudget : ℕ}
    {z : TypedFavoriteTilingTraceCode t}
    {canonicalSites oppositeSites : Finset Point} {x : Point}
    (hcanonicalCard : canonicalSites.card ≤ canonicalBudget)
    (hoppositeCard : oppositeSites.card ≤ oppositeBudget)
    (hx : x ∈ oppositeSites) :
    (.thetaOneShiftedOpposite, x) ∈ jointDominantStoppedCandidates
      (t := t) (canonicalBudget := canonicalBudget)
      (oppositeBudget := oppositeBudget)
      (some (z, canonicalSites, oppositeSites)) := by
  classical
  simp [jointDominantStoppedCandidates, hcanonicalCard, hoppositeCard, hx]

/-- The opposite spatial source is deliberately routed to the genuine
one-step-shift event rather than identified with a same-path source event. -/
theorem opposite_source_uses_shiftedCheckerSourceEvent
    (d : Tilings.CheckerDirection)
    (m k w low externalLow externalHigh cut : ℕ) :
    shiftedCheckerSourceEvent d m k w low externalLow externalHigh cut =
      oneStepRecenter ⁻¹'
        TilingShellZeroSourcePartition.shellZeroSourceEvent
          (shiftedCheckerTiling d) m k w low externalLow externalHigh cut := by
  rfl

theorem reflectedEven_source_uses_reflectedColumnSourceEvent
    (m k w low externalLow externalHigh cut : ℕ) :
    allTilingDominantSourceEvent .reflectedEvenColumnsOpposite
        m k w low externalLow externalHigh cut =
      reflectedColumnSourceEvent .evenColumns
        m k w low externalLow externalHigh cut := by
  rfl

theorem reflectedOdd_source_uses_reflectedColumnSourceEvent
    (m k w low externalLow externalHigh cut : ℕ) :
    allTilingDominantSourceEvent .reflectedOddColumnsOpposite
        m k w low externalLow externalHigh cut =
      reflectedColumnSourceEvent .oddColumns
        m k w low externalLow externalHigh cut := by
  rfl

end

end Erdos1165.HLOZDominantStoppedCandidatePartition
