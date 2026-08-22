/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCanonicalDominantStoppedCandidateFamily
import ErdosProblems.Erdos1165.HLOZHeterogeneousFilteredTransitionFactors

/-!
# One stopped-history candidate family for both dominant spatial sources

The whole low transition is not a canonical-source event.  For a fixed
tiling, an atom in this file fixes the retained typed trace together with
both exact normalized candidate Finsets.  Candidates are tagged as
canonical or opposite.  The opposite screen is an explicit input because it
must be the pullback through the checker one-step recentering or the column
reflection recorded by `oppositeDominantSource`; it is never replaced by a
same-path raw-band window.

The resulting deterministic data supplies a genuine `.lowAtomwise` factor.
The only field added at that final constructor is the later atomwise future
escape certificate.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZAllTilingDominantStoppedCandidateFamily

open HLOZCanonicalDominantStoppedCandidateFamily
open HLOZCanonicalDominantCandidateWindows
open HLOZDominantStoppedCandidatePartition HLOZGapRandomClockScreen
open HLOZPathEvents HLOZSourceCorrectFutureTransition
open HLOZHeterogeneousFilteredTransitionFactors
open HLOZStoppedHistoryCandidateFuture HLOZTilingGapRandomClockScreen
open HLOZTypedStoppedCandidateConditionalProduct
open HLOZTypedStoppedCandidateFamily TilingConditionalCappedMarginalization
open TilingTypedFavoriteTrace VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The opposite-source narrow screen after the exact source normalization.
Its measurability is kept with the screen, while its conditional product law
is stated separately on each joint stopped atom. -/
structure TransportedOppositeDominantScreen
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) where
  /-- Narrow source-coordinate event on the normalized path. -/
  normalizedNear : TypedFavoriteTilingTraceCode t → Point → Set WalkPath
  /-- Measurability of its literal checker-shift/column-reflection pullback. -/
  pullback_measurable : ∀ z x, MeasurableSet
    {s : WalkPath |
      (oppositeDominantSource t).normalizePath s ∈
        normalizedNear z ((oppositeDominantSource t).normalizePoint s x)}

/-- Literal pullback of an opposite narrow screen through the carrier's
path and endpoint normalization. -/
def TransportedOppositeDominantScreen.near
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    (screen : TransportedOppositeDominantScreen t m cutoff band)
    (z : TypedFavoriteTilingTraceCode t) (x : Point) : Set WalkPath :=
  {s : WalkPath |
    (oppositeDominantSource t).normalizePath s ∈
      screen.normalizedNear z
        ((oppositeDominantSource t).normalizePoint s x)}

/-- Canonical and transported-opposite narrow screens on a joint history. -/
def jointDominantStoppedCandidateNear
    {t : DominoTiling} {canonicalBudget oppositeBudget : ℕ}
    (m cutoff : ℕ) (band : RandomClockBand)
    (canonicalWindow : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (oppositeScreen : TransportedOppositeDominantScreen t m cutoff band) :
    JointDominantStoppedCandidateHistory
      t canonicalBudget oppositeBudget → TaggedDominantCandidate →
      Set WalkPath
  | none, _ => ∅
  | some (z, _, _), (.canonical, x) =>
      stoppedCandidateWindowEvent m cutoff band canonicalWindow z x
  | some (z, _, _), (.thetaOneShiftedOpposite, x) =>
      oppositeScreen.near z x

theorem measurableSet_jointDominantStoppedCandidateNear
    {t : DominoTiling} {canonicalBudget oppositeBudget : ℕ}
    (m cutoff : ℕ) (band : RandomClockBand)
    (canonicalWindow : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (oppositeScreen : TransportedOppositeDominantScreen t m cutoff band)
    (h : JointDominantStoppedCandidateHistory
      t canonicalBudget oppositeBudget) (x : TaggedDominantCandidate) :
    MeasurableSet (jointDominantStoppedCandidateNear m cutoff band
      canonicalWindow oppositeScreen h x) := by
  cases h with
  | none => exact MeasurableSet.empty
  | some h =>
      rcases x with ⟨source, x⟩
      cases source with
      | canonical =>
          exact measurableSet_stoppedCandidateWindowEvent
            m cutoff band canonicalWindow h.1 x
      | thetaOneShiftedOpposite =>
          exact oppositeScreen.pullback_measurable h.1 x

/-- Exact conditional stopped-history family for the union of the canonical
and genuinely transported opposite sources. -/
noncomputable def conditionalAllTilingDominantStoppedHistoryCandidateFamily
    (t : DominoTiling) (m k cutoff canonicalBudget oppositeBudget : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand)
    (canonicalWindow : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (oppositeScreen : TransportedOppositeDominantScreen t m cutoff band)
    (ratio : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hratio : ratio ≠ ∞)
    (coordinateData : ∀
      (h : JointDominantStoppedCandidateHistory
        t canonicalBudget oppositeBudget)
      (x : TaggedDominantCandidate),
      x ∈ jointDominantStoppedCandidates h →
        TilingConditionalFactoredStoppedCoordinateData
          (fun _ : Unit ↦ jointDominantStoppedCandidatePiece
            t m k cutoff canonicalBudget oppositeBudget
              stage previous band h)
          (jointDominantStoppedCandidatePiece
              t m k cutoff canonicalBudget oppositeBudget
                stage previous band h ∩
            jointDominantStoppedCandidateNear m cutoff band
              canonicalWindow oppositeScreen h x)
          ratio) :
    StoppedHistoryCandidateFamily
      (JointDominantStoppedCandidateHistory
        t canonicalBudget oppositeBudget)
      TaggedDominantCandidate previous
      (canonicalBudget + oppositeBudget) ratio where
  piece := jointDominantStoppedCandidatePiece
    t m k cutoff canonicalBudget oppositeBudget stage previous band
  candidates := jointDominantStoppedCandidates
  near := jointDominantStoppedCandidateNear
    m cutoff band canonicalWindow oppositeScreen
  piece_pairwise := pairwise_disjoint_jointDominantStoppedCandidatePiece
    t m k cutoff canonicalBudget oppositeBudget hstage previous band
  piece_measurable := measurableSet_jointDominantStoppedCandidatePiece
    t m k cutoff canonicalBudget oppositeBudget hstageMeasurable
      hpreviousMeasurable band
  piece_union := iUnion_jointDominantStoppedCandidatePiece
    t m k cutoff canonicalBudget oppositeBudget hstage band
  candidate_card := jointDominantStoppedCandidates_card_le
  coordinate_ratio := by
    intro h x hx
    exact coordinate_ratio_of_tilingConditionalFactoredStoppedCoordinateData
      (measurableSet_jointDominantStoppedCandidatePiece
        t m k cutoff canonicalBudget oppositeBudget hstageMeasurable
          hpreviousMeasurable band h)
      (measurableSet_jointDominantStoppedCandidateNear
        m cutoff band canonicalWindow oppositeScreen h x)
      hratio (coordinateData h x hx)

/-- A whole filtered low target enters the joint some-candidate event once
its stopped history has both source budgets and its selected tagged source
has the corresponding narrow screen. -/
theorem next_subset_conditionalAllTilingDominantSomeCandidate
    (t : DominoTiling) (m k cutoff canonicalBudget oppositeBudget : ℕ)
    (stage previous next : Set WalkPath) (band : RandomClockBand)
    (canonicalWindow : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (oppositeScreen : TransportedOppositeDominantScreen t m cutoff band)
    (ratio : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hnextPrevious : next ⊆ previous)
    (hcanonicalBudget : ∀ s ∈ next,
      (tilingAllTilingDominantSourceRandomClockBandSites
        (canonicalDominantSource t) m cutoff s band).card ≤ canonicalBudget)
    (hoppositeBudget : ∀ s ∈ next,
      (tilingAllTilingDominantSourceRandomClockBandSites
        (oppositeDominantSource t) m cutoff s band).card ≤ oppositeBudget)
    (hratio : ratio ≠ ∞)
    (coordinateData : ∀
      (h : JointDominantStoppedCandidateHistory
        t canonicalBudget oppositeBudget)
      (x : TaggedDominantCandidate),
      x ∈ jointDominantStoppedCandidates h →
        TilingConditionalFactoredStoppedCoordinateData
          (fun _ : Unit ↦ jointDominantStoppedCandidatePiece
            t m k cutoff canonicalBudget oppositeBudget
              stage previous band h)
          (jointDominantStoppedCandidatePiece
              t m k cutoff canonicalBudget oppositeBudget
                stage previous band h ∩
            jointDominantStoppedCandidateNear m cutoff band
              canonicalWindow oppositeScreen h x)
          ratio)
    (hsmallWindow : ∀ s ∈ next,
      ∃ (z : TypedFavoriteTilingTraceCode t)
        (x : TaggedDominantCandidate),
        s ∈ typedFavoriteTilingStagePiece t m k stage z ∧
        x.2 ∈ tilingAllTilingDominantSourceRandomClockBandSites
          (match x.1 with
            | .canonical => canonicalDominantSource t
            | .thetaOneShiftedOpposite => oppositeDominantSource t)
          m cutoff s band ∧
        s ∈ jointDominantStoppedCandidateNear
          (canonicalBudget := canonicalBudget)
          (oppositeBudget := oppositeBudget) m cutoff band
          canonicalWindow oppositeScreen
            (some (z,
              tilingAllTilingDominantSourceRandomClockBandSites
                (canonicalDominantSource t) m cutoff s band,
              tilingAllTilingDominantSourceRandomClockBandSites
                (oppositeDominantSource t) m cutoff s band)) x) :
    next ⊆
      (conditionalAllTilingDominantStoppedHistoryCandidateFamily
        t m k cutoff canonicalBudget oppositeBudget stage previous band
          canonicalWindow oppositeScreen ratio hstageMeasurable
            hpreviousMeasurable hstage hratio coordinateData).someCandidate := by
  classical
  intro s hs
  rcases hsmallWindow s hs with ⟨z, x, hz, hxSource, hxNear⟩
  let canonicalSites :=
    tilingAllTilingDominantSourceRandomClockBandSites
      (canonicalDominantSource t) m cutoff s band
  let oppositeSites :=
    tilingAllTilingDominantSourceRandomClockBandSites
      (oppositeDominantSource t) m cutoff s band
  let h : JointDominantStoppedCandidateHistory
      t canonicalBudget oppositeBudget :=
    some (z, canonicalSites, oppositeSites)
  refine Set.mem_iUnion.mpr ⟨h, Set.mem_iUnion.mpr ⟨x, ?_⟩⟩
  refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
  · rcases x with ⟨source, x⟩
    cases source with
    | canonical =>
        change (.canonical, x) ∈ jointDominantStoppedCandidates
          (some (z, canonicalSites, oppositeSites))
        exact canonical_mem_jointDominantStoppedCandidates
          (t := t) (z := z) (canonicalSites := canonicalSites)
          (oppositeSites := oppositeSites) (x := x)
          (hcanonicalBudget s hs) (hoppositeBudget s hs) hxSource
    | thetaOneShiftedOpposite =>
        change (.thetaOneShiftedOpposite, x) ∈
          jointDominantStoppedCandidates
            (some (z, canonicalSites, oppositeSites))
        exact opposite_mem_jointDominantStoppedCandidates
          (t := t) (z := z) (canonicalSites := canonicalSites)
          (oppositeSites := oppositeSites) (x := x)
          (hcanonicalBudget s hs) (hoppositeBudget s hs) hxSource
  · exact ⟨⟨⟨⟨hnextPrevious hs, hz⟩, rfl⟩, rfl⟩, hxNear⟩

/-! ## Deterministic low data and the public whole-source factor -/

/-- Deterministic stopped-coordinate data for one whole low rank.  No future
escape certificate and no target transition inequality occurs here. -/
structure AllTilingDominantTypedLowConditionalCoordinateData
    (t : DominoTiling) (m k canonicalBudget oppositeBudget : ℕ)
    (previous : Set WalkPath) (candidateRatio : ℝ≥0∞) where
  cutoff : ℕ
  stage : Set WalkPath
  band : RandomClockBand
  canonicalWindow : TypedFavoriteTilingTraceCode t → Point → Finset ℕ
  oppositeScreen : TransportedOppositeDominantScreen t m cutoff band
  stage_measurable : MeasurableSet stage
  previous_measurable : MeasurableSet previous
  stage_subset : stage ⊆ thresholdReachStage m k
  candidateRatio_ne_top : candidateRatio ≠ ∞
  coordinateData : ∀
    (h : JointDominantStoppedCandidateHistory
      t canonicalBudget oppositeBudget)
    (x : TaggedDominantCandidate),
    x ∈ jointDominantStoppedCandidates h →
      TilingConditionalFactoredStoppedCoordinateData
        (fun _ : Unit ↦ jointDominantStoppedCandidatePiece
          t m k cutoff canonicalBudget oppositeBudget
            stage previous band h)
        (jointDominantStoppedCandidatePiece
            t m k cutoff canonicalBudget oppositeBudget
              stage previous band h ∩
          jointDominantStoppedCandidateNear m cutoff band
            canonicalWindow oppositeScreen h x)
        candidateRatio

namespace AllTilingDominantTypedLowConditionalCoordinateData

noncomputable def family
    {t : DominoTiling} {m k canonicalBudget oppositeBudget : ℕ}
    {previous : Set WalkPath} {candidateRatio : ℝ≥0∞}
    (data : AllTilingDominantTypedLowConditionalCoordinateData
      t m k canonicalBudget oppositeBudget previous candidateRatio) :
    StoppedHistoryCandidateFamily
      (JointDominantStoppedCandidateHistory
        t canonicalBudget oppositeBudget)
      TaggedDominantCandidate previous
      (canonicalBudget + oppositeBudget) candidateRatio :=
  conditionalAllTilingDominantStoppedHistoryCandidateFamily
    t m k data.cutoff canonicalBudget oppositeBudget data.stage previous
      data.band data.canonicalWindow data.oppositeScreen candidateRatio
        data.stage_measurable data.previous_measurable data.stage_subset
          data.candidateRatio_ne_top data.coordinateData

/-- The requested whole-low-source constructor.  It consumes one joint
canonical/opposite history family and adds only the later future escape. -/
noncomputable def factor
    {Index State : Type} [Countable Index] [Countable State]
    {t : DominoTiling} {m k canonicalBudget oppositeBudget : ℕ}
    {previous next : Set WalkPath}
    {candidateRatio escapeCost q : ℝ≥0∞}
    (data : AllTilingDominantTypedLowConditionalCoordinateData
      t m k canonicalBudget oppositeBudget previous candidateRatio)
    (escape : CountableAtomFutureFactor Index State
      data.family.someCandidate next escapeCost)
    (cost_le : ((canonicalBudget + oppositeBudget : ℕ) : ℝ≥0∞) *
      candidateRatio * escapeCost ≤ q) :
    SourceCorrectTransitionFactor
      (JointDominantStoppedCandidateHistory
        t canonicalBudget oppositeBudget)
      TaggedDominantCandidate State previous next q :=
  .lowAtomwise (canonicalBudget + oppositeBudget) candidateRatio escapeCost
    { candidate := data.family, escape := escape } cost_le

end AllTilingDominantTypedLowConditionalCoordinateData

/-! ## Exact canonical-window certificates for both tagged sources -/

/-- A deterministic whole-source package stated in terms of the semantic
stopped-coordinate skeleton at the universal conditional cost `1` and the
exact broad/narrow canonical window certificate.  For an opposite tagged candidate the skeleton is on
the normalized source path because `oppositeScreen.near` is its literal
pullback. -/
structure AllTilingDominantConditionalWindowProductData
    (t : DominoTiling) (m k canonicalBudget oppositeBudget : ℕ)
    (previous : Set WalkPath) (candidateRatio : ℝ≥0∞) where
  cutoff : ℕ
  stage : Set WalkPath
  band : RandomClockBand
  canonicalWindow : TypedFavoriteTilingTraceCode t → Point → Finset ℕ
  oppositeScreen : TransportedOppositeDominantScreen t m cutoff band
  stage_measurable : MeasurableSet stage
  previous_measurable : MeasurableSet previous
  stage_subset : stage ⊆ thresholdReachStage m k
  candidateRatio_ne_top : candidateRatio ≠ ∞
  skeleton : ∀
    (h : JointDominantStoppedCandidateHistory
      t canonicalBudget oppositeBudget)
    (x : TaggedDominantCandidate),
    x ∈ jointDominantStoppedCandidates h →
      TilingConditionalFactoredStoppedCoordinateData
        (fun _ : Unit ↦ jointDominantStoppedCandidatePiece
          t m k cutoff canonicalBudget oppositeBudget
            stage previous band h)
        (jointDominantStoppedCandidatePiece
            t m k cutoff canonicalBudget oppositeBudget
              stage previous band h ∩
          jointDominantStoppedCandidateNear m cutoff band
            canonicalWindow oppositeScreen h x)
        (1 : ℝ≥0∞)
  windowCertificate : ∀
    (h : JointDominantStoppedCandidateHistory
      t canonicalBudget oppositeBudget)
    (x : TaggedDominantCandidate)
    (hx : x ∈ jointDominantStoppedCandidates h),
      CanonicalDominantWindowProductCertificate
        (skeleton h x hx) candidateRatio

namespace AllTilingDominantConditionalWindowProductData

/-- Replace the universal cost-one bound in every semantic skeleton by the
checked finite negative-binomial window ratio. -/
noncomputable def coordinateData
    {t : DominoTiling} {m k canonicalBudget oppositeBudget : ℕ}
    {previous : Set WalkPath} {candidateRatio : ℝ≥0∞}
    (data : AllTilingDominantConditionalWindowProductData
      t m k canonicalBudget oppositeBudget previous candidateRatio)
    (h : JointDominantStoppedCandidateHistory
      t canonicalBudget oppositeBudget)
    (x : TaggedDominantCandidate)
    (hx : x ∈ jointDominantStoppedCandidates h) :
    TilingConditionalFactoredStoppedCoordinateData
      (fun _ : Unit ↦ jointDominantStoppedCandidatePiece
        t m k data.cutoff canonicalBudget oppositeBudget
          data.stage previous data.band h)
      (jointDominantStoppedCandidatePiece
          t m k data.cutoff canonicalBudget oppositeBudget
            data.stage previous data.band h ∩
        jointDominantStoppedCandidateNear m data.cutoff data.band
          data.canonicalWindow data.oppositeScreen h x)
      candidateRatio :=
  conditionalFactoredDataOfCanonicalDominantWindowCertificate
    (data.skeleton h x hx) (data.windowCertificate h x hx)

/-- Forget the semantic construction details after the finite coordinate
law has been checked. -/
noncomputable def toCoordinateData
    {t : DominoTiling} {m k canonicalBudget oppositeBudget : ℕ}
    {previous : Set WalkPath} {candidateRatio : ℝ≥0∞}
    (data : AllTilingDominantConditionalWindowProductData
      t m k canonicalBudget oppositeBudget previous candidateRatio) :
    AllTilingDominantTypedLowConditionalCoordinateData
      t m k canonicalBudget oppositeBudget previous candidateRatio where
  cutoff := data.cutoff
  stage := data.stage
  band := data.band
  canonicalWindow := data.canonicalWindow
  oppositeScreen := data.oppositeScreen
  stage_measurable := data.stage_measurable
  previous_measurable := data.previous_measurable
  stage_subset := data.stage_subset
  candidateRatio_ne_top := data.candidateRatio_ne_top
  coordinateData := data.coordinateData

noncomputable def family
    {t : DominoTiling} {m k canonicalBudget oppositeBudget : ℕ}
    {previous : Set WalkPath} {candidateRatio : ℝ≥0∞}
    (data : AllTilingDominantConditionalWindowProductData
      t m k canonicalBudget oppositeBudget previous candidateRatio) :
    StoppedHistoryCandidateFamily
      (JointDominantStoppedCandidateHistory
        t canonicalBudget oppositeBudget)
      TaggedDominantCandidate previous
      (canonicalBudget + oppositeBudget) candidateRatio :=
  data.toCoordinateData.family

/-- Final whole-source low constructor from exact conditional products.  Its
only additional semantic input is the atomwise future escape factor. -/
noncomputable def factor
    {Index State : Type} [Countable Index] [Countable State]
    {t : DominoTiling} {m k canonicalBudget oppositeBudget : ℕ}
    {previous next : Set WalkPath}
    {candidateRatio escapeCost q : ℝ≥0∞}
    (data : AllTilingDominantConditionalWindowProductData
      t m k canonicalBudget oppositeBudget previous candidateRatio)
    (escape : CountableAtomFutureFactor Index State
      data.family.someCandidate next escapeCost)
    (cost_le : ((canonicalBudget + oppositeBudget : ℕ) : ℝ≥0∞) *
      candidateRatio * escapeCost ≤ q) :
    SourceCorrectTransitionFactor
      (JointDominantStoppedCandidateHistory
        t canonicalBudget oppositeBudget)
      TaggedDominantCandidate State previous next q :=
  data.toCoordinateData.factor escape cost_le

end AllTilingDominantConditionalWindowProductData

/-! ## Source-budget and rankwise specializations -/

/-- Corrected dominant-source analogue of the old raw-site
`CandidateBudgetTypedLowTransitionData`.  Both normalized halves use the
literal `J / 4` source budget.  The equality prevents a package from hiding
a different random-clock band inside its deterministic coordinate data. -/
structure CandidateBudgetAllTilingDominantLowConditionalData
    (t : DominoTiling) (m k : ℕ) (previous : Set WalkPath)
    (candidateRatio : ℝ≥0∞) where
  band : RandomClockBand
  data : AllTilingDominantConditionalWindowProductData
    t m k (dominantSourceCandidateBudget48 m band.beta)
      (dominantSourceCandidateBudget48 m band.beta)
      previous candidateRatio
  data_band : data.band = band

namespace CandidateBudgetAllTilingDominantLowConditionalData

abbrev sourceBudget
    {t : DominoTiling} {m k : ℕ} {previous : Set WalkPath}
    {candidateRatio : ℝ≥0∞}
    (data : CandidateBudgetAllTilingDominantLowConditionalData
      t m k previous candidateRatio) : ℕ :=
  dominantSourceCandidateBudget48 m data.band.beta

noncomputable def family
    {t : DominoTiling} {m k : ℕ} {previous : Set WalkPath}
    {candidateRatio : ℝ≥0∞}
    (data : CandidateBudgetAllTilingDominantLowConditionalData
      t m k previous candidateRatio) :
    StoppedHistoryCandidateFamily
      (JointDominantStoppedCandidateHistory
        t data.sourceBudget data.sourceBudget)
      TaggedDominantCandidate previous
      (data.sourceBudget + data.sourceBudget) candidateRatio :=
  data.data.family

/-- Assembly-facing corrected dominant low factor.  It adds only the
atomwise future escape and numerical cost comparison and returns the
heterogeneous wrapper used by the rank selector. -/
noncomputable def factor
    {Index State : Type} [Countable Index] [Countable State]
    {t : DominoTiling} {m k : ℕ} {previous next : Set WalkPath}
    {candidateRatio escapeCost q : ℝ≥0∞}
    (data : CandidateBudgetAllTilingDominantLowConditionalData
      t m k previous candidateRatio)
    (escape : CountableAtomFutureFactor Index State
      data.family.someCandidate next escapeCost)
    (cost_le : ((data.sourceBudget + data.sourceBudget : ℕ) : ℝ≥0∞) *
      candidateRatio * escapeCost ≤ q) :
    HeterogeneousSourceCorrectTransitionFactor previous next q :=
  .of (data.data.factor escape cost_le)

end CandidateBudgetAllTilingDominantLowConditionalData

/-- Rank one retains the explicit invalid-support atom over the whole prior
path space. -/
abbrev FirstCandidateBudgetAllTilingDominantLowConditionalData
    (t : DominoTiling) (m : ℕ) (candidateRatio : ℝ≥0∞) :=
  CandidateBudgetAllTilingDominantLowConditionalData
    t m 1 Set.univ candidateRatio

/-- Rank two is conditioned on the already filtered first transition. -/
abbrev SecondCandidateBudgetAllTilingDominantLowConditionalData
    (t : DominoTiling) (m : ℕ) (previous : Set WalkPath)
    (candidateRatio : ℝ≥0∞) :=
  CandidateBudgetAllTilingDominantLowConditionalData
    t m 2 previous candidateRatio

/-- Rank three is conditioned on the already filtered second transition. -/
abbrev ThirdCandidateBudgetAllTilingDominantLowConditionalData
    (t : DominoTiling) (m : ℕ) (previous : Set WalkPath)
    (candidateRatio : ℝ≥0∞) :=
  CandidateBudgetAllTilingDominantLowConditionalData
    t m 3 previous candidateRatio

end

end Erdos1165.HLOZAllTilingDominantStoppedCandidateFamily
