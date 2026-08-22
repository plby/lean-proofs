/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZGapRandomClockScreen
import ErdosProblems.Erdos1165.HLOZDynamicThresholdedScreening
import ErdosProblems.Erdos1165.TilingLazyDecomposition
import ErdosProblems.Erdos1165.TilingVariableStoppedTracePartition
import ErdosProblems.Erdos1165.TilingExternalPhaseSplit

/-!
# Random-clock candidates for every HLOZ domino tiling

This file replaces the checkerboard-specific deletion used by the first
random-clock screen with the state-dependent deletion attached to an
arbitrary `DominoTiling`.  The phase is still recorded by `Orientation`, but
the retained sites, lazy local times, and distinguished domino bases all use
the supplied tiling.  No symmetry reduction to the canonical east tiling is
made.

The last section exposes the exact trace partition on which the all-tiling
product law acts.  Thus a later probability estimate can use
`TilingStoppedCoordinateProductSpec` without reintroducing a deterministic
creation-time union.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZTilingGapRandomClockScreen

open HLOZDynamicThresholdedScreening HLOZGapEstimate
open HLOZGapRandomClockScreen HLOZPathEvents HLOZProposition48Candidates
open HLOZGapCandidateMeasurability NearFavoriteShells ScreeningInstantiation
open TilingLazyDecomposition TilingVariableStoppedTracePartition
open VariableStoppedTracePartition
open LazyDecomposition
open HLOZGapFixedPair HLOZGapGuardedPointReturn HLOZGapMeshEscape
open HLOZGapPointReturn HLOZGapStoppedCandidate
open PreStoppingSpatialLaw StoppedInsertion
open TilingExternalPhaseSplit

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-! ## Genuine all-tiling stopped candidate data -/

/-- Decode the finite endpoint/midpoint tag carried by a random-clock band. -/
def externalVertexPhaseOfBool : Bool → ExternalVertexPhase
  | false => .endpoint
  | true => .midpoint

/-- The genuinely phase-filtered stateful external local time. -/
def pathPhaseFilteredExternalLocalTime (t : DominoTiling) (o : Orientation)
    (phase : Bool) (s : WalkPath) (n : ℕ) (x : Point) : ℕ :=
  phasedExternalVertexLocalTime t o (externalVertexPhaseOfBool phase)
    (finitePathList (pathPrefix s n)) x

/-- The genuinely phase-filtered stateful external range. -/
def pathPhaseFilteredExternalVisitedSites (t : DominoTiling) (o : Orientation)
    (phase : Bool) (s : WalkPath) (n : ℕ) : Finset Point :=
  phasedExternalVertexVisitedSites t o (externalVertexPhaseOfBool phase)
    (finitePathList (pathPrefix s n))

/-- Stateful external range at the genuine old creation clock. -/
def tilingRandomClockVisitedSites (t : DominoTiling) (m cutoff : ℕ)
    (band : RandomClockBand) (s : WalkPath) : Finset Point :=
  pathPhaseFilteredExternalVisitedSites t band.orientation band.vertexPhase s
    (pathTruncatedLevelTime m band.oldRank cutoff s)

/-- External-local-time threshold at the same random clock. -/
def tilingRandomClockExternalLargeEvent (t : DominoTiling) (m cutoff : ℕ)
    (band : RandomClockBand) (x : Point) : Set WalkPath :=
  {s | band.externalThreshold ≤
    pathPhaseFilteredExternalLocalTime t band.orientation band.vertexPhase s
      (pathTruncatedLevelTime m band.oldRank cutoff s) x}

/-- Both endpoints, for `t`, of every favorite domino at a fixed time. -/
noncomputable def favoriteTilingDominoSites
    (t : DominoTiling) (s : WalkPath) (n : ℕ) : Finset Point :=
  favoriteSites s n ∪ (favoriteSites s n).image (tilingPartner t)

/-- Both endpoints of the favorite dominoes, evaluated at the old clock. -/
noncomputable def tilingRandomClockDistinguishedSites
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (s : WalkPath) : Finset Point :=
  favoriteTilingDominoSites t s
    (pathTruncatedLevelTime m band.oldRank cutoff s)

/-- Actual local-time profile at the random old clock. -/
def tilingRandomClockTotalLocalTime (m cutoff : ℕ)
    (band : RandomClockBand) (s : WalkPath) (x : Point) : ℕ :=
  localTime s (pathTruncatedLevelTime m band.oldRank cutoff s) x

/-- Proposition 4.8 candidate sites after genuine state-dependent tiling
deletion. -/
noncomputable def tilingRandomClockBandSites
    (t : DominoTiling) (m cutoff : ℕ) (s : WalkPath)
    (band : RandomClockBand) : Finset Point := by
  classical
  exact boundedCandidates
    ((tilingRandomClockVisitedSites t m cutoff band s).filter fun x ↦
      s ∈ tilingRandomClockExternalLargeEvent t m cutoff band x ∧
        x ∉ tilingRandomClockDistinguishedSites t m cutoff band s)
    (fun x ↦ (m - tilingRandomClockTotalLocalTime m cutoff band s x) /
      shellWidth48 m)
    (shellCount48 m band.beta)

theorem tilingRandomClockBandSites_eq_dynamic
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (s : WalkPath) :
    tilingRandomClockBandSites t m cutoff s band =
      dynamicStoppedCandidateSites48
        (tilingRandomClockVisitedSites t m cutoff band)
        (tilingRandomClockExternalLargeEvent t m cutoff band)
        (tilingRandomClockDistinguishedSites t m cutoff band)
        (tilingRandomClockTotalLocalTime m cutoff band) m band.beta s := by
  rfl

theorem tilingRandomClockBandOverflow_eq_dynamic
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) :
    {s | candidateBudget48 m band.beta <
      (tilingRandomClockBandSites t m cutoff s band).card} =
      dynamicStoppedCandidateOverflow48
        (tilingRandomClockVisitedSites t m cutoff band)
        (tilingRandomClockExternalLargeEvent t m cutoff band)
        (tilingRandomClockDistinguishedSites t m cutoff band)
        (tilingRandomClockTotalLocalTime m cutoff band) m band.beta := by
  ext s
  simp only [dynamicStoppedCandidateOverflow48, Set.mem_ofPred_eq,
    tilingRandomClockBandSites_eq_dynamic]

/-! ## Finite-prefix measurability -/

theorem measurable_pathPhasedExternalLocalTime
    (t : DominoTiling) (o : LazyDecomposition.Orientation)
    (n : ℕ) (x : Point) :
    Measurable fun s : WalkPath ↦ pathPhasedExternalLocalTime t o s n x := by
  change Measurable
    ((fun u : Fin (n + 1) → Point ↦
        phasedExternalLocalTime t o (finitePathList u) x) ∘
      fun s : WalkPath ↦ pathPrefix s n)
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

theorem measurable_pathPhasedBoundaryLocalTime
    (o : LazyDecomposition.Orientation) (n : ℕ) (x : Point) :
    Measurable fun s : WalkPath ↦ pathPhasedBoundaryLocalTime o s n x := by
  change Measurable
    ((fun u : Fin (n + 1) → Point ↦
        phasedBoundaryLocalTime o (finitePathList u) x) ∘
      fun s : WalkPath ↦ pathPrefix s n)
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

theorem measurable_pathPhasedLazyLocalTime
    (t : DominoTiling) (o : LazyDecomposition.Orientation)
    (n : ℕ) (x : Point) :
    Measurable fun s : WalkPath ↦ pathPhasedLazyLocalTime t o s n x := by
  change Measurable
    ((fun u : Fin (n + 1) → Point ↦
        phasedLazyLocalTime t o (finitePathList u) x) ∘
      fun s : WalkPath ↦ pathPrefix s n)
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

theorem measurable_pathPhasedExternalVisitedSites
    (t : DominoTiling) (o : LazyDecomposition.Orientation) (n : ℕ) :
    Measurable fun s : WalkPath ↦ pathPhasedExternalVisitedSites t o s n := by
  change Measurable
    ((fun u : Fin (n + 1) → Point ↦
        phasedExternalVisitedSites t o (finitePathList u)) ∘
      fun s : WalkPath ↦ pathPrefix s n)
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

theorem measurable_pathPhaseFilteredExternalLocalTime
    (t : DominoTiling) (o : LazyDecomposition.Orientation)
    (phase : Bool) (n : ℕ) (x : Point) :
    Measurable fun s : WalkPath ↦
      pathPhaseFilteredExternalLocalTime t o phase s n x := by
  change Measurable
    ((fun u : Fin (n + 1) → Point ↦
        phasedExternalVertexLocalTime t o (externalVertexPhaseOfBool phase)
          (finitePathList u) x) ∘
      fun s : WalkPath ↦ pathPrefix s n)
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

theorem measurable_pathPhaseFilteredExternalVisitedSites
    (t : DominoTiling) (o : LazyDecomposition.Orientation)
    (phase : Bool) (n : ℕ) :
    Measurable fun s : WalkPath ↦
      pathPhaseFilteredExternalVisitedSites t o phase s n := by
  change Measurable
    ((fun u : Fin (n + 1) → Point ↦
        phasedExternalVertexVisitedSites t o (externalVertexPhaseOfBool phase)
          (finitePathList u)) ∘
      fun s : WalkPath ↦ pathPrefix s n)
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

/-- Boolean form of the exact endpoint/midpoint phase selector used by band
enumeration. -/
theorem exists_boolPhase_threshold_half_le_and_mem
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (x : Point) (threshold : ℕ) (hpositive : 2 ≤ threshold)
    (hthreshold : threshold ≤ pathPhasedExternalLocalTime t o s n x) :
    ∃ phase : Bool,
      threshold / 2 ≤ pathPhaseFilteredExternalLocalTime t o phase s n x ∧
        x ∈ pathPhaseFilteredExternalVisitedSites t o phase s n := by
  obtain ⟨phase, hlocal, hvisited⟩ :=
    exists_vertexPhase_phasedExternal_threshold_half_le_and_mem
      t o (finitePathList (pathPrefix s n)) x threshold hpositive hthreshold
  cases phase with
  | endpoint => exact ⟨false, hlocal, hvisited⟩
  | midpoint => exact ⟨true, hlocal, hvisited⟩

theorem measurable_favoriteTilingBases (t : DominoTiling) (n : ℕ) :
    Measurable fun s : WalkPath ↦ favoriteTilingBases t s n := by
  exact (measurable_of_countable
    (fun S : Finset Point ↦ S.image (tilingBase t))).comp
      (measurable_favoriteSites n)

theorem measurable_favoriteTilingDominoSites (t : DominoTiling) (n : ℕ) :
    Measurable fun s : WalkPath ↦ favoriteTilingDominoSites t s n := by
  exact (measurable_of_countable
    (fun S : Finset Point ↦ S ∪ S.image (tilingPartner t))).comp
      (measurable_favoriteSites n)

theorem measurableSet_memberEvent_tilingRandomClockVisitedSites
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) (x : Point) :
    MeasurableSet (ExternalThickCount.memberEvent
      (tilingRandomClockVisitedSites t m cutoff band) x) := by
  rw [show ExternalThickCount.memberEvent
      (tilingRandomClockVisitedSites t m cutoff band) x =
        ⋃ n : ℕ,
          {s | pathTruncatedLevelTime m band.oldRank cutoff s = n} ∩
            {s | x ∈ pathPhaseFilteredExternalVisitedSites t band.orientation
              band.vertexPhase s n} by
    ext s
    simp only [ExternalThickCount.memberEvent, tilingRandomClockVisitedSites,
      Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hs
      exact ⟨pathTruncatedLevelTime m band.oldRank cutoff s, rfl, hs⟩
    · rintro ⟨n, hn, hs⟩
      simpa only [hn] using hs]
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_pathTruncatedLevelTime_eq m band.oldRank cutoff n).inter
      ((measurable_pathPhaseFilteredExternalVisitedSites t band.orientation
        band.vertexPhase n)
        (Set.to_countable {S : Finset Point | x ∈ S}).measurableSet)

theorem measurableSet_tilingRandomClockExternalLargeEvent
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) (x : Point) :
    MeasurableSet (tilingRandomClockExternalLargeEvent t m cutoff band x) := by
  rw [show tilingRandomClockExternalLargeEvent t m cutoff band x =
        ⋃ n : ℕ,
          {s | pathTruncatedLevelTime m band.oldRank cutoff s = n} ∩
            {s | band.externalThreshold ≤
              pathPhaseFilteredExternalLocalTime t band.orientation
                band.vertexPhase s n x} by
    ext s
    simp only [tilingRandomClockExternalLargeEvent, Set.mem_ofPred_eq,
      Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hs
      exact ⟨pathTruncatedLevelTime m band.oldRank cutoff s, rfl, hs⟩
    · rintro ⟨n, hn, hs⟩
      simpa only [hn] using hs]
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_pathTruncatedLevelTime_eq m band.oldRank cutoff n).inter
      (measurableSet_le measurable_const
        (measurable_pathPhaseFilteredExternalLocalTime t band.orientation
          band.vertexPhase n x))

/-! ## The deterministic lazy-cap seam -/

/-- All non-external local time at one prefix is capped simultaneously. -/
def TilingLazyGoodAt (t : DominoTiling) (o : LazyDecomposition.Orientation)
    (n cap : ℕ) (s : WalkPath) : Prop :=
  ∀ x, pathPhasedBoundaryLocalTime o s n x +
    pathPhasedLazyLocalTime t o s n x ≤ cap

def TilingLazyOverflowAt (t : DominoTiling) (o : LazyDecomposition.Orientation)
    (n cap : ℕ) (s : WalkPath) : Prop :=
  ∃ x, cap < pathPhasedBoundaryLocalTime o s n x +
    pathPhasedLazyLocalTime t o s n x

theorem tilingLazyOverflowAt_iff_not_good
    (t : DominoTiling) (o : LazyDecomposition.Orientation)
    (n cap : ℕ) (s : WalkPath) :
    TilingLazyOverflowAt t o n cap s ↔ ¬TilingLazyGoodAt t o n cap s := by
  simp only [TilingLazyOverflowAt, TilingLazyGoodAt, not_forall, not_le]

def tilingStoppedLazyOverflowEvent (t : DominoTiling)
    (o : LazyDecomposition.Orientation)
    (m k cap : ℕ) : Set WalkPath :=
  ⋃ n, thresholdCreationSet m k n ∩
    {s | TilingLazyOverflowAt t o n cap s}

theorem measurableSet_tilingLazyOverflowAt
    (t : DominoTiling) (o : LazyDecomposition.Orientation) (n cap : ℕ) :
    MeasurableSet {s : WalkPath | TilingLazyOverflowAt t o n cap s} := by
  rw [show {s : WalkPath | TilingLazyOverflowAt t o n cap s} =
      ⋃ x : Point, {s | cap < pathPhasedBoundaryLocalTime o s n x +
        pathPhasedLazyLocalTime t o s n x} by
    ext s
    simp [TilingLazyOverflowAt]]
  exact MeasurableSet.iUnion fun x ↦ measurableSet_lt measurable_const
    ((measurable_pathPhasedBoundaryLocalTime o n x).add
      (measurable_pathPhasedLazyLocalTime t o n x))

theorem measurableSet_tilingStoppedLazyOverflowEvent
    (t : DominoTiling) (o : LazyDecomposition.Orientation) (m k cap : ℕ) :
    MeasurableSet (tilingStoppedLazyOverflowEvent t o m k cap) := by
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_thresholdCreationSet m k n).inter
      (measurableSet_tilingLazyOverflowAt t o n cap)

theorem tilingStoppedLazyOverflowEvent_subset_thresholdReachStage
    (t : DominoTiling) (o : LazyDecomposition.Orientation) (m k cap : ℕ) :
    tilingStoppedLazyOverflowEvent t o m k cap ⊆ thresholdReachStage m k := by
  rw [thresholdReachStage_eq_iUnion_creation]
  intro s hs
  rw [tilingStoppedLazyOverflowEvent] at hs
  obtain ⟨n, hnCreation, _hnOverflow⟩ := Set.mem_iUnion.mp hs
  exact Set.mem_iUnion.mpr ⟨n, hnCreation⟩

/-- Trace piece used by the state-dependent insertion product law. -/
def tilingLazyOverflowTracePiece (t : DominoTiling)
    (o : LazyDecomposition.Orientation)
    (m k cap : ℕ) (z : FavoriteTilingTraceCode t) : Set WalkPath :=
  favoriteTilingStagePiece t m k
    (tilingStoppedLazyOverflowEvent t o m k cap) z

theorem iUnion_tilingLazyOverflowTracePiece
    (t : DominoTiling) (o : LazyDecomposition.Orientation) (m k cap : ℕ) :
    (⋃ z : FavoriteTilingTraceCode t,
      tilingLazyOverflowTracePiece t o m k cap z) =
      tilingStoppedLazyOverflowEvent t o m k cap := by
  exact iUnion_favoriteTilingStagePiece t m k
    (tilingStoppedLazyOverflowEvent_subset_thresholdReachStage t o m k cap)

/-- The six-tiling lazy exception still has two temporal phases and three
possible preceding creation ranks. -/
def tilingLazyOverflowExceptionalEvent
    (t : DominoTiling) (m cap : ℕ) : Set WalkPath :=
  (⋃ k : Fin 3,
      tilingStoppedLazyOverflowEvent t .even m (k + 1) cap) ∪
    ⋃ k : Fin 3,
      tilingStoppedLazyOverflowEvent t .shifted m (k + 1) cap

def tilingLazyGoodPart (t : DominoTiling) (gapEvent : Set WalkPath)
    (m cap : ℕ) : Set WalkPath :=
  gapEvent \ tilingLazyOverflowExceptionalEvent t m cap

theorem measurableSet_tilingLazyOverflowExceptionalEvent
    (t : DominoTiling) (m cap : ℕ) :
    MeasurableSet (tilingLazyOverflowExceptionalEvent t m cap) := by
  exact (MeasurableSet.iUnion fun k : Fin 3 ↦
    measurableSet_tilingStoppedLazyOverflowEvent t .even m (k + 1) cap).union
      (MeasurableSet.iUnion fun k : Fin 3 ↦
        measurableSet_tilingStoppedLazyOverflowEvent t .shifted m (k + 1) cap)

/-- On the good branch the all-tiling non-external contribution is capped
at every point at the genuine old threshold clock. -/
theorem tiling_lazy_cap_at_creation_of_mem_good
    {t : DominoTiling} {gapEvent : Set WalkPath} {m cap : ℕ}
    {o : LazyDecomposition.Orientation} {k n : ℕ} {s : WalkPath}
    (hs : s ∈ tilingLazyGoodPart t gapEvent m cap)
    (hkpos : 0 < k) (hkle : k ≤ 3)
    (hcreation : ThresholdCreation s m k n) :
    TilingLazyGoodAt t o n cap s := by
  intro x
  by_contra hcap
  have hoverflowAt : TilingLazyOverflowAt t o n cap s :=
    ⟨x, Nat.lt_of_not_ge hcap⟩
  have hstop : s ∈ tilingStoppedLazyOverflowEvent t o m k cap := by
    exact Set.mem_iUnion.mpr ⟨n, hcreation, hoverflowAt⟩
  let j : Fin 3 := ⟨k - 1, by omega⟩
  have hj : (j : ℕ) + 1 = k := by
    dsimp only [j]
    omega
  apply hs.2
  cases ho : o with
  | even =>
      left
      have hstop' : s ∈ tilingStoppedLazyOverflowEvent t .even m k cap := by
        simpa only [ho] using hstop
      exact Set.mem_iUnion.mpr ⟨j, by simpa only [hj] using hstop'⟩
  | shifted =>
      right
      have hstop' : s ∈ tilingStoppedLazyOverflowEvent t .shifted m k cap := by
        simpa only [ho] using hstop
      exact Set.mem_iUnion.mpr ⟨j, by simpa only [hj] using hstop'⟩

/-- On the good branch the all-tiling non-external contribution is capped
at every point at the genuine old threshold clock. -/
theorem tiling_lazy_cap_at_randomClock_of_mem_good
    {t : DominoTiling} {gapEvent : Set WalkPath} {m cutoff cap : ℕ}
    {band : RandomClockBand} {s : WalkPath}
    (hs : s ∈ tilingLazyGoodPart t gapEvent m cap)
    (hcreation : ThresholdCreation s m band.oldRank
      (pathTruncatedLevelTime m band.oldRank cutoff s)) :
    TilingLazyGoodAt t band.orientation
      (pathTruncatedLevelTime m band.oldRank cutoff s) cap s := by
  have hrank : band.oldRank ≤ 3 := by
    exact Nat.lt_succ_iff.mp
      (band.rank_lt.trans_le band.newRank_le_four)
  exact tiling_lazy_cap_at_creation_of_mem_good hs band.oldRank_pos hrank hcreation

/-- A point meeting the actual-local-time, lazy-cap, favorite-separation and
shell-band conditions belongs to the genuine all-tiling candidate set. -/
theorem mem_tilingRandomClockBandSites_of_lazy_cap
    {t : DominoTiling} {m cutoff : ℕ} {s : WalkPath}
    {band : RandomClockBand} {x : Point}
    (hvisited : x ∈ pathPhaseFilteredExternalVisitedSites t band.orientation
      band.vertexPhase s
        (pathTruncatedLevelTime m band.oldRank cutoff s))
    (hexternal : band.externalThreshold ≤
      pathPhaseFilteredExternalLocalTime t band.orientation band.vertexPhase s
        (pathTruncatedLevelTime m band.oldRank cutoff s) x)
    (hsep : ∀ y ∈ favoriteSites s
        (pathTruncatedLevelTime m band.oldRank cutoff s),
      x ≠ y ∧ ¬Tilings.sameDomino t x y)
    (hshell : deficitShellLabel
        (tilingRandomClockTotalLocalTime m cutoff band) m (shellWidth48 m)
    s x < shellCount48 m band.beta) :
    x ∈ tilingRandomClockBandSites t m cutoff s band := by
  classical
  rw [tilingRandomClockBandSites, mem_boundedCandidates]
  refine ⟨?_, hshell⟩
  rw [Finset.mem_filter]
  refine ⟨?_, ?_, ?_⟩
  · exact hvisited
  · exact hexternal
  · rw [tilingRandomClockDistinguishedSites, favoriteTilingDominoSites,
      Finset.mem_union, not_or]
    refine ⟨?_, ?_⟩
    · intro hx
      exact (hsep x hx).1 rfl
    · intro hx
      obtain ⟨y, hy, hpartner⟩ := Finset.mem_image.mp hx
      have hxy : tilingPartner t x = y := by
        rw [← hpartner, tilingPartner_partner]
      exact (hsep y hy).2 ((sameDomino_iff_partner_eq t x y).2 hxy)

/-! ## Extraction interface -/

/-- The deterministic path seam for arbitrary tilings.  It contains beta,
rank, phase and scale data but no physical creation times. -/
def TilingRandomClockExtraction
    (t : DominoTiling) (gapEvent : Set WalkPath) (m cutoff : ℕ)
    (bands : Finset RandomClockBand) : Prop :=
  PathGapWitness gapEvent bands
    (tilingRandomClockBandSites t m cutoff)
    (fun band ↦ candidateBudget48 m band.beta)
    (RandomClockPairRealizes m cutoff)

/-- Extraction restricted to the genuine all-tiling lazy-good branch. -/
def TilingLazyGoodRandomClockExtraction
    (t : DominoTiling) (gapEvent : Set WalkPath) (m cutoff cap : ℕ)
    (bands : Finset RandomClockBand) : Prop :=
  TilingRandomClockExtraction t (tilingLazyGoodPart t gapEvent m cap)
    m cutoff bands

/-- Concrete constructor for the all-tiling extraction.  These are exactly
the deterministic facts supplied by the failed-pair beta-band
decomposition: the next favorite is a base of the selected tiling, separated
from the old favorite dominoes, lies in the displayed deficit shell, and has
enough old local time after the lazy cap is removed. -/
theorem tilingLazyGoodRandomClockExtraction_of_band_realization
    {t : DominoTiling} {gapEvent : Set WalkPath} {m cutoff cap : ℕ}
    {bands : Finset RandomClockBand}
    (hselect : ∀ s ∈ tilingLazyGoodPart t gapEvent m cap,
      ∃ band ∈ bands, ∃ x : Point,
        RandomClockPairRealizes m cutoff s band x ∧
        x ∈ pathPhaseFilteredExternalVisitedSites t band.orientation
          band.vertexPhase s
            (pathTruncatedLevelTime m band.oldRank cutoff s) ∧
        band.externalThreshold ≤
          pathPhaseFilteredExternalLocalTime t band.orientation
            band.vertexPhase s
              (pathTruncatedLevelTime m band.oldRank cutoff s) x ∧
        (∀ y ∈ favoriteSites s
            (pathTruncatedLevelTime m band.oldRank cutoff s),
          x ≠ y ∧ ¬Tilings.sameDomino t x y) ∧
        deficitShellLabel
            (tilingRandomClockTotalLocalTime m cutoff band)
            m (shellWidth48 m) s x < shellCount48 m band.beta) :
    TilingLazyGoodRandomClockExtraction t gapEvent m cutoff cap bands := by
  intro s hs _hnoOverflow
  obtain ⟨band, hband, x, hrealizes, hvisited, hexternal,
      hsep, hshell⟩ := hselect s hs
  refine ⟨band, hband, x,
    mem_tilingRandomClockBandSites_of_lazy_cap hvisited hexternal
      hsep hshell, hrealizes⟩

/-- This is the exact screened event passed to the all-tiling stopped product
law. -/
def tilingRandomClockCandidateOverflow
    (t : DominoTiling) (m cutoff : ℕ)
    (bands : Finset RandomClockBand) : Set WalkPath :=
  candidateOverflow bands (tilingRandomClockBandSites t m cutoff)
    (fun band ↦ candidateBudget48 m band.beta)

/-! ## Stopped candidate slots and geometric returns -/

def tilingRandomClockSlotCandidatePoint
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (slot : ℕ) (omega : StepPath) : Point :=
  (finsetSlot
    (tilingRandomClockBandSites t m cutoff (trajectory omega) band) slot).getD 0

/-- Pure finite-prefix form of the all-tiling candidate Finset. -/
noncomputable def tilingPrefixBandSites
    (t : DominoTiling) (o : LazyDecomposition.Orientation)
    (phase : Bool)
    (externalThreshold m : ℕ) (beta : ℝ) {n : ℕ}
    (u : Fin (n + 1) → Point) : Finset Point := by
  classical
  exact boundedCandidates
    ((phasedExternalVertexVisitedSites t o
      (externalVertexPhaseOfBool phase) (finitePathList u)).filter fun x ↦
      externalThreshold ≤ phasedExternalVertexLocalTime t o
          (externalVertexPhaseOfBool phase) (finitePathList u) x ∧
        x ∉ favoritePrefix u ∪ (favoritePrefix u).image (tilingPartner t))
    (fun x ↦ (m - localTimePrefix u x) / shellWidth48 m)
    (shellCount48 m beta)

theorem tilingRandomClockBandSites_eq_prefix_of_clock
    {t : DominoTiling} {m cutoff n : ℕ} {s : WalkPath}
    {band : RandomClockBand}
    (hn : pathTruncatedLevelTime m band.oldRank cutoff s = n) :
    tilingRandomClockBandSites t m cutoff s band =
      tilingPrefixBandSites t band.orientation band.vertexPhase band.externalThreshold
        m band.beta (pathPrefix s n) := by
  classical
  subst n
  ext x
  simp [tilingRandomClockBandSites, tilingPrefixBandSites,
    tilingRandomClockExternalLargeEvent, tilingRandomClockVisitedSites,
    tilingRandomClockDistinguishedSites, tilingRandomClockTotalLocalTime,
    favoriteTilingDominoSites, pathPhaseFilteredExternalVisitedSites,
    pathPhaseFilteredExternalLocalTime, localTime, favoriteSites]

theorem measurable_fixed_tilingPrefixBandSites
    (t : DominoTiling) (n m : ℕ) (band : RandomClockBand) :
    Measurable fun s : WalkPath ↦
      tilingPrefixBandSites t band.orientation band.vertexPhase
        band.externalThreshold
        m band.beta (pathPrefix s n) := by
  exact (measurable_of_countable
    (tilingPrefixBandSites t band.orientation band.vertexPhase band.externalThreshold
      m band.beta)).comp (measurable_pathPrefix n)

theorem measurableSet_tilingRandomClockBandSlot_eq
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (slot : ℕ) (x : Point) :
    MeasurableSet {s : WalkPath |
      finsetSlot (tilingRandomClockBandSites t m cutoff s band) slot =
        some x} := by
  have heq :
      {s : WalkPath |
          finsetSlot (tilingRandomClockBandSites t m cutoff s band) slot =
            some x} =
        ⋃ n : ℕ,
          {s | pathTruncatedLevelTime m band.oldRank cutoff s = n} ∩
            {s | finsetSlot
              (tilingPrefixBandSites t band.orientation
                band.vertexPhase band.externalThreshold m band.beta
                  (pathPrefix s n)) slot =
                some x} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hs
      refine ⟨pathTruncatedLevelTime m band.oldRank cutoff s, rfl, ?_⟩
      simpa only [tilingRandomClockBandSites_eq_prefix_of_clock rfl] using hs
    · rintro ⟨n, hn, hs⟩
      simpa only [tilingRandomClockBandSites_eq_prefix_of_clock hn] using hs
  rw [heq]
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_pathTruncatedLevelTime_eq m band.oldRank cutoff n).inter
      ((measurable_fixed_tilingPrefixBandSites t n m band)
        (Set.to_countable {S : Finset Point |
          finsetSlot S slot = some x}).measurableSet)

lemma tilingRandomClockSlotCandidatePoint_eq_of_slot
    {t : DominoTiling} {m cutoff : ℕ} {band : RandomClockBand}
    {slot : ℕ} {omega : StepPath} {x : Point}
    (hslot : finsetSlot
      (tilingRandomClockBandSites t m cutoff (trajectory omega) band) slot =
        some x) :
    tilingRandomClockSlotCandidatePoint t m cutoff band slot omega = x := by
  simp [tilingRandomClockSlotCandidatePoint, hslot]

/-- The remaining measurability obligation for the state-dependent
candidate enumeration.  Both fields are finite-prefix statements; keeping
them together prevents a probability theorem from silently assuming a
non-observable future favorite. -/
structure TilingRandomClockCandidateMeasurability
    (t : DominoTiling) (m cutoff : ℕ) : Prop where
  slot_fiber : ∀ band slot x, MeasurableSet {s : WalkPath |
    finsetSlot (tilingRandomClockBandSites t m cutoff s band) slot = some x}
  point_observable : ∀ band slot x,
    IsMeasurableAtStopping
      (truncatedLevelTime m band.oldRank cutoff)
      {omega | tilingRandomClockSlotCandidatePoint
        t m cutoff band slot omega = x}

theorem tilingRandomClockSlotCandidatePoint_observable
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (slot : ℕ) (x : Point) :
    IsMeasurableAtStopping
      (truncatedLevelTime m band.oldRank cutoff)
      {omega | tilingRandomClockSlotCandidatePoint
        t m cutoff band slot omega = x} := by
  intro n
  let deterministicPoint : StepPath → Point := fun omega ↦
    (finsetSlot
      (tilingPrefixBandSites t band.orientation band.vertexPhase
        band.externalThreshold
        m band.beta (trajectoryPrefix (stepPrefix n omega))) slot).getD 0
  have hdetMeas : Measurable[incrementFiltration n] deterministicPoint := by
    rw [incrementFiltration_apply]
    exact (measurable_of_countable
      (fun u : Fin n → Direction ↦
        (finsetSlot
          (tilingPrefixBandSites t band.orientation band.vertexPhase
            band.externalThreshold
            m band.beta (trajectoryPrefix u)) slot).getD 0)).comp
        (comap_measurable (stepPrefix n))
  have heq :
      {omega | tilingRandomClockSlotCandidatePoint
          t m cutoff band slot omega = x} ∩
          {omega | truncatedLevelTime m band.oldRank cutoff omega = n} =
        {omega | deterministicPoint omega = x} ∩
          {omega | truncatedLevelTime m band.oldRank cutoff omega = n} := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hpoint, hclock⟩
      refine ⟨?_, hclock⟩
      have hclock' : pathTruncatedLevelTime m band.oldRank cutoff
          (trajectory omega) = n := by
        simpa only [pathTruncatedLevelTime_trajectory] using hclock
      simpa only [tilingRandomClockSlotCandidatePoint,
        tilingRandomClockBandSites_eq_prefix_of_clock hclock',
        deterministicPoint, trajectoryPrefix_stepPrefix] using hpoint
    · rintro ⟨hpoint, hclock⟩
      refine ⟨?_, hclock⟩
      have hclock' : pathTruncatedLevelTime m band.oldRank cutoff
          (trajectory omega) = n := by
        simpa only [pathTruncatedLevelTime_trajectory] using hclock
      simpa only [tilingRandomClockSlotCandidatePoint,
        tilingRandomClockBandSites_eq_prefix_of_clock hclock',
        deterministicPoint, trajectoryPrefix_stepPrefix] using hpoint
  rw [heq]
  exact (measurableSet_eq_fun hdetMeas measurable_const).inter
    ((isFiniteStoppingTime_truncatedLevelTime m band.oldRank cutoff).measurableSet_eq n)

theorem tilingRandomClockCandidateMeasurability_closed
    (t : DominoTiling) (m cutoff : ℕ) :
    TilingRandomClockCandidateMeasurability t m cutoff where
  slot_fiber := measurableSet_tilingRandomClockBandSlot_eq t m cutoff
  point_observable :=
    tilingRandomClockSlotCandidatePoint_observable t m cutoff

theorem measurableSet_tilingRandomClockBandSlotSuccess
    {t : DominoTiling} {m cutoff : ℕ}
    (hmeas : TilingRandomClockCandidateMeasurability t m cutoff)
    (band : RandomClockBand) (slot : ℕ) :
    MeasurableSet
      (slotSuccessEvent (tilingRandomClockBandSites t m cutoff)
        (RandomClockPairRealizes m cutoff) band slot) := by
  have heq :
      slotSuccessEvent (tilingRandomClockBandSites t m cutoff)
          (RandomClockPairRealizes m cutoff) band slot =
        ⋃ x : Point,
          {s | finsetSlot
            (tilingRandomClockBandSites t m cutoff s band) slot = some x} ∩
            {s | RandomClockPairRealizes m cutoff s band x} := by
    ext s
    simp only [slotSuccessEvent, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_inter_iff]
  rw [heq]
  exact MeasurableSet.iUnion fun x ↦
    (hmeas.slot_fiber band slot x).inter
      (measurableSet_randomClockPairRealizes m cutoff band x)

def tilingRandomClockBandSpatialGuard
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (slot : ℕ) : Set StepPath :=
  {omega | gapScaleOf m
      (trajectory omega
        (truncatedLevelTime m band.oldRank cutoff omega))
      (tilingRandomClockSlotCandidatePoint t m cutoff band slot omega) =
        band.scale}

theorem tilingRandomClockBandSpatialGuard_observable
    {t : DominoTiling} {m cutoff : ℕ}
    (hmeas : TilingRandomClockCandidateMeasurability t m cutoff)
    (band : RandomClockBand) (slot : ℕ) :
    IsMeasurableAtStopping
      (truncatedLevelTime m band.oldRank cutoff)
      (tilingRandomClockBandSpatialGuard t m cutoff band slot) := by
  have hold : ∀ x, IsMeasurableAtStopping
      (truncatedLevelTime m band.oldRank cutoff)
      {omega | trajectory omega
        (truncatedLevelTime m band.oldRank cutoff omega) = x} := by
    intro x
    simpa only [stoppedLocation] using
      (stoppedLocation_fiber_observable
        (isFiniteStoppingTime_truncatedLevelTime m band.oldRank cutoff) x)
  simpa only [tilingRandomClockBandSpatialGuard] using
    (isMeasurableAtStopping_binary_fiber hold
      (hmeas.point_observable band slot)
      (fun old candidate ↦ gapScaleOf m old candidate) band.scale)

/-- The strong-Markov return witness is independent of the deletion rule;
only stopped-past slot observability changes. -/
noncomputable def tilingRandomClockBandSlotScheduleWitness
    {t : DominoTiling} {m cutoff : ℕ}
    (hmeas : TilingRandomClockCandidateMeasurability t m cutoff)
    (band : RandomClockBand) (slot : ℕ) :
    GuardedStoppedCandidateScheduleWitness
      (slotSuccessEvent (tilingRandomClockBandSites t m cutoff)
        (RandomClockPairRealizes m cutoff) band slot)
      (cutoff + 1) band.returns
      (HLOZGapMeshEscape.meshPointEscapeChance m band.scale) where
  past := truncatedLevelTime m band.oldRank cutoff
  candidate := tilingRandomClockSlotCandidatePoint t m cutoff band slot
  oldFavorite := fun omega ↦ trajectory omega
    (truncatedLevelTime m band.oldRank cutoff omega)
  past_isStopping :=
    isFiniteStoppingTime_truncatedLevelTime m band.oldRank cutoff
  past_lt_deadline := fun omega ↦
    Nat.lt_succ_of_le (truncatedLevelTime_le m band.oldRank cutoff omega)
  candidate_observable := hmeas.point_observable band slot
  oldFavorite_observable := by
    intro x
    simpa only [stoppedLocation] using
      (stoppedLocation_fiber_observable
        (isFiniteStoppingTime_truncatedLevelTime m band.oldRank cutoff) x)
  guard := tilingRandomClockBandSpatialGuard t m cutoff band slot
  guard_observable :=
    tilingRandomClockBandSpatialGuard_observable hmeas band slot
  event_guard := by
    intro omega homega
    obtain ⟨x, hslot, hrealizes⟩ := homega
    have hcandidate :
        tilingRandomClockSlotCandidatePoint t m cutoff band slot omega = x :=
      tilingRandomClockSlotCandidatePoint_eq_of_slot hslot
    change gapScaleOf m
      (trajectory omega
        (truncatedLevelTime m band.oldRank cutoff omega))
      (tilingRandomClockSlotCandidatePoint t m cutoff band slot omega) =
        band.scale
    rw [hcandidate]
    have hx : x = trajectory omega
        (truncatedLevelTime m band.newRank cutoff omega) := by
      simpa only [RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory] using hrealizes.1.2.2.2.2.2.2
    rw [hx]
    simpa only [RandomClockPairRealizes,
      pathTruncatedLevelTime_trajectory] using hrealizes.1.2.2.2.2.1
  event_distinct := by
    intro omega homega
    obtain ⟨x, hslot, hrealizes⟩ := homega
    have hcandidate :
        tilingRandomClockSlotCandidatePoint t m cutoff band slot omega = x :=
      tilingRandomClockSlotCandidatePoint_eq_of_slot hslot
    change trajectory omega
      (truncatedLevelTime m band.oldRank cutoff omega) ≠
        tilingRandomClockSlotCandidatePoint t m cutoff band slot omega
    rw [hcandidate]
    have hx : x = trajectory omega
        (truncatedLevelTime m band.newRank cutoff omega) := by
      simpa only [RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory] using hrealizes.1.2.2.2.2.2.2
    rw [hx]
    exact creation_locations_ne band.oldRank_pos band.newRank_pos band.rank_lt
      (by simpa only [RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory] using hrealizes.1.1)
      (by simpa only [RandomClockPairRealizes,
        pathTruncatedLevelTime_trajectory] using hrealizes.1.2.1)
  event_schedule := by
    intro omega homega
    obtain ⟨x, hslot, hrealizes⟩ := homega
    let nOld := truncatedLevelTime m band.oldRank cutoff omega
    let nNew := truncatedLevelTime m band.newRank cutoff omega
    let nTerminal := truncatedLevelTime m 4 cutoff omega
    have hold : ThresholdCreation (trajectory omega) m band.oldRank nOld := by
      simpa only [RandomClockPairRealizes, pathTruncatedLevelTime_trajectory,
        nOld, nNew, nTerminal] using hrealizes.1.1
    have hnew : ThresholdCreation (trajectory omega) m band.newRank nNew := by
      simpa only [RandomClockPairRealizes, pathTruncatedLevelTime_trajectory,
        nOld, nNew, nTerminal] using hrealizes.1.2.1
    have hnext : thresholdCount (trajectory omega) nTerminal (m + 1) = 0 := by
      simpa only [RandomClockPairRealizes, pathTruncatedLevelTime_trajectory,
        nOld, nNew, nTerminal] using hrealizes.1.2.2.1
    have hnewTerminal : nNew ≤ nTerminal := by
      simpa only [RandomClockPairRealizes, pathTruncatedLevelTime_trajectory,
        nOld, nNew, nTerminal] using hrealizes.1.2.2.2.1
    have hcandidate :
        tilingRandomClockSlotCandidatePoint t m cutoff band slot omega = x :=
      tilingRandomClockSlotCandidatePoint_eq_of_slot hslot
    have hx : x = trajectory omega nNew := by
      simpa only [RandomClockPairRealizes, pathTruncatedLevelTime_trajectory,
        nOld, nNew, nTerminal] using hrealizes.1.2.2.2.2.2.2
    have hreturn : localTime (trajectory omega) nOld x +
        (band.returns + 1) ≤ m := by
      simpa only [RandomClockPairRealizes, pathTruncatedLevelTime_trajectory,
        nOld, nNew, nTerminal] using hrealizes.2
    have hthreshold : m ≤ localTime (trajectory omega) nNew x := by
      rw [hx]
      exact (mem_thresholdSites (trajectory omega) nNew m
        (trajectory omega nNew)).mp
          (position_mem_thresholdSites_of_creation band.newRank_pos hnew) |>.2
    have holdNew : nOld < nNew :=
      creation_time_lt band.oldRank_pos band.newRank_pos band.rank_lt hold hnew
    have hgain : localTime (trajectory omega) nOld
        (tilingRandomClockSlotCandidatePoint t m cutoff band slot omega) +
          (band.returns + 1) ≤
        localTime (trajectory omega) nNew
          (tilingRandomClockSlotCandidatePoint t m cutoff band slot omega) := by
      rw [hcandidate]
      exact hreturn.trans hthreshold
    have hschedule : HasStrictVisitSchedule
        (truncatedLevelTime m band.oldRank cutoff)
        (tilingRandomClockSlotCandidatePoint t m cutoff band slot)
        (nNew + 1) (band.returns + 1) omega := by
      apply hasStrictVisitSchedule_of_localTime_gain
        (past := truncatedLevelTime m band.oldRank cutoff)
        (target := tilingRandomClockSlotCandidatePoint t m cutoff band slot)
      · simpa only [nOld] using Nat.lt_succ_of_lt holdNew
      · simpa only [Nat.add_sub_cancel] using hgain
    obtain ⟨times, hmono, hafter, hbeforeNew, hvisit⟩ := hschedule
    refine ⟨times, hmono, hafter, ?_, hvisit, ?_⟩
    · intro i
      exact (hbeforeNew i).trans_le
        (Nat.succ_le_succ (truncatedLevelTime_le m band.newRank cutoff omega))
    · intro q hpast hq
      have hlastNew :
          times ⟨band.returns, Nat.lt_succ_self band.returns⟩ ≤ nNew :=
        Nat.lt_succ_iff.mp (hbeforeNew _)
      have havoid := no_oldCreation_visit_of_no_next_level
        band.oldRank_pos hold hnext
      exact havoid q (by simpa only [nOld] using hpast)
        ((hq.trans hlastNew).trans hnewTerminal)
  guard_lower := by
    intro omega hguard hdistinct
    exact HLOZGapMeshEscape.meshPointEscapeChance_le_pointBeforeReturnProbability
      band.scale_proper hguard hdistinct

theorem measure_tilingRandomClockBandSlotSuccess_le_geometric
    {t : DominoTiling} {m cutoff : ℕ}
    (hmeas : TilingRandomClockCandidateMeasurability t m cutoff)
    (band : RandomClockBand) (slot : ℕ) :
    simpleRandomWalk
        (slotSuccessEvent (tilingRandomClockBandSites t m cutoff)
          (RandomClockPairRealizes m cutoff) band slot) ≤
      Gap.geometricReturnCost
        (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
        band.returns := by
  exact measure_le_geometricReturnCost_of_guardedStoppedCandidateSchedule
    (measurableSet_tilingRandomClockBandSlotSuccess hmeas band slot)
    (HLOZGapMeshEscape.meshPointEscapeChance_pos m band.scale).le
    (HLOZGapMeshEscape.meshPointEscapeChance_le_one m band.scale)
    (tilingRandomClockBandSlotScheduleWitness hmeas band slot)

/-! ## Finite all-tiling screen -/

theorem measure_tilingRandomClockExtraction_le
    {t : DominoTiling} {gapEvent : Set WalkPath} {m cutoff : ℕ}
    {bands : Finset RandomClockBand}
    (hmeas : TilingRandomClockCandidateMeasurability t m cutoff)
    (hextract : TilingRandomClockExtraction t gapEvent m cutoff bands) :
    simpleRandomWalk gapEvent ≤
      simpleRandomWalk (tilingRandomClockCandidateOverflow t m cutoff bands) +
        ∑ band ∈ bands,
          (candidateBudget48 m band.beta : ℝ≥0∞) *
            Gap.geometricReturnCost
              (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
              band.returns := by
  let sites := tilingRandomClockBandSites t m cutoff
  let budget : RandomClockBand → ℕ := fun band ↦
    candidateBudget48 m band.beta
  let realizes := RandomClockPairRealizes m cutoff
  let overflow := candidateOverflow bands sites budget
  let screened := gapEvent \ overflow
  have hsplit : gapEvent ⊆ overflow ∪ screened := by
    intro s hs
    by_cases hoverflow : s ∈ overflow
    · exact Or.inl hoverflow
    · exact Or.inr ⟨hs, hoverflow⟩
  calc
    simpleRandomWalk gapEvent ≤ simpleRandomWalk (overflow ∪ screened) :=
      measure_mono hsplit
    _ ≤ simpleRandomWalk overflow + simpleRandomWalk screened :=
      measure_union_le _ _
    _ ≤ simpleRandomWalk overflow +
        ∑ band ∈ bands, (budget band : ℝ≥0∞) *
          Gap.geometricReturnCost
            (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
            band.returns := by
      gcongr
      exact Gap.measure_gapEvent_le_geometric_sum simpleRandomWalk screened bands
        (fun band ↦ Finset.range (budget band))
        (slotSuccessEvent sites realizes) budget
        (fun band ↦ HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
        RandomClockBand.returns
        (by
          dsimp only [screened, overflow]
          exact gapEvent_diff_overflow_covered_by_slots
            gapEvent bands sites budget realizes hextract)
        (range_candidateCountBound bands budget)
        (by
          intro band _hband slot _hslot
          exact measure_tilingRandomClockBandSlotSuccess_le_geometric
            hmeas band slot)
    _ = simpleRandomWalk
          (tilingRandomClockCandidateOverflow t m cutoff bands) +
        ∑ band ∈ bands,
          (candidateBudget48 m band.beta : ℝ≥0∞) *
            Gap.geometricReturnCost
              (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
              band.returns := rfl

theorem measure_tilingRandomClockExtraction_le_closed
    {t : DominoTiling} {gapEvent : Set WalkPath} {m cutoff : ℕ}
    {bands : Finset RandomClockBand}
    (hextract : TilingRandomClockExtraction t gapEvent m cutoff bands) :
    simpleRandomWalk gapEvent ≤
      simpleRandomWalk (tilingRandomClockCandidateOverflow t m cutoff bands) +
        ∑ band ∈ bands,
          (candidateBudget48 m band.beta : ℝ≥0∞) *
            Gap.geometricReturnCost
              (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
              band.returns :=
  measure_tilingRandomClockExtraction_le
    (tilingRandomClockCandidateMeasurability_closed t m cutoff) hextract

/-- Complete all-tiling lazy-bad/lazy-good split.  The remaining two
probability terms are now precisely the events controlled by the tiling
trace product law and dynamic Proposition 4.8. -/
theorem measure_gapEvent_le_tilingLazyRandomClockScreen
    (t : DominoTiling) (gapEvent : Set WalkPath) (m cutoff cap : ℕ)
    (bands : Finset RandomClockBand)
    (hextract : TilingLazyGoodRandomClockExtraction
      t gapEvent m cutoff cap bands) :
    simpleRandomWalk gapEvent ≤
      simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m cap) +
        (simpleRandomWalk
            (tilingRandomClockCandidateOverflow t m cutoff bands) +
          ∑ band ∈ bands,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) := by
  have hsplit : gapEvent ⊆
      tilingLazyOverflowExceptionalEvent t m cap ∪
        tilingLazyGoodPart t gapEvent m cap := by
    intro s hs
    by_cases hoverflow : s ∈ tilingLazyOverflowExceptionalEvent t m cap
    · exact Or.inl hoverflow
    · exact Or.inr ⟨hs, hoverflow⟩
  calc
    simpleRandomWalk gapEvent ≤
        simpleRandomWalk
          (tilingLazyOverflowExceptionalEvent t m cap ∪
            tilingLazyGoodPart t gapEvent m cap) := measure_mono hsplit
    _ ≤ simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m cap) +
          simpleRandomWalk (tilingLazyGoodPart t gapEvent m cap) :=
      measure_union_le _ _
    _ ≤ simpleRandomWalk (tilingLazyOverflowExceptionalEvent t m cap) +
        (simpleRandomWalk
            (tilingRandomClockCandidateOverflow t m cutoff bands) +
          ∑ band ∈ bands,
            (candidateBudget48 m band.beta : ℝ≥0∞) *
              Gap.geometricReturnCost
                (HLOZGapMeshEscape.meshPointEscapeChance m band.scale)
                band.returns) := by
      gcongr
      exact measure_tilingRandomClockExtraction_le_closed hextract

end

end Erdos1165.HLOZTilingGapRandomClockScreen
