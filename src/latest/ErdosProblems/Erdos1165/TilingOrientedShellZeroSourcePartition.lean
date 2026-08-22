/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedExternalLocalTime
import ErdosProblems.Erdos1165.TilingShellZeroSourcePartition
import ErdosProblems.Erdos1165.TilingTypedFavoriteTrace

/-!
# Endpoint-oriented shell-zero source atoms

The retained external coordinate in the HLOZ source screen belongs to the
endpoint chain of one temporal pairing.  This module therefore adds the
pairing orientation to `Theta` and to the complete stopped trace code.  The
trace code is typed: it carries its spatial start, a statefully valid retained
word, the boundary tail, and the creation-favorite data.
-/

open MeasureTheory Set

namespace Erdos1165.TilingOrientedShellZeroSourcePartition

open HLOZPathEvents HLOZShellZeroReplacementWindows
open HLOZSourceOrientedExternalLocalTime
open TilingLazyDecomposition TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber TilingTypedFavoriteTrace
open TilingVariableStoppedTracePartition VariableStoppedTracePartition
open LazyDecomposition PathInsertion SpatialInsertionFiber VariableStoppedFiber
open PreStoppingFiber StoppedInsertion

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- Uniform all-six cut after the raw-to-base fiber loss and the four-way
canonical/opposite-by-orientation split. -/
def orientedSourceCut48 (m : ℕ) : ℕ :=
  HLOZProposition48Candidates.initialBudget48 m / 8

/-- A typed retained word with the physical prefix preceding the selected
temporal pairing.  The prefix is empty for the even pairing and is the
single first step for the shifted pairing.  Making it part of the code is
what lets the stopped cylinder reconstruct the original walk rather than a
spatially translated suffix. -/
structure OrientedTilingTypedExternalWordCode (t : DominoTiling) where
  initial : BoundaryTail
  retainedCount : ℕ
  retained : TilingRetainedWord t
    ((trajectory (extendPrefix (directionVectorOfList initial.1)))
      initial.1.length) retainedCount
  tail : BoundaryTail
  deriving Countable

def OrientedTilingTypedExternalWordCode.start {t : DominoTiling}
    (z : OrientedTilingTypedExternalWordCode t) : Point :=
  trajectory (extendPrefix (directionVectorOfList z.initial.1))
    z.initial.1.length

/-- The complete non-null source trace used by one literal stopped fibre.
Besides the retained word and favorite data it records the exact dominant
`V₂(I₀ ∪ I₁)` support.  This last field is indispensable: it is the
complement of the distinguished coordinates in the finite product, and is
not determined by the retained word or favorite set alone. -/
structure OrientedTypedFavoriteTilingTraceCode (t : DominoTiling) where
  external : OrientedTilingTypedExternalWordCode t
  favorite : TilingCreationFavoriteData
  supportBases : Finset Point
  deriving Countable

/-- Increment list seen by the selected temporal pairing. -/
def orientedIncrementPrefixList (o : Orientation) (n : ℕ) (s : WalkPath) :
    List Direction :=
  match o with
  | .even => incrementPrefixList n (stepsOfWalk s)
  | .shifted => (incrementPrefixList n (stepsOfWalk s)).drop 1

/-- Spatial start of the selected temporal pairing.  The shifted pairing
starts after the first increment.  On the source events below the creation
time is positive; the total definition at time zero is harmless. -/
def orientedInitialPrefix (o : Orientation) (n : ℕ) (s : WalkPath) :
    BoundaryTail :=
  match o with
  | .even => ⟨[], by simp⟩
  | .shifted =>
      ⟨(incrementPrefixList n (stepsOfWalk s)).take 1,
        List.length_take_le _ _⟩

/-- The `V₂` support belonging to one endpoint chain.  A source fibre for
orientation `o` must neither count nor screen bases from the other temporal
endpoint class. -/
def orientedTilingVTwoBases (t : DominoTiling) (o : Orientation)
    (window : Finset ℕ) (s : WalkPath) (n : ℕ) : Finset Point :=
  (tilingVTwoBases t window s n).filter (OrientationCompatible o)

theorem mem_orientedTilingVTwoBases_iff
    (t : DominoTiling) (o : Orientation) (window : Finset ℕ)
    (s : WalkPath) (n : ℕ) (b : Point) :
    b ∈ orientedTilingVTwoBases t o window s n ↔
      b ∈ tilingVTwoBases t window s n ∧ OrientationCompatible o b := by
  rw [orientedTilingVTwoBases, Finset.mem_filter]

/-- Canonical typed external word at a deterministic physical time. -/
def fixedOrientedTypedExternalWordCode (t : DominoTiling) (o : Orientation)
    (n : ℕ) (s : WalkPath) : OrientedTilingTypedExternalWordCode t :=
  let directions := orientedIncrementPrefixList o n s
  let initial := orientedInitialPrefix o n s
  let start := trajectory (extendPrefix (directionVectorOfList initial.1))
    initial.1.length
  let blocks := pairDirectionList directions
  let retained := deletedTilingRetainedWord t start blocks
  { initial := initial
    retainedCount := (deleteTilingBlocks t start blocks).length
    retained := retained
    tail := ⟨unpairedDirectionTail directions,
      unpairedDirectionTail_length_le_one directions⟩ }

/-- Full typed trace at deterministic time `n`. -/
def fixedOrientedTypedFavoriteTraceCode (t : DominoTiling) (o : Orientation)
    (supportWindow : Finset ℕ) (n : ℕ) (s : WalkPath) :
    OrientedTypedFavoriteTilingTraceCode t where
  external := fixedOrientedTypedExternalWordCode t o n s
  favorite := ((favoriteSites s n, (favoriteSites s n).image (tilingBase t)),
    ((fixedOrientedTypedExternalWordCode t o n s).start, s n))
  supportBases := orientedTilingVTwoBases t o supportWindow s n

/-- Full typed trace at the genuine rank-`k` creation clock. -/
def orientedTypedCreationTraceCode (t : DominoTiling) (o : Orientation)
    (m k w : ℕ) (s : WalkPath) : OrientedTypedFavoriteTilingTraceCode t :=
  fixedOrientedTypedFavoriteTraceCode t o (shellZeroSourceTotalWindow m w)
    (creationTimeNat m k s) s

/-- Dominance-filtered endpoint-oriented `Theta`. -/
def orientedTilingThetaBases (t : DominoTiling) (o : Orientation)
    (m w externalLow externalHigh : ℕ) (s : WalkPath) (n : ℕ) :
    Finset Point :=
  (orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m w ∪
        shellZeroReplacementTotalWindow m w) s n).filter fun b ↦
      ¬(externalLow ≤ tilingSourceExternalBaseLocalTime t o s n b ∧
        tilingSourceExternalBaseLocalTime t o s n b < externalHigh)

/-- Endpoint-oriented literal shell-zero source event. -/
def orientedShellZeroSourceEvent (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh cut : ℕ) : Set WalkPath :=
  {s | ReachesThreshold s m k ∧
    let n := creationTimeNat m k s
    tilingDEtaAt t m k w low s n ∧
      orientedTilingThetaBases t o m w externalLow externalHigh s n = ∅ ∧
      cut < (orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) s n).card}

/-- A preliminary rank stage intersected with the exact oriented source. -/
def orientedFilteredShellZeroSourceEvent (preliminary : Set WalkPath)
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh cut : ℕ) : Set WalkPath :=
  preliminary ∩ orientedShellZeroSourceEvent t o m k w low externalLow
    externalHigh cut

/-- Exact selected-count slice of the oriented source. -/
def orientedShellZeroExactSourceEvent (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ) : Set WalkPath :=
  {s | ReachesThreshold s m k ∧
    let n := creationTimeNat m k s
    tilingDEtaAt t m k w low s n ∧
      orientedTilingThetaBases t o m w externalLow externalHigh s n = ∅ ∧
      (orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) s n).card = total}

/-- One complete typed trace atom of an oriented exact source slice. -/
def orientedShellZeroExactSourceTraceAtom (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ)
    (z : OrientedTypedFavoriteTilingTraceCode t) : Set WalkPath :=
  orientedShellZeroExactSourceEvent t o m k w low externalLow externalHigh
      total ∩
    {s | orientedTypedCreationTraceCode t o m k w s = z}

/-- The oriented exact source is covered by its complete typed trace atoms. -/
theorem iUnion_orientedShellZeroExactSourceTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ) :
    (⋃ z : OrientedTypedFavoriteTilingTraceCode t,
      orientedShellZeroExactSourceTraceAtom t o m k w low externalLow
        externalHigh total z) =
      orientedShellZeroExactSourceEvent t o m k w low externalLow
        externalHigh total := by
  ext s
  simp only [Set.mem_iUnion, orientedShellZeroExactSourceTraceAtom,
    Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hs, _⟩
    exact hs
  · intro hs
    exact ⟨orientedTypedCreationTraceCode t o m k w s, hs, rfl⟩

/-- Fixed-central-count replacement atom with the same endpoint orientation
and complete typed trace code. -/
def orientedShellZeroReplacementTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (z : OrientedTypedFavoriteTilingTraceCode t) : Set WalkPath :=
  let rank := replacementCreationRank k total central
  {s | ReachesThreshold s m rank ∧
    let n := creationTimeNat m rank s
    tilingDtildeEtaAt t m k w low s n ∧
      orientedTilingThetaBases t o m w externalLow externalHigh s n = ∅ ∧
      (orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m w) s n).card =
        central ∧
      (orientedTilingVTwoBases t o
        (shellZeroReplacementTotalWindow m w) s n).card =
        total - central ∧
      fixedOrientedTypedFavoriteTraceCode t o
        (shellZeroSourceTotalWindow m w ∪
          shellZeroReplacementTotalWindow m w) n s = z}

theorem orientedShellZeroReplacementTraceAtom_creation
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total central : ℕ}
    {z : OrientedTypedFavoriteTilingTraceCode t} {s : WalkPath}
    (hs : s ∈ orientedShellZeroReplacementTraceAtom t o m k w low
      externalLow externalHigh total central z) :
    ThresholdCreation s m (replacementCreationRank k total central)
      (creationTimeNat m (replacementCreationRank k total central) s) := by
  simpa only [creationTimeNat, hs.1, dif_pos] using
    (thresholdCreation_natFind hs.1)

theorem orientedShellZeroReplacementTraceAtom_trace
    {t : DominoTiling} {o : Orientation}
    {m k w low externalLow externalHigh total central : ℕ}
    {z : OrientedTypedFavoriteTilingTraceCode t} {s : WalkPath}
    (hs : s ∈ orientedShellZeroReplacementTraceAtom t o m k w low
      externalLow externalHigh total central z) :
    fixedOrientedTypedFavoriteTraceCode t o
        (shellZeroSourceTotalWindow m w ∪
          shellZeroReplacementTotalWindow m w)
        (creationTimeNat m (replacementCreationRank k total central) s) s =
      z := by
  exact hs.2.2.2.2.2

/-- Variable-clock jump data for the oriented full-trace replacement atoms. -/
def orientedShellZeroVariableClockJump
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (hm : 1 < m)
    (hrank : 0 < replacementCreationRank k total central) :
    VariableClockThresholdJumpReplacementFamily
      (orientedShellZeroReplacementTraceAtom t o m k w low externalLow
        externalHigh total central) where
  clock := fun _ s ↦
    creationTimeNat m (replacementCreationRank k total central) s
  traceAt := fun s n ↦ fixedOrientedTypedFavoriteTraceCode t o
    (shellZeroSourceTotalWindow m w ∪ shellZeroReplacementTotalWindow m w)
      n s
  thresholdCount := fun s n ↦ thresholdCount s n m
  monotone_thresholdCount := fun s ↦ thresholdCount_mono_time s m
  rank := replacementCreationRank k total central - 1
  trace_eq := fun _ _ hs ↦ orientedShellZeroReplacementTraceAtom_trace hs
  count_before := fun _ _ hs ↦
    thresholdCount_pred_eq_of_creation hm hrank
      (orientedShellZeroReplacementTraceAtom_creation hs)
  count_at := by
    intro z s hs
    have hcreation := orientedShellZeroReplacementTraceAtom_creation hs
    have hcount := thresholdCount_eq_of_creation hrank hcreation
    simpa only [Nat.sub_add_cancel hrank] using hcount

end

end Erdos1165.TilingOrientedShellZeroSourcePartition
