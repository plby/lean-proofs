import ErdosProblems.Erdos1165.TilingTypedFavoriteTrace
import ErdosProblems.Erdos1165.TilingFavoriteTraceSupport
import ErdosProblems.Erdos1165.PreStoppingCutoff

/-!
# Pointwise factorization on typed favorite traces

This module fixes the concrete coordinate objects shared by the rank-one,
rank-two, and rank-three transition fibres.  A base coordinate predicate is
literal membership in the typed favorite-stage piece together with the
level-favorite condition at the stopped endpoint.  The coordinate cutoff is
chosen large enough for every capped insertion word.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.TilingTypedFavoriteFactorization

open HLOZPathEvents VariableStoppedTracePartition
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition TilingTypedFavoriteTrace
open TilingFavoriteTraceSupport TilingInsertionTerminalInvariant
open TilingTraceDataFixing PreStoppingSpatialLaw
open TilingCappedMarginalization TilingStoppedAcceptanceFactorization
open TilingInsertedLocalTime
open StoppedInsertion SpatialInsertionFiber PreStoppingFiber VariableStoppedFiber
open PreStoppingFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

abbrev typedRetainedCount {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) : ℕ := z.1.1

def typedRetained {t : DominoTiling} (z : TypedFavoriteTilingTraceCode t) :
    TilingRetainedWord t (0, 0) (typedRetainedCount z) := z.1.2.1

def typedBoundaryTail {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) : BoundaryTail := z.1.2.2

def typedFavoriteData {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) : TilingCreationFavoriteData := z.2

/-- Uniform time cutoff exceeding every insertion word whose individual
coordinates are bounded by `cap`. -/
def typedCoordinateCutoff {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) (cap : ℕ) : ℕ :=
  2 * (typedRetainedCount z + (typedRetainedCount z + 1) * cap) + 2

theorem tilingInsertionPrefixList_lt_typedCoordinateCutoff
    {t : DominoTiling} (z : TypedFavoriteTilingTraceCode t) (cap : ℕ)
    (q : TilingCappedCoordinates (typedRetainedCount z) cap) :
    (tilingInsertionPrefixList t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1).length <
        typedCoordinateCutoff z cap := by
  have hsum : (∑ j, (q j : ℕ)) ≤
      (typedRetainedCount z + 1) * cap := by
    calc
      (∑ j, (q j : ℕ)) ≤ ∑ _j : Fin (typedRetainedCount z + 1), cap :=
        Finset.sum_le_sum fun j _ ↦ by
          have hj := (q j).isLt
          omega
      _ = (typedRetainedCount z + 1) * cap := by simp
  rw [tilingInsertionPrefixList_length]
  have htail := (typedBoundaryTail z).2
  unfold typedCoordinateCutoff
  omega

/-- The canonical reconstructed path for one typed trace coordinate. -/
def typedInsertionWalk {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap) : WalkPath :=
  trajectory (extendPrefix (directionVectorOfList
    (tilingInsertionPrefixList t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1)))

/-- Literal base event on one coordinate fibre. -/
def typedFavoriteStageBasePredicate (t : DominoTiling) (m k : ℕ)
    (stage : Set WalkPath) (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap) : Prop :=
  typedInsertionWalk z q ∈ typedFavoriteTilingStagePiece t m k stage z ∧
    levelFavorite (typedInsertionWalk z q) m k

/-- The optional boundary terminal depends only on the typed trace, not on
insertion coordinates. -/
def typedInsertionTerminal (t : DominoTiling)
    (z : TypedFavoriteTilingTraceCode t) : Option Point :=
  tilingInsertionTerminal t (typedRetained z) (fun _ ↦ 0)
    (typedBoundaryTail z)

theorem tilingInsertionTerminal_eq_typedInsertionTerminal
    {t : DominoTiling} (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap) :
    tilingInsertionTerminal t (typedRetained z) (fun j ↦ (q j : ℕ))
        (typedBoundaryTail z) =
      typedInsertionTerminal t z := by
  exact tilingInsertionTerminal_eq_of_coordinates t (typedRetained z)
    (fun j ↦ (q j : ℕ)) (fun _ ↦ 0) (typedBoundaryTail z)

def typedDistinguished {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) : Finset Point :=
  (typedFavoriteData z).1.2

def typedFavoriteAwayUpper (t : DominoTiling)
    (m : ℕ) (z : TypedFavoriteTilingTraceCode t)
    (b : TilingAwayDomino t (0, 0) (typedRetained z)
      (typedDistinguished z)) : ℕ :=
  tilingFavoriteAwayUpper t (0, 0) (typedRetained z)
    (typedInsertionTerminal t z) m (typedDistinguished z) b

/-- Literal stopped clock associated with the coordinate cap. -/
def typedStoppingTime (m k : ℕ) {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) (cap : ℕ) : StepPath → ℕ :=
  truncatedLevelTime m k (typedCoordinateCutoff z cap)

theorem isFiniteStoppingTime_typedStoppingTime
    (m k : ℕ) {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) (cap : ℕ) :
    IsFiniteStoppingTime (typedStoppingTime m k z cap) :=
  isFiniteStoppingTime_truncatedLevelTime m k (typedCoordinateCutoff z cap)

/-- Base membership and stopped acceptance force the exact away-domino
truncation at level `m`. -/
theorem typedFavoriteStageBase_support
    (t : DominoTiling) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (stage : Set WalkPath) (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hbase : typedFavoriteStageBasePredicate t m k stage z q)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    TilingAwayTotalsScreen t (0, 0) (typedRetained z)
      (typedDistinguished z) (typedFavoriteAwayUpper t m z)
      (fun _ ↦ True)
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).2 := by
  have hpiece : typedInsertionWalk z q ∈
      favoriteTilingCreationPiece t m k
        (some (eraseTypedFavoriteTilingTraceCode t z)) := hbase.1.1
  have hscreen := tilingAwayTotalsScreen_of_acceptedFavoriteTrace
    t m k (typedCoordinateCutoff z cap) hm hk (typedRetained z) q
    (typedBoundaryTail z) (eraseTypedFavoriteTilingTraceCode t z)
    hpiece haccepted
    (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q)
    hbase.2
  rw [tilingInsertionTerminal_eq_typedInsertionTerminal z q] at hscreen
  exact hscreen

/-- Every actual away cutoff in a base fibre is strictly positive. -/
theorem typedFavoriteAwayUpper_pos_of_base_accepted
    (t : DominoTiling) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (stage : Set WalkPath) (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hbase : typedFavoriteStageBasePredicate t m k stage z q)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1)
    (b : TilingAwayDomino t (0, 0) (typedRetained z)
      (typedDistinguished z)) :
    0 < typedFavoriteAwayUpper t m z b := by
  have hs := typedFavoriteStageBase_support
    t m k hm hk stage z q hbase haccepted
  rw [tilingAwayTotalsScreen_true_iff] at hs
  exact (hs b).trans_le' (Nat.zero_le _)

/-- The stopped endpoint belongs to the distinguished favorite-base set
stored in its typed trace code. -/
theorem typedInsertionEndpoint_base_mem_distinguished
    (t : DominoTiling) (m k : ℕ) (hk : 0 < k)
    (stage : Set WalkPath) (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hbase : typedFavoriteStageBasePredicate t m k stage z q)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
    tilingBase t (typedInsertionWalk z q v.length) ∈ typedDistinguished z := by
  let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
  let s := typedInsertionWalk z q
  have hlt := tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q
  have hcreation : ThresholdCreation s m k v.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m k (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z) hlt).mp haccepted
  have hthreshold : s v.length ∈ thresholdSites s v.length m :=
    position_mem_thresholdSites_of_creation hk hcreation
  have hsites : thresholdSites s v.length m = favoriteSites s v.length :=
    thresholdSites_eq_favoriteSites_at_truncatedLevelTime
      m k (typedCoordinateCutoff z cap) v.length
      (extendPrefix (directionVectorOfList v)) hk hlt haccepted hbase.2
  have hfavorite : s v.length ∈ favoriteSites s v.length := by
    rw [← hsites]
    exact hthreshold
  have hmem : tilingBase t (s v.length) ∈ favoriteTilingBases t s v.length :=
    mem_favoriteTilingBases hfavorite
  have hpiece : s ∈ favoriteTilingCreationPiece t m k
      (some (eraseTypedFavoriteTilingTraceCode t z)) := hbase.1.1
  change tilingBase t (s v.length) ∈ typedDistinguished z
  have heq : favoriteTilingBases t s v.length = typedDistinguished z := by
    have hdata := hpiece.2
    change fixedTilingCreationFavoriteData t (creationTimeNat m k s) s =
      (eraseTypedFavoriteTilingTraceCode t z).2 at hdata
    have htime : creationTimeNat m k s = v.length :=
      creationTimeNat_eq_of_creation hcreation
    rw [htime] at hdata
    have heq' := congrArg (fun data : TilingCreationFavoriteData ↦ data.1.2) hdata
    exact heq'
  rw [← heq]
  exact hmem

/-- Positive version of the away cutoff, total even on empty typed trace
pieces.  It agrees with the literal favorite cutoff on every accepted base
coordinate. -/
def typedPositiveAwayUpper (t : DominoTiling)
    (m : ℕ) (z : TypedFavoriteTilingTraceCode t)
    (b : TilingAwayDomino t (0, 0) (typedRetained z)
      (typedDistinguished z)) : ℕ :=
  max 1 (typedFavoriteAwayUpper t m z b)

theorem typedPositiveAwayUpper_pos (t : DominoTiling)
    (m : ℕ) (z : TypedFavoriteTilingTraceCode t)
    (b : TilingAwayDomino t (0, 0) (typedRetained z)
      (typedDistinguished z)) :
    0 < typedPositiveAwayUpper t m z b := by
  unfold typedPositiveAwayUpper
  omega

theorem typedPositiveAwayUpper_eq_of_base_accepted
    (t : DominoTiling) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (stage : Set WalkPath) (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hbase : typedFavoriteStageBasePredicate t m k stage z q)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    typedPositiveAwayUpper t m z = typedFavoriteAwayUpper t m z := by
  funext b
  unfold typedPositiveAwayUpper
  rw [max_eq_right]
  exact typedFavoriteAwayUpper_pos_of_base_accepted
    t m k hm hk stage z q hbase haccepted b

/-- Support rewritten using the total strictly-positive cutoff. -/
theorem typedFavoriteStageBase_positive_support
    (t : DominoTiling) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (stage : Set WalkPath) (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hbase : typedFavoriteStageBasePredicate t m k stage z q)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    TilingAwayTotalsScreen t (0, 0) (typedRetained z)
      (typedDistinguished z) (typedPositiveAwayUpper t m z)
      (fun _ ↦ True)
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).2 := by
  rw [typedPositiveAwayUpper_eq_of_base_accepted
    t m k hm hk stage z q hbase haccepted]
  exact typedFavoriteStageBase_support
    t m k hm hk stage z q hbase haccepted

/-- Above level one, an accepted positive-rank creation word has nonzero
physical length. -/
theorem typedInsertionPrefixList_pos_of_accepted
    (t : DominoTiling) (m k : ℕ) (hm : 1 < m) (hk : 0 < k)
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    0 < (tilingInsertionPrefixList t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1).length := by
  let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
  have hcreation : ThresholdCreation (typedInsertionWalk z q) m k v.length :=
    (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m k (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z)
      (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q)).mp
        haccepted
  have hcount := thresholdCount_eq_of_creation hk hcreation
  by_contra hnot
  have hv : v.length = 0 := Nat.eq_zero_of_not_pos hnot
  have hvnil : v = [] := List.length_eq_zero_iff.mp hv
  change thresholdCount
      (trajectory (extendPrefix (directionVectorOfList v))) v.length m = k at hcount
  simp [hvnil, PreStoppingFiber.thresholdCount_trajectory_zero_time,
    show ¬m ≤ 1 by omega] at hcount
  omega

/-! ## Cylinder-level base predicate -/

/-- A coordinate belongs to the base fibre when every continuation of its
stopped prefix lies in the fixed typed trace/stage piece and is a
level-`m`, rank-`k` favorite path.  This formulation makes the required
`base_subset_piece` field literal rather than silently replacing an actual
walk by the canonical eventually-constant continuation. -/
def typedStoppedFavoriteStageBasePredicate
    (t : DominoTiling) (m k : ℕ) (stage : Set WalkPath)
    (z : TypedFavoriteTilingTraceCode t) (cap : ℕ)
    (q : TilingCappedCoordinates (typedRetainedCount z) cap) : Prop :=
  tilingStoppedInsertionAtom (typedStoppingTime m k z cap) t (0, 0)
      (typedRetained z) (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1 ⊆
    trajectory ⁻¹' (typedFavoriteTilingStagePiece t m k stage z ∩
      levelFavoriteSet m k)

/-- The cylinder-level definition supplies the exact path-space inclusion
required by a stopped coordinate product specification. -/
theorem typedStoppedFavoriteStageBase_subset_piece
    (t : DominoTiling) (m k : ℕ) (stage : Set WalkPath)
    (z : TypedFavoriteTilingTraceCode t) (cap : ℕ) :
    walkLift (tilingPreStoppingFiberEvent (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) cap (typedBoundaryTail z).1
      (typedStoppedFavoriteStageBasePredicate t m k stage z cap)) ⊆
      typedFavoriteTilingStagePiece t m k stage z := by
  intro s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  have hprefix := q.2.1 (hq : stepsOfWalk s ∈
    tilingStoppedInsertionAtom (typedStoppingTime m k z cap) t (0, 0)
      (typedRetained z) (fun j ↦ (q.1 j : ℕ)) (typedBoundaryTail z).1)
  have htraj := hprefix
  change trajectory (stepsOfWalk s) ∈
      typedFavoriteTilingStagePiece t m k stage z ∩ levelFavoriteSet m k at htraj
  rw [hvalid] at htraj
  exact htraj.1

/-- On an accepted coordinate, the canonical continuation witnesses the
cylinder predicate's trace and level-favorite data. -/
theorem typedStoppedFavoriteStageBase_canonical
    (t : DominoTiling) (m k : ℕ) (stage : Set WalkPath)
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hbase : typedStoppedFavoriteStageBasePredicate t m k stage z cap q)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    typedFavoriteStageBasePredicate t m k stage z q := by
  let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
  let omega := extendPrefix (directionVectorOfList v)
  have hatom : omega ∈ tilingStoppedInsertionAtom
      (typedStoppingTime m k z cap) t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1 := by
    exact ⟨haccepted, by
      unfold incrementPrefixList omega
      rw [stepPrefix_extendPrefix, ofFn_directionVectorOfList]⟩
  have h := hbase hatom
  exact ⟨h.1, h.2⟩

/-- Hence the exact positive away truncation also follows from the
cylinder-level base predicate used by the product specification. -/
theorem typedStoppedFavoriteStageBase_positive_support
    (t : DominoTiling) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (stage : Set WalkPath) (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (hbase : typedStoppedFavoriteStageBasePredicate t m k stage z cap q)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    TilingAwayTotalsScreen t (0, 0) (typedRetained z)
      (typedDistinguished z) (typedPositiveAwayUpper t m z)
      (fun _ ↦ True)
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).2 :=
  typedFavoriteStageBase_positive_support t m k hm hk stage z q
    (typedStoppedFavoriteStageBase_canonical
      t m k stage z q hbase haccepted) haccepted

/-! ## Exact factored stopped-coordinate constructor -/

/-- The screened coordinate predicate is the literal stopped base predicate
intersected with an arbitrary finite predicate on the away-domino totals. -/
def typedStoppedScreenedPredicate
    (t : DominoTiling) (m k : ℕ) (stage : Set WalkPath)
    (z : TypedFavoriteTilingTraceCode t) (cap : ℕ)
    (accepts : FiniteDominoProductLaw.TruncatedTotals
      (typedPositiveAwayUpper t m z) → Bool)
    (q : TilingCappedCoordinates (typedRetainedCount z) cap) : Prop :=
  screenedByAwayTotals t (0, 0) (typedRetained z) (typedDistinguished z)
    (typedPositiveAwayUpper t m z) (fun ell ↦ accepts ell = true)
    (typedStoppedFavoriteStageBasePredicate t m k stage z cap) q

/-- Remaining finite-screen inputs after all spatial marginal identities
have been reduced to pointwise stopped-stage invariance.  The `invariant`
field is semantic: it states that changing only strictly truncated away
coordinates preserves the stopped trace/stage/level data.  It is not a
probability estimate. -/
structure TypedStoppedStageScreeningData
    (t : DominoTiling) (m k : ℕ) (stage next : Set WalkPath)
    (cost : ℝ≥0∞) where
  accepts : ∀ z : TypedFavoriteTilingTraceCode t, ∀ cap,
    FiniteDominoProductLaw.TruncatedTotals
      (typedPositiveAwayUpper t m z) → Bool
  invariant : ∀ (z : TypedFavoriteTilingTraceCode t) cap q q',
    (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).1 =
      (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q').1 →
    TilingAwayTotalsScreen t (0, 0) (typedRetained z)
        (typedDistinguished z) (typedPositiveAwayUpper t m z)
        (fun _ ↦ True)
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) q).2 →
    TilingAwayTotalsScreen t (0, 0) (typedRetained z)
        (typedDistinguished z) (typedPositiveAwayUpper t m z)
        (fun _ ↦ True)
        (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
          (typedDistinguished z) q').2 →
    (typedStoppedFavoriteStageBasePredicate t m k stage z cap q ∧
        TilingStoppingAccepted (typedStoppingTime m k z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
          (typedBoundaryTail z).1 ↔
      typedStoppedFavoriteStageBasePredicate t m k stage z cap q' ∧
        TilingStoppingAccepted (typedStoppingTime m k z cap)
          t (0, 0) (typedRetained z) (fun j ↦ (q' j : ℕ))
          (typedBoundaryTail z).1)
  monotone_screened : ∀ z, Monotone fun cap ↦
    walkLift (tilingPreStoppingFiberEvent (typedStoppingTime m k z cap)
      t (0, 0) (typedRetained z) cap (typedBoundaryTail z).1
      (typedStoppedScreenedPredicate t m k stage z cap (accepts z cap)))
  transition_covered : ∀ z,
    typedFavoriteTilingStagePiece t m k stage z ∩ next ⊆ ⋃ cap,
      walkLift (tilingPreStoppingFiberEvent (typedStoppingTime m k z cap)
        t (0, 0) (typedRetained z) cap (typedBoundaryTail z).1
        (typedStoppedScreenedPredicate t m k stage z cap (accepts z cap)))
  product_bound : ∀ z cap,
    FiniteDominoProductLaw.screenMass
      (tilingAwayPointMass (cap := cap) t (0, 0) (typedRetained z)
        (typedDistinguished z)) (typedPositiveAwayUpper t m z)
      (fun ell ↦ accepts z cap ell = true) ≤ cost.toReal

/-- Exact all-six stopped-coordinate product data derived from typed trace
semantics.  Distinguished marginalization and both finite product identities
are provided by `TilingCappedMarginalization`; they are not assumptions of
this constructor. -/
noncomputable def typedFactoredStoppedCoordinateData
    (t : DominoTiling) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (stage next : Set WalkPath) (cost : ℝ≥0∞)
    (data : TypedStoppedStageScreeningData t m k stage next cost) :
    TilingFactoredStoppedCoordinateData
      (typedFavoriteTilingStagePiece t m k stage) next cost := by
  classical
  refine {
    tiling := fun _ _ ↦ t
    retainedCount := fun z _ ↦ typedRetainedCount z
    start := fun _ _ ↦ (0, 0)
    retained := fun z _ ↦ typedRetained z
    tail := fun z _ ↦ (typedBoundaryTail z).1
    stoppingTime := fun z cap ↦ typedStoppingTime m k z cap
    isStoppingTime := fun z cap ↦
      isFiniteStoppingTime_typedStoppingTime m k z cap
    basePredicate := fun z cap ↦
      typedStoppedFavoriteStageBasePredicate t m k stage z cap
    screenedPredicate := fun z cap ↦
      typedStoppedScreenedPredicate t m k stage z cap (data.accepts z cap)
    screened_subset_base := ?_
    base_subset_piece := ?_
    distinguished := fun z _ ↦ typedDistinguished z
    selected := fun z cap ↦ distinguishedAcceptedSelector
      (typedStoppingTime m k z cap) t (0, 0) (typedRetained z)
      (typedBoundaryTail z).1
      (typedStoppedFavoriteStageBasePredicate t m k stage z cap)
      (typedDistinguished z)
    upper := fun z _ ↦ typedPositiveAwayUpper t m z
    accepts := data.accepts
    base_factorization := ?_
    screened_factorization := ?_
    upper_pos := fun z _ ↦ typedPositiveAwayUpper_pos t m z
    monotone_screened := data.monotone_screened
    transition_covered := data.transition_covered
    product_bound := data.product_bound }
  · intro z cap q hq
    exact screenedByAwayTotals_subset_base t (0, 0) (typedRetained z)
      (typedDistinguished z) (typedPositiveAwayUpper t m z)
      (fun ell ↦ data.accepts z cap ell = true)
      (typedStoppedFavoriteStageBasePredicate t m k stage z cap) q hq
  · intro z cap
    exact typedStoppedFavoriteStageBase_subset_piece t m k stage z cap
  · intro z cap q
    exact acceptedBase_iff_distinguishedSelector_and_awayScreen
      (typedStoppingTime m k z cap) t (0, 0) (typedRetained z)
      (typedBoundaryTail z).1
      (typedStoppedFavoriteStageBasePredicate t m k stage z cap)
      (typedDistinguished z) (typedPositiveAwayUpper t m z)
      (typedPositiveAwayUpper_pos t m z)
      (fun q hq ↦ typedStoppedFavoriteStageBase_positive_support
        t m k hm hk stage z q hq.1 hq.2)
      (data.invariant z cap) q
  · intro z cap q
    apply screenedByAwayTotals_and_accepted_iff
      (typedStoppingTime m k z cap) t (0, 0) (typedRetained z)
      (typedBoundaryTail z).1
      (typedStoppedFavoriteStageBasePredicate t m k stage z cap)
      (typedDistinguished z) (typedPositiveAwayUpper t m z)
      (fun ell ↦ data.accepts z cap ell = true)
      (distinguishedAcceptedSelector (typedStoppingTime m k z cap)
        t (0, 0) (typedRetained z) (typedBoundaryTail z).1
        (typedStoppedFavoriteStageBasePredicate t m k stage z cap)
        (typedDistinguished z))
    intro q'
    exact acceptedBase_iff_distinguishedSelector_and_awayScreen
      (typedStoppingTime m k z cap) t (0, 0) (typedRetained z)
      (typedBoundaryTail z).1
      (typedStoppedFavoriteStageBasePredicate t m k stage z cap)
      (typedDistinguished z) (typedPositiveAwayUpper t m z)
      (typedPositiveAwayUpper_pos t m z)
      (fun q'' hq ↦ typedStoppedFavoriteStageBase_positive_support
        t m k hm hk stage z q'' hq.1 hq.2)
      (data.invariant z cap) q'

end

end Erdos1165.TilingTypedFavoriteFactorization
