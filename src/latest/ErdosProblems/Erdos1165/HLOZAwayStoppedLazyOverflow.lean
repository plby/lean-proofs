/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZTypedTilingLazyOverflowScreen

/-!
# Source-correct stopped lazy overflow away from current favorite dominoes

The insertion product at a rank creation clock factors only away from the
current distinguished favorite dominoes.  Candidate extraction also uses
only a point outside those dominoes.  This file therefore replaces the
legacy all-point lazy exception by exactly the away event needed downstream.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZAwayStoppedLazyOverflow

open HLOZGapRandomClockScreen HLOZPathEvents HLOZTilingGapRandomClockScreen
open LazyDecomposition TilingLazyDecomposition
open TilingExternalPhaseSplit VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- At a deterministic prefix, non-external local time is capped at every
site outside the dominoes of the current favorite sites. -/
def TilingAwayLazyGoodAt (t : DominoTiling) (o : Orientation)
    (n cap : ℕ) (s : WalkPath) : Prop :=
  ∀ x, x ∉ favoriteTilingDominoSites t s n →
    pathPhasedBoundaryLocalTime o s n x +
      pathPhasedLazyLocalTime t o s n x ≤ cap

/-- The literal complement of `TilingAwayLazyGoodAt`. -/
def TilingAwayLazyOverflowAt (t : DominoTiling) (o : Orientation)
    (n cap : ℕ) (s : WalkPath) : Prop :=
  ∃ x, x ∉ favoriteTilingDominoSites t s n ∧
    cap < pathPhasedBoundaryLocalTime o s n x +
      pathPhasedLazyLocalTime t o s n x

theorem tilingAwayLazyOverflowAt_iff_not_good
    (t : DominoTiling) (o : Orientation) (n cap : ℕ) (s : WalkPath) :
    TilingAwayLazyOverflowAt t o n cap s ↔
      ¬TilingAwayLazyGoodAt t o n cap s := by
  simp only [TilingAwayLazyOverflowAt, TilingAwayLazyGoodAt,
    not_forall, not_le, exists_prop]

private theorem measurableSet_not_mem_favoriteTilingDominoSites
    (t : DominoTiling) (n : ℕ) (x : Point) :
    MeasurableSet {s : WalkPath | x ∉ favoriteTilingDominoSites t s n} := by
  exact measurable_favoriteTilingDominoSites t n
    (Set.to_countable {S : Finset Point | x ∉ S}).measurableSet

theorem measurableSet_tilingAwayLazyOverflowAt
    (t : DominoTiling) (o : Orientation) (n cap : ℕ) :
    MeasurableSet {s : WalkPath | TilingAwayLazyOverflowAt t o n cap s} := by
  rw [show {s : WalkPath | TilingAwayLazyOverflowAt t o n cap s} =
      ⋃ x : Point,
        {s | x ∉ favoriteTilingDominoSites t s n} ∩
          {s | cap < pathPhasedBoundaryLocalTime o s n x +
            pathPhasedLazyLocalTime t o s n x} by
    ext s
    simp [TilingAwayLazyOverflowAt]]
  exact MeasurableSet.iUnion fun x ↦
    (measurableSet_not_mem_favoriteTilingDominoSites t n x).inter
      (measurableSet_lt measurable_const
        ((measurable_pathPhasedBoundaryLocalTime o n x).add
          (measurable_pathPhasedLazyLocalTime t o n x)))

theorem measurableSet_tilingAwayLazyGoodAt
    (t : DominoTiling) (o : Orientation) (n cap : ℕ) :
    MeasurableSet {s : WalkPath | TilingAwayLazyGoodAt t o n cap s} := by
  rw [show {s : WalkPath | TilingAwayLazyGoodAt t o n cap s} =
      {s | TilingAwayLazyOverflowAt t o n cap s}ᶜ by
    ext s
    simp [tilingAwayLazyOverflowAt_iff_not_good]]
  exact (measurableSet_tilingAwayLazyOverflowAt t o n cap).compl

/-- Away lazy overflow at the genuine level/rank creation clock. -/
def tilingStoppedAwayLazyOverflowEvent (t : DominoTiling) (o : Orientation)
    (m rank cap : ℕ) : Set WalkPath :=
  ⋃ n, thresholdCreationSet m rank n ∩
    {s | TilingAwayLazyOverflowAt t o n cap s}

theorem measurableSet_tilingStoppedAwayLazyOverflowEvent
    (t : DominoTiling) (o : Orientation) (m rank cap : ℕ) :
    MeasurableSet (tilingStoppedAwayLazyOverflowEvent t o m rank cap) := by
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_thresholdCreationSet m rank n).inter
      (measurableSet_tilingAwayLazyOverflowAt t o n cap)

theorem tilingStoppedAwayLazyOverflowEvent_subset_thresholdReachStage
    (t : DominoTiling) (o : Orientation) (m rank cap : ℕ) :
    tilingStoppedAwayLazyOverflowEvent t o m rank cap ⊆
      thresholdReachStage m rank := by
  rw [thresholdReachStage_eq_iUnion_creation]
  rintro s hs
  rcases Set.mem_iUnion.mp hs with ⟨n, hcreation, _hoverflow⟩
  exact Set.mem_iUnion.mpr ⟨n, hcreation⟩

/-- The two temporal phases of the away lazy failure at one rank. -/
def rankAwayLazyCapFailureEvent (t : DominoTiling)
    (m cap rank : ℕ) : Set WalkPath :=
  tilingStoppedAwayLazyOverflowEvent t .even m rank cap ∪
    tilingStoppedAwayLazyOverflowEvent t .shifted m rank cap

theorem measurableSet_rankAwayLazyCapFailureEvent
    (t : DominoTiling) (m cap rank : ℕ) :
    MeasurableSet (rankAwayLazyCapFailureEvent t m cap rank) :=
  (measurableSet_tilingStoppedAwayLazyOverflowEvent
    t .even m rank cap).union
      (measurableSet_tilingStoppedAwayLazyOverflowEvent
        t .shifted m rank cap)

/-- Finite all-six away lazy exception. -/
def awayLazyOverflowExceptionalEvent
    (t : DominoTiling) (m cap : ℕ) : Set WalkPath :=
  (⋃ k : Fin 3,
      tilingStoppedAwayLazyOverflowEvent t .even m (k + 1) cap) ∪
    ⋃ k : Fin 3,
      tilingStoppedAwayLazyOverflowEvent t .shifted m (k + 1) cap

theorem measurableSet_awayLazyOverflowExceptionalEvent
    (t : DominoTiling) (m cap : ℕ) :
    MeasurableSet (awayLazyOverflowExceptionalEvent t m cap) :=
  (MeasurableSet.iUnion fun k : Fin 3 ↦
    measurableSet_tilingStoppedAwayLazyOverflowEvent
      t .even m (k + 1) cap).union
    (MeasurableSet.iUnion fun k : Fin 3 ↦
      measurableSet_tilingStoppedAwayLazyOverflowEvent
        t .shifted m (k + 1) cap)

/-- Source-correct good part: only away lazy overflow is removed. -/
def tilingAwayLazyGoodPart (t : DominoTiling) (event : Set WalkPath)
    (m cap : ℕ) : Set WalkPath :=
  event \ awayLazyOverflowExceptionalEvent t m cap

theorem measurableSet_tilingAwayLazyGoodPart
    {t : DominoTiling} {event : Set WalkPath} (hevent : MeasurableSet event)
    (m cap : ℕ) :
    MeasurableSet (tilingAwayLazyGoodPart t event m cap) :=
  hevent.diff (measurableSet_awayLazyOverflowExceptionalEvent t m cap)

/-- Outside the stopped away-overflow event, the exact away cap holds at
the supplied rank-creation clock. -/
theorem tiling_away_lazy_cap_at_creation_of_not_mem_overflow
    {t : DominoTiling} {o : Orientation} {m rank cap n : ℕ}
    {s : WalkPath}
    (hnot : s ∉ tilingStoppedAwayLazyOverflowEvent t o m rank cap)
    (hcreation : ThresholdCreation s m rank n) :
    TilingAwayLazyGoodAt t o n cap s := by
  intro x hxaway
  by_contra hcap
  apply hnot
  exact Set.mem_iUnion.mpr
    ⟨n, hcreation, x, hxaway, Nat.lt_of_not_ge hcap⟩

/-- Membership in the finite all-six good part supplies the away cap at
every positive rank at most three. -/
theorem tiling_away_lazy_cap_at_creation_of_mem_good
    {t : DominoTiling} {event : Set WalkPath} {m cap : ℕ}
    {o : Orientation} {rank n : ℕ} {s : WalkPath}
    (hs : s ∈ tilingAwayLazyGoodPart t event m cap)
    (hrankPos : 0 < rank) (hrankLe : rank ≤ 3)
    (hcreation : ThresholdCreation s m rank n) :
    TilingAwayLazyGoodAt t o n cap s := by
  apply tiling_away_lazy_cap_at_creation_of_not_mem_overflow
    (hcreation := hcreation)
  intro hoverflow
  let k : Fin 3 := ⟨rank - 1, by omega⟩
  have hk : (k : ℕ) + 1 = rank := by
    dsimp only [k]
    omega
  apply hs.2
  cases ho : o with
  | even =>
      left
      exact Set.mem_iUnion.mpr ⟨k, by simpa only [ho, hk] using hoverflow⟩
  | shifted =>
      right
      exact Set.mem_iUnion.mpr ⟨k, by simpa only [ho, hk] using hoverflow⟩

theorem tiling_away_lazy_cap_at_randomClock_of_mem_good
    {t : DominoTiling} {event : Set WalkPath} {m cutoff cap : ℕ}
    {band : RandomClockBand} {s : WalkPath}
    (hs : s ∈ tilingAwayLazyGoodPart t event m cap)
    (hcreation : ThresholdCreation s m band.oldRank
      (pathTruncatedLevelTime m band.oldRank cutoff s)) :
    TilingAwayLazyGoodAt t band.orientation
      (pathTruncatedLevelTime m band.oldRank cutoff s) cap s := by
  have hrank : band.oldRank ≤ 3 := Nat.lt_succ_iff.mp
    (band.rank_lt.trans_le band.newRank_le_four)
  exact tiling_away_lazy_cap_at_creation_of_mem_good hs
    band.oldRank_pos hrank hcreation

/-- The favorite-separation predicate used by candidate extraction implies
membership outside every current favorite domino. -/
theorem not_mem_favoriteTilingDominoSites_of_separated
    {t : DominoTiling} {s : WalkPath} {n : ℕ} {x : Point}
    (hsep : ∀ y ∈ favoriteSites s n,
      x ≠ y ∧ ¬Tilings.sameDomino t x y) :
    x ∉ favoriteTilingDominoSites t s n := by
  rw [favoriteTilingDominoSites, Finset.mem_union, not_or]
  refine ⟨?_, ?_⟩
  · intro hx
    exact (hsep x hx).1 rfl
  · intro hx
    obtain ⟨y, hy, hpartner⟩ := Finset.mem_image.mp hx
    have hxy : tilingPartner t x = y := by
      rw [← hpartner, tilingPartner_partner]
    exact (hsep y hy).2 ((sameDomino_iff_partner_eq t x y).2 hxy)

/-- This is the deterministic cap step used in endpoint candidate
extraction.  It asks for the lazy cap only at the separated new favorite,
never at a distinguished old favorite. -/
theorem pathPhasedExternalLocalTime_lower_bound_of_away_lazy_cap
    {t : DominoTiling} {o : Orientation} {s : WalkPath} {n : ℕ}
    {x : Point} {cap externalThreshold : ℕ}
    (hgood : TilingAwayLazyGoodAt t o n cap s)
    (hsep : ∀ y ∈ favoriteSites s n,
      x ≠ y ∧ ¬Tilings.sameDomino t x y)
    (hlarge : cap + externalThreshold ≤ localTime s n x) :
    externalThreshold ≤ pathPhasedExternalLocalTime t o s n x :=
  pathPhasedExternalLocalTime_lower_bound_of_boundary_lazy_cap
    (hgood x (not_mem_favoriteTilingDominoSites_of_separated hsep)) hlarge

end

end Erdos1165.HLOZAwayStoppedLazyOverflow
