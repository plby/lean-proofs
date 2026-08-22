/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedAllCreationConcreteFamily

/-!
# External-word all-creation stopped coordinates

The shell-zero replacement changes current favorite sites, so a common
cross-clock atom cannot fix `TilingCreationFavoriteData`.  This file removes
exactly that field while retaining the physical oriented external word and
the exact represented support `S`.

The construction is not a new path decomposition.  An external atom is the
countable union of the already checked full-favorite atoms over all favorite
data.  Consequently soundness, cofinal completeness, and cap monotonicity are
inherited from the physical prefixed all-creation fibres, while no equality
of source and replacement favorite data is asserted.
-/

open MeasureTheory Set

namespace Erdos1165.TilingOrientedExternalAllCreationStoppedCoordinate

open FiniteDominoProductLaw HLOZProposition48Candidates
open LazyDecomposition
open PreStoppingFiber SpatialInsertionFiber StoppedInsertion VariableStoppedFiber
open TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition
open HLOZPathEvents VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A full trace obtained by adjoining one possible current-favorite datum
to a fixed physical oriented external word. -/
def withFavorite {t : DominoTiling}
    (z : OrientedTilingTypedExternalWordCode t)
    (favorite : TilingCreationFavoriteData) :
    OrientedAllCreationTraceCode t where
  external := z
  favorite := favorite

@[simp] theorem withFavorite_external {t : DominoTiling}
    (z : OrientedTilingTypedExternalWordCode t)
    (favorite : TilingCreationFavoriteData) :
    (withFavorite z favorite).external = z := rfl

/-- A creation atom fixing the complete physical external word and support,
but deliberately summing over every possible current-favorite datum. -/
def orientedExternalAllCreationSupportTraceAtom
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) :
    Set WalkPath :=
  ⋃ favorite : TilingCreationFavoriteData,
    orientedAllCreationSupportTraceAtom t o m k supportAt
      (withFavorite z favorite) S

/-- Nonempty exact external-word/support atoms. -/
abbrev SupportedIndex
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) :=
  {eta : OrientedTilingTypedExternalWordCode t × Finset Point //
    (orientedExternalAllCreationSupportTraceAtom
      t o m k supportAt eta.1 eta.2).Nonempty}

theorem orientedExternalAllCreationSupportTraceAtom_eq
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point) :
    orientedExternalAllCreationSupportTraceAtom t o m k supportAt z S =
      {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
        fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s = z ∧
        supportAt s (creationTimeNat m k s) = S} := by
  ext s
  constructor
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨favorite, hs⟩
    rcases hs with ⟨⟨hvalid, hreach, hcode⟩, hsupport⟩
    exact ⟨hvalid, hreach,
      congrArg OrientedAllCreationTraceCode.external hcode, hsupport⟩
  · rintro ⟨hvalid, hreach, hexternal, hsupport⟩
    let favorite := (fixedOrientedAllCreationTraceCode t o
      (creationTimeNat m k s) s).favorite
    apply Set.mem_iUnion.mpr
    refine ⟨favorite, ⟨⟨hvalid, hreach, ?_⟩, hsupport⟩⟩
    simp only [favorite, fixedOrientedAllCreationTraceCode, withFavorite,
      OrientedAllCreationTraceCode.mk.injEq]
    exact ⟨hexternal, trivial⟩

theorem measurableSet_orientedExternalAllCreationSupportTraceAtom
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (z : OrientedTilingTypedExternalWordCode t) (S : Finset Point)
    (hsupport : Measurable fun s ↦
      supportAt s (creationTimeNat m k s)) :
    MeasurableSet
      (orientedExternalAllCreationSupportTraceAtom
        t o m k supportAt z S) := by
  apply MeasurableSet.iUnion
  intro favorite
  exact measurableSet_orientedAllCreationSupportTraceAtom_of
    t o m k supportAt (withFavorite z favorite) S
      (measurableSet_orientedAllCreationTraceAtom
        t o m k (withFavorite z favorite)) hsupport

/-- The stopped cylinder predicate with the current-favorite datum erased. -/
def externalStoppedAtomPredicate
    {t : DominoTiling} (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (S : Finset Point) (z : OrientedTilingTypedExternalWordCode t)
    (cap : ℕ) (q : TilingCappedCoordinates z.retainedCount cap) : Prop :=
  ∃ favorite : TilingCreationFavoriteData,
    orientedAllCreationStoppedAtomPredicate o m k supportAt S
      (withFavorite z favorite) cap q

/-- The cutoff is independent of current-favorite data. -/
def externalCoordinateCutoff {t : DominoTiling}
    (z : OrientedTilingTypedExternalWordCode t) (cap : ℕ) : ℕ :=
  z.initial.1.length +
    2 * (z.retainedCount + (z.retainedCount + 1) * cap) +
    z.tail.1.length + 1

@[simp] theorem orientedAllCreationCoordinateCutoff_withFavorite
    {t : DominoTiling} (z : OrientedTilingTypedExternalWordCode t)
    (favorite : TilingCreationFavoriteData) (cap : ℕ) :
    orientedAllCreationCoordinateCutoff (withFavorite z favorite) cap =
      externalCoordinateCutoff z cap := rfl

/-- The distinguished projection of the external-word atom. -/
def externalSelected
    {t : DominoTiling} (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (S : Finset Point) (z : OrientedTilingTypedExternalWordCode t)
    (cap : ℕ)
    (d : TilingDistinguishedCoordinates (cap := cap) t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S)) : Prop :=
  ∃ a, let q :=
      (splitTilingCoordinatesEquiv t z.start z.retained
        (supportComplementDistinguished t z.start z.retained S)).symm (d, a)
    externalStoppedAtomPredicate o m k supportAt S z cap q ∧
      PrefixedTilingStoppingAccepted
        (truncatedLevelTime m k (externalCoordinateCutoff z cap))
        z.initial.1 t z.start z.retained (fun j ↦ (q j : ℕ)) z.tail.1

/-- Stopped-coordinate data on an external-word/support atom.  This mirrors
the reusable all-creation spec, but its atom is the honest union over current
favorite data. -/
structure Spec
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (S : Finset Point) (z : OrientedTilingTypedExternalWordCode t) where
  coordinateCap : ℕ → ℕ
  capStart : ℕ
  coordinateCap_eq : ∀ cap, coordinateCap cap = capStart + cap
  totalCap : ℕ
  totalCap_le_capStart : totalCap ≤ capStart
  retainedCount_le_totalCap : z.retainedCount ≤ totalCap
  stoppingTime : ℕ → StepPath → ℕ
  isStoppingTime : ∀ cap, IsFiniteStoppingTime (stoppingTime cap)
  atomPredicate : ∀ cap, TilingCappedCoordinates z.retainedCount
    (coordinateCap cap) → Prop
  support_represented :
    S ⊆ tilingExternalDominoBases t z.start z.retained
  selected : ∀ cap, TilingDistinguishedCoordinates
    (cap := coordinateCap cap) t z.start z.retained
      (supportComplementDistinguished t z.start z.retained S) → Prop
  upper : ∀ (_cap : ℕ), TilingAwayDomino t z.start z.retained
    (supportComplementDistinguished t z.start z.retained S) → ℕ
  upper_pos : ∀ cap b, 0 < upper cap b
  totalCap_lt_upper : ∀ cap b, totalCap < upper cap b
  atom_measurable : MeasurableSet
    (orientedExternalAllCreationSupportTraceAtom t o m k supportAt z S)
  atom_sound : ∀ cap,
    walkLift (prefixedTilingPreStoppingFiberEvent (stoppingTime cap)
      z.initial.1 t z.start z.retained (coordinateCap cap) z.tail.1
        (atomPredicate cap)) ⊆
      orientedExternalAllCreationSupportTraceAtom t o m k supportAt z S
  atom_complete :
    orientedExternalAllCreationSupportTraceAtom t o m k supportAt z S ⊆
      ⋃ cap, walkLift (prefixedTilingPreStoppingFiberEvent
        (stoppingTime cap) z.initial.1 t z.start z.retained
        (coordinateCap cap) z.tail.1 (atomPredicate cap))
  atom_monotone : Monotone fun cap ↦
    walkLift (prefixedTilingPreStoppingFiberEvent (stoppingTime cap)
      z.initial.1 t z.start z.retained (coordinateCap cap) z.tail.1
        (atomPredicate cap))

/-- One concrete external-word/support fibre, obtained by taking the union
of the already checked full-favorite stopped cylinders. -/
noncomputable def concreteFiber
    {t : DominoTiling} (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt) :
    Spec t o m k supportAt eta.1.2 eta.1.1 := by
  classical
  let z := eta.1.1
  let S := eta.1.2
  have hrepresented : S ⊆
      tilingExternalDominoBases t z.start z.retained := by
    rcases eta.2 with ⟨s, hs⟩
    rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs
    have hrep := supportData.represented s (creationTimeNat m k s) hs.1
    rw [hs.2.2.1] at hrep
    simpa only [hs.2.2.2] using hrep
  let capStart := max z.retainedCount (m + shellWidth48 m)
  let dummy : TilingCreationFavoriteData := ((∅, ∅), (z.start, z.start))
  refine {
    coordinateCap := fun cap ↦ capStart + cap
    capStart := capStart
    coordinateCap_eq := fun _ ↦ rfl
    totalCap := capStart
    totalCap_le_capStart := le_rfl
    retainedCount_le_totalCap := Nat.le_max_left _ _
    stoppingTime := fun cap ↦ truncatedLevelTime m k
      (externalCoordinateCutoff z (capStart + cap))
    isStoppingTime := fun cap ↦ isFiniteStoppingTime_truncatedLevelTime
      m k (externalCoordinateCutoff z (capStart + cap))
    atomPredicate := fun cap ↦ externalStoppedAtomPredicate
      o m k supportAt S z (capStart + cap)
    support_represented := hrepresented
    selected := fun cap ↦ externalSelected o m k supportAt S z
      (capStart + cap)
    upper := fun _ _ ↦ capStart + 1
    upper_pos := by intro _ _; omega
    totalCap_lt_upper := by intro _ _; omega
    atom_measurable := measurableSet_orientedExternalAllCreationSupportTraceAtom
      t o m k supportAt z S supportData.measurableAtCreation
    atom_sound := ?_
    atom_complete := ?_
    atom_monotone := ?_ }
  · intro cap s hs
    rcases hs with ⟨hvalid, hevent⟩
    rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
    rcases q.2.1 with ⟨favorite, hfavorite⟩
    apply Set.mem_iUnion.mpr
    refine ⟨favorite, ?_⟩
    apply (walkLift_orientedAllCreationStoppedAtomFiber_subset
      o m k supportAt S (withFavorite z favorite) (capStart + cap))
    let qfull : PrefixedTilingAcceptedCappedCoordinates
        (truncatedLevelTime m k
          (orientedAllCreationCoordinateCutoff
            (withFavorite z favorite) (capStart + cap)))
        z.initial.1 t z.start z.retained (capStart + cap) z.tail.1
        (orientedAllCreationStoppedAtomPredicate o m k supportAt S
          (withFavorite z favorite) (capStart + cap)) :=
      ⟨q.1, hfavorite, by
        simpa only [z, withFavorite, orientedAllCreationCoordinateCutoff,
          externalCoordinateCutoff] using q.2.2⟩
    refine ⟨hvalid, Set.mem_iUnion.mpr ⟨qfull, ?_⟩⟩
    simpa only [z, qfull, withFavorite, orientedAllCreationCoordinateCutoff,
      externalCoordinateCutoff] using hq
  · intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨favorite, hfavorite⟩
    have hfull := exactAtom_subset_iUnion_orientedAllCreationStoppedAtomFiber
      o m k capStart supportAt supportData S (withFavorite z favorite)
        hfavorite
    rcases Set.mem_iUnion.mp hfull with ⟨cap, hcap⟩
    apply Set.mem_iUnion.mpr
    refine ⟨cap, ?_⟩
    rcases hcap with ⟨hvalid, hevent⟩
    refine ⟨hvalid, ?_⟩
    rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
    let qexternal : PrefixedTilingAcceptedCappedCoordinates
        (truncatedLevelTime m k (externalCoordinateCutoff z (capStart + cap)))
        z.initial.1 t z.start z.retained (capStart + cap) z.tail.1
        (externalStoppedAtomPredicate o m k supportAt S z
          (capStart + cap)) :=
      ⟨q.1, ⟨favorite, q.2.1⟩, by
        simpa only [z, withFavorite, orientedAllCreationCoordinateCutoff,
          externalCoordinateCutoff] using q.2.2⟩
    apply Set.mem_iUnion.mpr
    refine ⟨qexternal, ?_⟩
    simpa only [z, qexternal, withFavorite,
      orientedAllCreationCoordinateCutoff, externalCoordinateCutoff] using hq
  · intro cap cap' hcap s hs
    rcases hs with ⟨hvalid, hevent⟩
    rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
    rcases q.2.1 with ⟨favorite, hfavorite⟩
    have hmono := monotone_orientedAllCreationStoppedAtomFiber
      o m k capStart supportAt S (withFavorite z favorite) hcap
    have hsource : s ∈ walkLift
        (prefixedTilingPreStoppingFiberEvent
          (truncatedLevelTime m k
            (orientedAllCreationCoordinateCutoff
              (withFavorite z favorite) (capStart + cap)))
          z.initial.1 t z.start z.retained (capStart + cap) z.tail.1
          (orientedAllCreationStoppedAtomPredicate o m k supportAt S
            (withFavorite z favorite) (capStart + cap))) := by
      let qfull : PrefixedTilingAcceptedCappedCoordinates
          (truncatedLevelTime m k
            (orientedAllCreationCoordinateCutoff
              (withFavorite z favorite) (capStart + cap)))
          z.initial.1 t z.start z.retained (capStart + cap) z.tail.1
          (orientedAllCreationStoppedAtomPredicate o m k supportAt S
            (withFavorite z favorite) (capStart + cap)) :=
        ⟨q.1, hfavorite, by
          simpa only [z, withFavorite, orientedAllCreationCoordinateCutoff,
            externalCoordinateCutoff] using q.2.2⟩
      refine ⟨hvalid, Set.mem_iUnion.mpr ⟨qfull, ?_⟩⟩
      simpa only [z, qfull, withFavorite,
        orientedAllCreationCoordinateCutoff, externalCoordinateCutoff] using hq
    rcases hmono hsource with ⟨hvalid', hevent'⟩
    refine ⟨hvalid', ?_⟩
    rcases Set.mem_iUnion.mp hevent' with ⟨q', hq'⟩
    let qexternal : PrefixedTilingAcceptedCappedCoordinates
        (truncatedLevelTime m k (externalCoordinateCutoff z (capStart + cap')))
        z.initial.1 t z.start z.retained (capStart + cap') z.tail.1
        (externalStoppedAtomPredicate o m k supportAt S z
          (capStart + cap')) :=
      ⟨q'.1, ⟨favorite, q'.2.1⟩, by
        simpa only [z, withFavorite, orientedAllCreationCoordinateCutoff,
          externalCoordinateCutoff] using q'.2.2⟩
    apply Set.mem_iUnion.mpr
    refine ⟨qexternal, ?_⟩
    simpa only [z, qexternal, withFavorite,
      orientedAllCreationCoordinateCutoff, externalCoordinateCutoff] using hq'

/-- The reusable external-word family for every nonempty exact `(z,S)` atom. -/
noncomputable def concreteFamily
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt) :
    ∀ eta : SupportedIndex t o m k supportAt,
      Spec t o m k supportAt eta.1.2 eta.1.1 :=
  fun eta ↦ concreteFiber o m k supportAt supportData eta

end

end Erdos1165.TilingOrientedExternalAllCreationStoppedCoordinate
