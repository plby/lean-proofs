/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingPrefixedConditionalCappedMarginalization
import ErdosProblems.Erdos1165.TilingOrientedPrefixedSupportBridge
import ErdosProblems.Erdos1165.TilingOrientedShellZeroSourcePartition

/-!
# A reusable prefixed coordinate fibre before source screening

The shell-zero fibres are already restricted by `D_eta` and `Theta = empty`.
They therefore cannot be used either to pay the complementary Theta event or
to condition the good low-scale history.  This file puts the common stopped
coordinate disintegration one layer earlier: an atom fixes only the creation
clock and the complete oriented retained/favorite/support trace.

An arbitrary predicate on the reconstructed away-total vector can then be
added deterministically.  Theta slot screens and the broad/narrow low-scale
candidate screens consequently share the same physical-prefix cylinders and
the same unscreened base factorization.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.TilingOrientedAllCreationStoppedCoordinate

open FiniteDominoProductLaw HLOZPathEvents
open LazyDecomposition
open TilingCappedMarginalization
open TilingConditionalCappedMarginalization
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedConditionalCappedMarginalization
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Complete oriented retained/favorite data, deliberately excluding any
`V₂` support or Theta classification. -/
structure OrientedAllCreationTraceCode (t : DominoTiling) where
  external : OrientedTilingTypedExternalWordCode t
  favorite : TilingCreationFavoriteData
  deriving Countable

/-- The pre-source trace at a deterministic physical time. -/
def fixedOrientedAllCreationTraceCode (t : DominoTiling) (o : Orientation)
    (n : ℕ) (s : WalkPath) : OrientedAllCreationTraceCode t where
  external := fixedOrientedTypedExternalWordCode t o n s
  favorite := ((favoriteSites s n,
      (favoriteSites s n).image (TilingLazyDecomposition.tilingBase t)),
    ((fixedOrientedTypedExternalWordCode t o n s).start, s n))

/-- A complete oriented trace atom at the rank-`k` creation clock, before any
`D_eta`, Theta, support-window, or source-window restriction. -/
def orientedAllCreationTraceAtom (t : DominoTiling) (o : Orientation)
    (m k : ℕ) (z : OrientedAllCreationTraceCode t) : Set WalkPath :=
  {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
    fixedOrientedAllCreationTraceCode t o (creationTimeNat m k s) s = z}

theorem iUnion_orientedAllCreationTraceAtom (t : DominoTiling)
    (o : Orientation) (m k : ℕ) :
    (⋃ z : OrientedAllCreationTraceCode t,
      orientedAllCreationTraceAtom t o m k z) =
      thresholdReachStage m k ∩ validStepWalk := by
  ext s
  simp only [Set.mem_iUnion, orientedAllCreationTraceAtom,
    Set.mem_ofPred_eq, thresholdReachStage, Set.mem_inter_iff]
  constructor
  · rintro ⟨z, hvalid, hs, _⟩
    exact ⟨hs, hvalid⟩
  · rintro ⟨hs, hvalid⟩
    exact ⟨fixedOrientedAllCreationTraceCode t o
      (creationTimeNat m k s) s, hvalid, hs, rfl⟩

/-- Nonempty all-creation trace atoms.  The null/invalid support branch is
absent by construction, while no source-goodness predicate is assumed. -/
abbrev OrientedAllCreationSupportedTraceIndex
    (t : DominoTiling) (o : Orientation) (m k : ℕ) :=
  {z : OrientedAllCreationTraceCode t //
    (orientedAllCreationTraceAtom t o m k z).Nonempty}

theorem iUnion_supported_orientedAllCreationTraceAtom
    (t : DominoTiling) (o : Orientation) (m k : ℕ) :
    (⋃ eta : OrientedAllCreationSupportedTraceIndex t o m k,
      orientedAllCreationTraceAtom t o m k eta.1) =
      thresholdReachStage m k ∩ validStepWalk := by
  rw [← iUnion_orientedAllCreationTraceAtom t o m k]
  ext s
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨eta, hs⟩
    exact ⟨eta.1, hs⟩
  · rintro ⟨z, hs⟩
    exact ⟨⟨z, ⟨s, hs⟩⟩, hs⟩

theorem pairwise_disjoint_orientedAllCreationTraceAtom
    (t : DominoTiling) (o : Orientation) (m k : ℕ) :
    Pairwise fun z z' : OrientedAllCreationTraceCode t ↦
      Disjoint (orientedAllCreationTraceAtom t o m k z)
        (orientedAllCreationTraceAtom t o m k z') := by
  intro z z' hne
  rw [Set.disjoint_left]
  intro s hs hs'
  apply hne
  exact hs.2.2.symm.trans hs'.2.2

/-- Refine a full retained/favorite atom by an exact finite support selector.
The selector is a parameter: low-scale candidates use the dominant broad-I1
support, while Theta consumers may use their own slot support. -/
def orientedAllCreationSupportTraceAtom
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (z : OrientedAllCreationTraceCode t) (S : Finset Point) : Set WalkPath :=
  orientedAllCreationTraceAtom t o m k z ∩
    {s | supportAt s (creationTimeNat m k s) = S}

abbrev OrientedAllCreationSupportedAtomIndex
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) :=
  {eta : OrientedAllCreationTraceCode t × Finset Point //
    (orientedAllCreationSupportTraceAtom t o m k supportAt eta.1 eta.2).Nonempty}

theorem iUnion_supported_orientedAllCreationSupportTraceAtom
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) :
    (⋃ eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt,
      orientedAllCreationSupportTraceAtom t o m k supportAt eta.1.1 eta.1.2) =
      thresholdReachStage m k ∩ validStepWalk := by
  rw [← iUnion_orientedAllCreationTraceAtom t o m k]
  ext s
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨eta, hs⟩
    exact ⟨eta.1.1, hs.1⟩
  · rintro ⟨z, hs⟩
    let S := supportAt s (creationTimeNat m k s)
    have hsupported : s ∈
        orientedAllCreationSupportTraceAtom t o m k supportAt z S :=
      ⟨hs, rfl⟩
    exact ⟨⟨(z, S), ⟨s, hsupported⟩⟩, hsupported⟩

theorem pairwise_disjoint_orientedAllCreationSupportTraceAtom
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) :
    Pairwise fun eta eta' : OrientedAllCreationTraceCode t × Finset Point ↦
      Disjoint
        (orientedAllCreationSupportTraceAtom t o m k supportAt eta.1 eta.2)
        (orientedAllCreationSupportTraceAtom t o m k supportAt eta'.1 eta'.2) := by
  intro eta eta' hne
  rw [Set.disjoint_left]
  intro s hs hs'
  apply hne
  apply Prod.ext
  · exact hs.1.2.2.symm.trans hs'.1.2.2
  · exact hs.2.symm.trans hs'.2

theorem measurableSet_orientedAllCreationSupportTraceAtom_of
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (z : OrientedAllCreationTraceCode t) (S : Finset Point)
    (htrace : MeasurableSet (orientedAllCreationTraceAtom t o m k z))
    (hsupport : Measurable fun s ↦
      supportAt s (creationTimeNat m k s)) :
    MeasurableSet
      (orientedAllCreationSupportTraceAtom t o m k supportAt z S) := by
  exact htrace.inter (measurableSet_eq_fun hsupport measurable_const)

/-- The common stopped-coordinate input used before Theta/source screening.
It covers the exact atom but deliberately contains no unscreened product
factorization; each consumer supplies its honest direct screen below. -/
structure OrientedAllCreationPrefixedStoppedCoordinateSpec
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (S : Finset Point) (z : OrientedAllCreationTraceCode t) where
  coordinateCap : ℕ → ℕ
  capStart : ℕ
  coordinateCap_eq : ∀ cap, coordinateCap cap = capStart + cap
  totalCap : ℕ
  totalCap_le_capStart : totalCap ≤ capStart
  retainedCount_le_totalCap : z.external.retainedCount ≤ totalCap
  stoppingTime : ℕ → StepPath → ℕ
  isStoppingTime : ∀ cap, IsFiniteStoppingTime (stoppingTime cap)
  atomPredicate : ∀ cap,
    TilingCappedCoordinates z.external.retainedCount (coordinateCap cap) → Prop
  support_represented :
    S ⊆ tilingExternalDominoBases t z.external.start z.external.retained
  selected : ∀ cap, TilingDistinguishedCoordinates (cap := coordinateCap cap)
    t z.external.start z.external.retained
      (supportComplementDistinguished t z.external.start z.external.retained S) → Prop
  upper : ∀ (_cap : ℕ), TilingAwayDomino t z.external.start z.external.retained
    (supportComplementDistinguished t z.external.start z.external.retained S) → ℕ
  upper_pos : ∀ (cap : ℕ) b, 0 < upper cap b
  totalCap_lt_upper : ∀ (cap : ℕ) b, totalCap < upper cap b
  atom_measurable : MeasurableSet
    (orientedAllCreationSupportTraceAtom t o m k supportAt z S)
  atom_sound : ∀ cap,
    walkLift (prefixedTilingPreStoppingFiberEvent (stoppingTime cap)
      z.external.initial.1 t z.external.start z.external.retained
      (coordinateCap cap) z.external.tail.1 (atomPredicate cap)) ⊆
        orientedAllCreationSupportTraceAtom t o m k supportAt z S
  atom_complete :
    orientedAllCreationSupportTraceAtom t o m k supportAt z S ⊆
      ⋃ cap, walkLift (prefixedTilingPreStoppingFiberEvent
        (stoppingTime cap) z.external.initial.1 t z.external.start
        z.external.retained (coordinateCap cap) z.external.tail.1
        (atomPredicate cap))
  atom_monotone : Monotone fun cap ↦
    walkLift (prefixedTilingPreStoppingFiberEvent (stoppingTime cap)
      z.external.initial.1 t z.external.start z.external.retained
      (coordinateCap cap) z.external.tail.1 (atomPredicate cap))

namespace OrientedAllCreationPrefixedStoppedCoordinateSpec

def retainedCount
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (_data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (_cap : ℕ) : ℕ :=
  z.external.retainedCount

def start
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (_data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (_cap : ℕ) : Point :=
  z.external.start

def retained
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (_data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (_cap : ℕ) :
    TilingRetainedWord t z.external.start z.external.retainedCount :=
  z.external.retained

def initial
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (_data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (_cap : ℕ) : List Direction :=
  z.external.initial.1

def tail
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (_data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (_cap : ℕ) : List Direction :=
  z.external.tail.1

def distinguished
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (_data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (_cap : ℕ) : Finset Point :=
  supportComplementDistinguished t z.external.start z.external.retained S

theorem card_away_eq_support
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (cap : ℕ) :
    @Fintype.card
      (TilingAwayDomino t (data.start cap) (data.retained cap)
        (data.distinguished cap))
      (instFintypeTilingAwayDomino t (data.start cap) (data.retained cap)
        (data.distinguished cap)) = S.card := by
  exact card_supportAwayDomino t z.external.start z.external.retained S
    data.support_represented

theorem support_card_le_retainedCount_succ
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) :
    S.card ≤ z.external.retainedCount + 1 := by
  calc
    S.card ≤ (tilingExternalDominoBases t z.external.start
      z.external.retained).card := Finset.card_le_card data.support_represented
    _ ≤ (Finset.univ : Finset (Fin (z.external.retainedCount + 1))).card :=
      Finset.card_image_le
    _ = z.external.retainedCount + 1 := by simp

theorem totalCap_le_coordinateCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z) (cap : ℕ) :
    data.totalCap ≤ data.coordinateCap cap := by
  rw [data.coordinateCap_eq]
  have h := data.totalCap_le_capStart
  omega

end OrientedAllCreationPrefixedStoppedCoordinateSpec

/-- One literal prefixed stopped-coordinate fibre for every nonempty exact
`(trace, support)` atom.  All fibres use the same support selector, while
their retained words and away carriers are definitionally fixed by the atom. -/
structure OrientedAllCreationPrefixedStoppedCoordinateFamily
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) where
  fiber : ∀ eta : OrientedAllCreationSupportedAtomIndex t o m k supportAt,
    OrientedAllCreationPrefixedStoppedCoordinateSpec t o m k supportAt
      eta.1.2 eta.1.1

/-- The screen mass with the canonical away-domino enumeration and the
computable Boolean decision procedure fixed explicitly.  This prevents
classical instance choices from leaking into the reusable record type. -/
noncomputable def allCreationBoolScreenMass
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (accepts : ∀ cap, TruncatedTotals (data.upper cap) → Bool)
    (cap : ℕ) : ℝ :=
  @screenMass
    (TilingAwayDomino t (data.start cap) (data.retained cap)
      (data.distinguished cap))
    (instFintypeTilingAwayDomino t (data.start cap) (data.retained cap)
      (data.distinguished cap))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t
      (data.start cap) (data.retained cap) (data.distinguished cap))
    (data.upper cap) (fun ell ↦ accepts cap ell = true)
    (fun ell ↦ instDecidableEqBool (accepts cap ell) true)

/-- The corresponding exact conditional broad-to-narrow product mass. -/
noncomputable def allCreationBoolConditionalScreenMass
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (baseAccepts screenedAccepts :
      ∀ cap, TruncatedTotals (data.upper cap) → Bool)
    (cap : ℕ) : ℝ :=
  @conditionalScreenMass
    (TilingAwayDomino t (data.start cap) (data.retained cap)
      (data.distinguished cap))
    (instFintypeTilingAwayDomino t (data.start cap) (data.retained cap)
      (data.distinguished cap))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t
      (data.start cap) (data.retained cap) (data.distinguished cap))
    (data.upper cap) (fun ell ↦ baseAccepts cap ell = true)
    (fun ell ↦ screenedAccepts cap ell = true)
    (fun ell ↦ instDecidableEqBool (baseAccepts cap ell) true)
    (fun ell ↦ instDecidableEqBool (screenedAccepts cap ell) true)

/-- Semantic broad/narrow data on one shared all-creation stopped atom.  The
finite product field is an exact conditional coordinate estimate. -/
structure OrientedAllCreationConditionalRefinementData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (piece next : Set WalkPath) (cost : ℝ≥0∞) where
  basePredicate : ∀ cap,
    TilingCappedCoordinates (data.retainedCount cap)
      (data.coordinateCap cap) → Prop
  screenedPredicate : ∀ cap,
    TilingCappedCoordinates (data.retainedCount cap)
      (data.coordinateCap cap) → Prop
  base_subset_atom : ∀ cap q, basePredicate cap q → data.atomPredicate cap q
  screened_subset_basePredicate : ∀ cap q,
    screenedPredicate cap q → basePredicate cap q
  baseAccepts : ∀ cap, TruncatedTotals (data.upper cap) → Bool
  screenedAccepts : ∀ cap, TruncatedTotals (data.upper cap) → Bool
  screened_subset_base : ∀ cap ell,
    screenedAccepts cap ell = true → baseAccepts cap ell = true
  base_factorization : ∀ cap q,
    basePredicate cap q ∧
        PrefixedTilingStoppingAccepted (data.stoppingTime cap)
          (data.initial cap) t (data.start cap) (data.retained cap)
          (fun j ↦ (q j : ℕ)) (data.tail cap) ↔
      data.selected cap
          ((splitTilingCoordinatesEquiv t (data.start cap)
            (data.retained cap) (data.distinguished cap) q).1) ∧
        TilingAwayTotalsScreen t (data.start cap) (data.retained cap)
          (data.distinguished cap) (data.upper cap)
          (fun ell ↦ baseAccepts cap ell = true)
          ((splitTilingCoordinatesEquiv t (data.start cap)
            (data.retained cap) (data.distinguished cap) q).2)
  screened_factorization : ∀ cap q,
    screenedPredicate cap q ∧
        PrefixedTilingStoppingAccepted (data.stoppingTime cap)
          (data.initial cap) t (data.start cap) (data.retained cap)
          (fun j ↦ (q j : ℕ)) (data.tail cap) ↔
      data.selected cap
          ((splitTilingCoordinatesEquiv t (data.start cap)
            (data.retained cap) (data.distinguished cap) q).1) ∧
        TilingAwayTotalsScreen t (data.start cap) (data.retained cap)
          (data.distinguished cap) (data.upper cap)
          (fun ell ↦ screenedAccepts cap ell = true)
          ((splitTilingCoordinatesEquiv t (data.start cap)
            (data.retained cap) (data.distinguished cap) q).2)
  base_mass_pos : ∀ cap,
    0 < allCreationBoolScreenMass data baseAccepts cap
  base_subset_piece : ∀ cap,
    walkLift (prefixedTilingPreStoppingFiberEvent (data.stoppingTime cap)
      (data.initial cap) t (data.start cap) (data.retained cap)
      (data.coordinateCap cap) (data.tail cap)
      (basePredicate cap)) ⊆ piece
  monotone_screened : Monotone fun cap ↦
    walkLift (prefixedTilingPreStoppingFiberEvent (data.stoppingTime cap)
      (data.initial cap) t (data.start cap) (data.retained cap)
      (data.coordinateCap cap) (data.tail cap)
      (screenedPredicate cap))
  transition_covered : piece ∩ next ⊆ ⋃ cap,
    walkLift (prefixedTilingPreStoppingFiberEvent (data.stoppingTime cap)
      (data.initial cap) t (data.start cap) (data.retained cap)
      (data.coordinateCap cap) (data.tail cap)
      (screenedPredicate cap))
  product_bound : ∀ cap,
    allCreationBoolConditionalScreenMass data baseAccepts screenedAccepts cap ≤
      cost.toReal

/-- Reuse the common all-creation fibre as the scheduled prefixed conditional
product package. -/
noncomputable def prefixedConditionalFactoredDataOfAllCreation
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (refinement : OrientedAllCreationConditionalRefinementData
      data piece next cost) :
    TilingPrefixedConditionalFactoredStoppedCoordinateData
      (fun _ : Unit ↦ piece) next cost where
  tiling := fun _ _ ↦ t
  retainedCount := fun _ ↦ data.retainedCount
  coordinateCap := fun _ ↦ data.coordinateCap
  initial := fun _ ↦ data.initial
  start := fun _ ↦ data.start
  retained := fun _ ↦ data.retained
  tail := fun _ ↦ data.tail
  stoppingTime := fun _ ↦ data.stoppingTime
  isStoppingTime := fun _ ↦ data.isStoppingTime
  basePredicate := fun _ ↦ refinement.basePredicate
  screenedPredicate := fun _ ↦ refinement.screenedPredicate
  screened_subset_base := fun _ ↦ refinement.screened_subset_basePredicate
  base_subset_piece := fun _ ↦ refinement.base_subset_piece
  distinguished := fun _ ↦ data.distinguished
  selected := fun _ ↦ data.selected
  upper := fun _ ↦ data.upper
  baseAccepts := fun _ ↦ refinement.baseAccepts
  screenedAccepts := fun _ ↦ refinement.screenedAccepts
  screenedAccepts_subset_base := fun _ ↦ refinement.screened_subset_base
  base_factorization := fun _ ↦ refinement.base_factorization
  screened_factorization := fun _ ↦ refinement.screened_factorization
  upper_pos := fun _ ↦ data.upper_pos
  base_mass_ne_zero := fun _ cap ↦ by
    change allCreationBoolScreenMass data refinement.baseAccepts cap ≠ 0
    exact ne_of_gt (refinement.base_mass_pos cap)
  monotone_screened := fun _ ↦ refinement.monotone_screened
  transition_covered := fun _ ↦ refinement.transition_covered
  product_bound := fun _ cap ↦ by
    change allCreationBoolConditionalScreenMass data refinement.baseAccepts
      refinement.screenedAccepts cap ≤ cost.toReal
    exact refinement.product_bound cap

noncomputable def coordinateMassSpecOfAllCreation
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (refinement : OrientedAllCreationConditionalRefinementData
      data piece next cost) :
    CappedCoordinateMassCertificate.CoordinateMassSpec
      (fun _ : Unit ↦ piece) next cost :=
  coordinateMassSpecOfTilingPrefixedConditionalFactoredData
    (prefixedConditionalFactoredDataOfAllCreation data refinement)

end

end Erdos1165.TilingOrientedAllCreationStoppedCoordinate
