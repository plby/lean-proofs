/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedExternalAllCreationStoppedCoordinate

/-!
# Accepted stopped-history marginals for source-Theta slots

An unconditional sum of distinguished-coordinate carriers is not a valid
normalization for the source part of Proposition 4.5: after the retained
external word has been fixed, arbitrary away totals need not preserve the
creation rank.  This file records the normalization that is safe to sum.

Each history has a *full accepted stopped atom*.  The bad event is a subset
of that atom, and its conditional cost is proved from literal finite
coordinate masses before converting back to walk measure.  The accepted
atoms, rather than the projected retained-word cylinders, are required to be
pairwise disjoint.  Thus the global theorem is an ordinary disjoint stopped
history marginalization and never sums a bare screen cost over histories.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaAcceptedSourceSlotMarginal

open TilingSpatialInsertionFiber
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingPrefixedStoppedProductDisintegration
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-! ## One accepted stopped-history atom -/

/-- Coordinate-mass certificate on one full accepted stopped-history atom.

`commonFactor` contains the fixed physical-prefix cylinder mass.
`acceptedCoordinateMass` retains the complete accepted-coordinate
denominator.  In particular it is not replaced by the unconditional mass of
all truncated away totals. -/
structure AcceptedSourceSlotMarginalAtom (ratio : ℝ≥0∞) where
  accepted : Set WalkPath
  bad : Set WalkPath
  accepted_measurable : MeasurableSet accepted
  bad_measurable : MeasurableSet bad
  bad_subset : bad ⊆ accepted
  commonFactor : ℝ≥0∞
  acceptedCoordinateMass : ℝ≥0∞
  badCoordinateMass : ℝ≥0∞
  accepted_mass_eq :
    simpleRandomWalk accepted = commonFactor * acceptedCoordinateMass
  bad_mass_eq :
    simpleRandomWalk bad = commonFactor * badCoordinateMass
  coordinate_ratio : badCoordinateMass ≤ ratio * acceptedCoordinateMass

namespace AcceptedSourceSlotMarginalAtom

/-- The natural same-rank cutoff is not in the existing half-mass regime at
the HLOZ center.  If the retained external count is `15 n` and the total
local-time level is `16 n`, then the safe inserted-total range has length
only `n`; the first-moment truncation hypothesis would demand `30 n ≤ 15 n`.
This is why the unconditional carrier estimate cannot simply be divided by
a same-rank accepted mass. -/
theorem centeredSafeUpper_not_halfMassRegime (n : ℕ) (hn : 0 < n) :
    ¬2 * (15 * n) ≤ 15 * ((16 * n) - (15 * n)) := by
  omega

/-- The literal finite-coordinate comparison gives the conditional estimate
on one accepted stopped-history atom. -/
theorem measure_bad_le
    {ratio : ℝ≥0∞} (atom : AcceptedSourceSlotMarginalAtom ratio) :
    simpleRandomWalk atom.bad ≤ ratio * simpleRandomWalk atom.accepted := by
  rw [atom.bad_mass_eq, atom.accepted_mass_eq]
  calc
    atom.commonFactor * atom.badCoordinateMass ≤
        atom.commonFactor * (ratio * atom.acceptedCoordinateMass) := by
      exact mul_le_mul_of_nonneg_left atom.coordinate_ratio bot_le
    _ = ratio *
        (atom.commonFactor * atom.acceptedCoordinateMass) := by
      ac_rfl

/-- Build one marginal atom directly from the checked physical-prefix
stopped-product law.  The only inequality supplied here is between explicit
finite geometric coordinate masses; no event-probability comparison is an
input. -/
noncomputable def ofPrefixedGeometricMass
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (cap : ℕ) (tail : List Direction)
    (acceptedPredicate badPredicate :
      TilingCappedCoordinates i cap → Prop)
    (hbad : ∀ q, badPredicate q → acceptedPredicate q)
    (ratio : ℝ≥0∞)
    (hcoordinate :
      ENNReal.ofReal
          (prefixedTilingStoppedAcceptedGeometricMass τ initial t x r cap tail
            badPredicate) ≤
        ratio * ENNReal.ofReal
          (prefixedTilingStoppedAcceptedGeometricMass τ initial t x r cap tail
            acceptedPredicate)) :
    AcceptedSourceSlotMarginalAtom ratio where
  accepted := walkLift (prefixedTilingPreStoppingFiberEvent
    τ initial t x r cap tail acceptedPredicate)
  bad := walkLift (prefixedTilingPreStoppingFiberEvent
    τ initial t x r cap tail badPredicate)
  accepted_measurable := measurableSet_walkLift
    (measurableSet_prefixedTilingPreStoppingFiberEvent
      hτ initial t x r cap tail acceptedPredicate)
  bad_measurable := measurableSet_walkLift
    (measurableSet_prefixedTilingPreStoppingFiberEvent
      hτ initial t x r cap tail badPredicate)
  bad_subset := by
    intro s hs
    rcases hs with ⟨hvalid, hs⟩
    exact ⟨hvalid,
      prefixedTilingPreStoppingFiberEvent_mono τ initial t x r tail hbad hs⟩
  commonFactor := ENNReal.ofReal (prefixedPrefixFiberConstant initial i tail)
  acceptedCoordinateMass := ENNReal.ofReal
    (prefixedTilingStoppedAcceptedGeometricMass τ initial t x r cap tail
      acceptedPredicate)
  badCoordinateMass := ENNReal.ofReal
    (prefixedTilingStoppedAcceptedGeometricMass τ initial t x r cap tail
      badPredicate)
  accepted_mass_eq := by
    rw [simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent hτ]
    rw [ENNReal.ofReal_mul (prefixedPrefixFiberConstant_nonneg initial i tail)]
  bad_mass_eq := by
    rw [simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent hτ]
    rw [ENNReal.ofReal_mul (prefixedPrefixFiberConstant_nonneg initial i tail)]
  coordinate_ratio := hcoordinate

end AcceptedSourceSlotMarginalAtom

/-! ## Countable disjoint stopped-history marginalization -/

/-- Source-slot marginal data indexed by complete stopped histories.

The accepted atoms may cover only the part of `stage` relevant to this
source row.  Exact equality with `stage` is unnecessary; containment is the
direction used by the probability bound. -/
structure AcceptedSourceSlotMarginalData
    (History : Type*) [Countable History]
    (event stage : Set WalkPath) (ratio : ℝ≥0∞) where
  atom : History → AcceptedSourceSlotMarginalAtom ratio
  accepted_pairwise : Pairwise fun h h' ↦
    Disjoint (atom h).accepted (atom h').accepted
  event_subset : event ⊆ ⋃ h, (atom h).bad
  accepted_union_subset : (⋃ h, (atom h).accepted) ⊆ stage

namespace AcceptedSourceSlotMarginalData

/-- Direct conditional-ratio summation over disjoint full stopped atoms. -/
theorem measure_event_le
    {History : Type*} [Countable History]
    {event stage : Set WalkPath} {ratio : ℝ≥0∞}
    (data : AcceptedSourceSlotMarginalData History event stage ratio) :
    simpleRandomWalk event ≤ ratio * simpleRandomWalk stage := by
  calc
    simpleRandomWalk event ≤
        simpleRandomWalk (⋃ h, (data.atom h).bad) :=
      measure_mono data.event_subset
    _ ≤ ∑' h, simpleRandomWalk (data.atom h).bad :=
      measure_iUnion_le _
    _ ≤ ∑' h, ratio * simpleRandomWalk (data.atom h).accepted := by
      exact ENNReal.tsum_le_tsum fun h ↦ (data.atom h).measure_bad_le
    _ = ratio * ∑' h, simpleRandomWalk (data.atom h).accepted := by
      rw [ENNReal.tsum_mul_left]
    _ = ratio * simpleRandomWalk (⋃ h, (data.atom h).accepted) := by
      rw [measure_iUnion data.accepted_pairwise
        (fun h ↦ (data.atom h).accepted_measurable)]
    _ ≤ ratio * simpleRandomWalk stage := by
      exact mul_le_mul_of_nonneg_left
        (measure_mono data.accepted_union_subset) bot_le

/-- Probability-measure specialization when no smaller preceding stage is
needed. -/
theorem measure_event_le_ratio
    {History : Type*} [Countable History]
    {event stage : Set WalkPath} {ratio : ℝ≥0∞}
    (data : AcceptedSourceSlotMarginalData History event stage ratio) :
    simpleRandomWalk event ≤ ratio := by
  calc
    simpleRandomWalk event ≤ ratio * simpleRandomWalk stage :=
      data.measure_event_le
    _ ≤ ratio * simpleRandomWalk Set.univ := by
      exact mul_le_mul_of_nonneg_left
        (measure_mono (Set.subset_univ stage)) bot_le
    _ = ratio := by simp

end AcceptedSourceSlotMarginalData

/-! ## External creation atoms at one cap -/

/-- The exact external-word/support creation atoms are pairwise disjoint.
This remains true although each atom is a union over current-favorite data:
the external code and the support are still fixed pathwise. -/
theorem externalCreationAtoms_pairwiseDisjoint
    (t : DominoTiling) (o : LazyDecomposition.Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) :
    Pairwise fun eta eta' : SupportedIndex t o m k supportAt ↦
      Disjoint
        (orientedExternalAllCreationSupportTraceAtom
          t o m k supportAt eta.1.1 eta.1.2)
        (orientedExternalAllCreationSupportTraceAtom
          t o m k supportAt eta'.1.1 eta'.1.2) := by
  intro eta eta' hne
  rw [Set.disjoint_left]
  intro s hs hs'
  rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs hs'
  apply hne
  apply Subtype.ext
  apply Prod.ext
  · exact hs.2.2.1.symm.trans hs'.2.2.1
  · exact hs.2.2.2.symm.trans hs'.2.2.2

/-- The countable union of exact nonempty external-word/support atoms at one
creation rank. -/
def externalCreationStage
    (t : DominoTiling) (o : LazyDecomposition.Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) : Set WalkPath :=
  ⋃ eta : SupportedIndex t o m k supportAt,
    orientedExternalAllCreationSupportTraceAtom
      t o m k supportAt eta.1.1 eta.1.2

/-- Build the accepted marginal at one coordinate cap from literal external
stopped fibres.  Histories are the exact external-code/support atoms.  The
cap is fixed here; a cofinal application should take a monotone union in
`cap`, not assert disjointness between different caps. -/
noncomputable def externalStoppedFiberMarginalDataAtCap
    {t : DominoTiling} {o : LazyDecomposition.Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (data : ∀ eta : SupportedIndex t o m k supportAt,
      Spec t o m k supportAt eta.1.2 eta.1.1)
    (cap : ℕ)
    (acceptedPredicate badPredicate : ∀ eta,
      TilingCappedCoordinates eta.1.1.retainedCount
        ((data eta).coordinateCap cap) → Prop)
    (hbad : ∀ eta q, badPredicate eta q → acceptedPredicate eta q)
    (hacceptedAtom : ∀ eta q,
      acceptedPredicate eta q → (data eta).atomPredicate cap q)
    (ratio : ℝ≥0∞)
    (hcoordinate : ∀ eta,
      ENNReal.ofReal
          (prefixedTilingStoppedAcceptedGeometricMass
            ((data eta).stoppingTime cap) eta.1.1.initial.1 t eta.1.1.start
            eta.1.1.retained ((data eta).coordinateCap cap) eta.1.1.tail.1
            (badPredicate eta)) ≤
        ratio * ENNReal.ofReal
          (prefixedTilingStoppedAcceptedGeometricMass
            ((data eta).stoppingTime cap) eta.1.1.initial.1 t eta.1.1.start
            eta.1.1.retained ((data eta).coordinateCap cap) eta.1.1.tail.1
            (acceptedPredicate eta)))
    (event : Set WalkPath)
    (hcover : event ⊆ ⋃ eta : SupportedIndex t o m k supportAt,
      walkLift (prefixedTilingPreStoppingFiberEvent
        ((data eta).stoppingTime cap) eta.1.1.initial.1 t eta.1.1.start
        eta.1.1.retained ((data eta).coordinateCap cap) eta.1.1.tail.1
        (badPredicate eta))) :
    AcceptedSourceSlotMarginalData
      (SupportedIndex t o m k supportAt) event
      (externalCreationStage t o m k supportAt) ratio where
  atom := fun eta ↦
    AcceptedSourceSlotMarginalAtom.ofPrefixedGeometricMass
      ((data eta).isStoppingTime cap) eta.1.1.initial.1 t eta.1.1.start
      eta.1.1.retained ((data eta).coordinateCap cap) eta.1.1.tail.1
      (acceptedPredicate eta) (badPredicate eta) (hbad eta) ratio
      (hcoordinate eta)
  accepted_pairwise := by
    intro eta eta' hne
    apply (externalCreationAtoms_pairwiseDisjoint
      t o m k supportAt hne).mono
    · intro s hs
      rcases hs with ⟨hvalid, hs⟩
      apply (data eta).atom_sound cap
      exact ⟨hvalid, prefixedTilingPreStoppingFiberEvent_mono
        ((data eta).stoppingTime cap) eta.1.1.initial.1 t eta.1.1.start
        eta.1.1.retained eta.1.1.tail.1 (hacceptedAtom eta) hs⟩
    · intro s hs
      rcases hs with ⟨hvalid, hs⟩
      apply (data eta').atom_sound cap
      exact ⟨hvalid, prefixedTilingPreStoppingFiberEvent_mono
        ((data eta').stoppingTime cap) eta'.1.1.initial.1 t eta'.1.1.start
        eta'.1.1.retained eta'.1.1.tail.1 (hacceptedAtom eta') hs⟩
  event_subset := hcover
  accepted_union_subset := by
    intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨eta, hs⟩
    apply Set.mem_iUnion.mpr
    rcases hs with ⟨hvalid, hs⟩
    refine ⟨eta, (data eta).atom_sound cap ⟨hvalid, ?_⟩⟩
    exact prefixedTilingPreStoppingFiberEvent_mono
      ((data eta).stoppingTime cap) eta.1.1.initial.1 t eta.1.1.start
      eta.1.1.retained eta.1.1.tail.1 (hacceptedAtom eta) hs

/-! ## Cofinal cap removal -/

/-- A monotone cap family of accepted stopped-history marginals.  The
history partition is allowed to be rebuilt at each cap; disjointness is used
only within a fixed cap. -/
structure MonotoneAcceptedSourceSlotMarginalData
    (History : Type*) [Countable History]
    (eventCap : ℕ → Set WalkPath) (stage : Set WalkPath) (ratio : ℝ≥0∞) where
  capData : ∀ cap,
    AcceptedSourceSlotMarginalData History (eventCap cap) stage ratio
  event_monotone : Monotone eventCap

namespace MonotoneAcceptedSourceSlotMarginalData

def event
    {History : Type*} [Countable History]
    {eventCap : ℕ → Set WalkPath} {stage : Set WalkPath} {ratio : ℝ≥0∞}
    (_data : MonotoneAcceptedSourceSlotMarginalData
      History eventCap stage ratio) : Set WalkPath :=
  ⋃ cap, eventCap cap

/-- Uniform conditional bounds pass to the cofinal cap union by continuity
from below. -/
theorem measure_event_le
    {History : Type*} [Countable History]
    {eventCap : ℕ → Set WalkPath} {stage : Set WalkPath} {ratio : ℝ≥0∞}
    (data : MonotoneAcceptedSourceSlotMarginalData
      History eventCap stage ratio) :
    simpleRandomWalk data.event ≤ ratio * simpleRandomWalk stage := by
  have hlim := tendsto_measure_iUnion_atTop
    (μ := simpleRandomWalk) data.event_monotone
  apply le_of_tendsto hlim
  filter_upwards [] with cap
  exact (data.capData cap).measure_event_le

theorem measure_event_le_ratio
    {History : Type*} [Countable History]
    {eventCap : ℕ → Set WalkPath} {stage : Set WalkPath} {ratio : ℝ≥0∞}
    (data : MonotoneAcceptedSourceSlotMarginalData
      History eventCap stage ratio) :
    simpleRandomWalk data.event ≤ ratio := by
  calc
    simpleRandomWalk data.event ≤ ratio * simpleRandomWalk stage :=
      data.measure_event_le
    _ ≤ ratio * simpleRandomWalk Set.univ := by
      exact mul_le_mul_of_nonneg_left
        (measure_mono (Set.subset_univ stage)) bot_le
    _ = ratio := by simp

end MonotoneAcceptedSourceSlotMarginalData

end

end Erdos1165.HLOZSourceOrientedThetaAcceptedSourceSlotMarginal
