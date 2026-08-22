/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49Observability

/-!
# Fixed-creation observability of arbitrary prefixed all-creation screens

The cylinder argument used by the canonical Proposition 4.9 screen depends
only on the common prefixed stopped-coordinate specification, not on the
particular coordinate predicate.  This module exposes that reusable fact.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZPrefixedAllCreationScreenObservability

open HLOZPathEvents
open HLOZPrefixedCanonicalSourceProp49Observability
open HLOZSpatialAdapter
open LazyDecomposition PreStoppingFiber StoppedInsertion
open SpatialInsertionFiber
open TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A prefixed stopped screen built on a concrete all-creation coordinate
specification. -/
def allCreationScreenFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (cap : ℕ)
    (predicate : TilingCappedCoordinates z.external.retainedCount
      (fiber.coordinateCap cap) → Prop) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    (fiber.stoppingTime cap) (fiber.initial cap) t (fiber.start cap)
    (fiber.retained cap) (fiber.coordinateCap cap) (fiber.tail cap) predicate)

private theorem allCreationScreenFiber_preimage_of_stepPrefix_eq
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (cap : ℕ)
    (predicate : TilingCappedCoordinates z.external.retainedCount
      (fiber.coordinateCap cap) → Prop)
    (hstopping : fiber.stoppingTime cap = truncatedLevelTime m k
      (orientedAllCreationCoordinateCutoff z (fiber.coordinateCap cap)))
    {omega omega' : StepPath}
    (hp : stepPrefix n omega = stepPrefix n omega')
    (hcreation : ThresholdCreation (trajectory omega) m k n)
    (_hcreation' : ThresholdCreation (trajectory omega') m k n) :
    trajectory omega ∈ allCreationScreenFiber fiber cap predicate →
      trajectory omega' ∈ allCreationScreenFiber fiber cap predicate := by
  let initial := fiber.initial cap
  let start := fiber.start cap
  let retained := fiber.retained cap
  let coordinateCap := fiber.coordinateCap cap
  let tail := fiber.tail cap
  have hlt (q : TilingCappedCoordinates z.external.retainedCount
      coordinateCap) :
      (prefixedTilingInsertionPrefixList initial t start retained
        (fun j ↦ (q j : ℕ)) tail).length <
        orientedAllCreationCoordinateCutoff z coordinateCap := by
    simpa only [initial, start, retained, coordinateCap, tail,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.initial,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.tail] using
      prefixedInsertion_lt_orientedAllCreationCoordinateCutoff z
        coordinateCap q
  intro homega
  have hraw : omega ∈ prefixedTilingPreStoppingFiberEvent
      (fiber.stoppingTime cap) initial t start retained coordinateCap tail
        predicate := by
    simpa only [allCreationScreenFiber, walkLift, Set.mem_inter_iff,
      trajectory_mem_validStepWalk, true_and, Set.mem_preimage,
      stepsOfWalk_trajectory] using homega
  rcases Set.mem_iUnion.mp hraw with ⟨q, hq⟩
  let v := prefixedTilingInsertionPrefixList initial t start retained
    (fun j ↦ (q.1 j : ℕ)) tail
  have hstop : fiber.stoppingTime cap omega = v.length := hq.1
  have hvCreation : ThresholdCreation (trajectory omega) m k v.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff z coordinateCap)
        v.length omega (hlt q.1)).mp
    rw [hstopping] at hstop
    exact hstop
  have hvn : v.length = n := thresholdCreation_time_unique hvCreation hcreation
  have hq' : omega' ∈ prefixedTilingStoppedInsertionAtom
      (fiber.stoppingTime cap) initial t start retained
        (fun j ↦ (q.1 j : ℕ)) tail := by
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      (fiber.isStoppingTime cap) initial t start retained
        (fun j ↦ (q.1 j : ℕ)) tail q.2.2]
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      (fiber.isStoppingTime cap) initial t start retained
        (fun j ↦ (q.1 j : ℕ)) tail q.2.2] at hq
    calc
      stepPrefix v.length omega' = stepPrefix v.length omega := by
        rw [hvn]
        exact hp.symm
      _ = directionVectorOfList v := hq
  have hraw' : omega' ∈ prefixedTilingPreStoppingFiberEvent
      (fiber.stoppingTime cap) initial t start retained coordinateCap tail
        predicate := Set.mem_iUnion.mpr ⟨q, hq'⟩
  simpa only [allCreationScreenFiber, walkLift, Set.mem_inter_iff,
    trajectory_mem_validStepWalk, true_and, Set.mem_preimage,
    stepsOfWalk_trajectory] using hraw'

theorem allCreationScreenFiber_preimage_iff_of_stepPrefix_eq
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (cap : ℕ)
    (predicate : TilingCappedCoordinates z.external.retainedCount
      (fiber.coordinateCap cap) → Prop)
    (hstopping : fiber.stoppingTime cap = truncatedLevelTime m k
      (orientedAllCreationCoordinateCutoff z (fiber.coordinateCap cap)))
    {omega omega' : StepPath}
    (hp : stepPrefix n omega = stepPrefix n omega')
    (hcreation : ThresholdCreation (trajectory omega) m k n)
    (hcreation' : ThresholdCreation (trajectory omega') m k n) :
    trajectory omega ∈ allCreationScreenFiber fiber cap predicate ↔
      trajectory omega' ∈ allCreationScreenFiber fiber cap predicate :=
  ⟨allCreationScreenFiber_preimage_of_stepPrefix_eq fiber cap predicate hstopping hp
      hcreation hcreation',
    allCreationScreenFiber_preimage_of_stepPrefix_eq fiber cap predicate hstopping hp.symm
      hcreation' hcreation⟩

/-- Every predicate on a prefixed all-creation coordinate vector is
observable after intersecting its screen with a fixed rank-creation atom. -/
theorem allCreationScreenFiber_fixedCreation_observable
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (cap : ℕ)
    (predicate : TilingCappedCoordinates z.external.retainedCount
      (fiber.coordinateCap cap) → Prop)
    (hstopping : fiber.stoppingTime cap = truncatedLevelTime m k
      (orientedAllCreationCoordinateCutoff z (fiber.coordinateCap cap))) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      {omega | ThresholdCreation (trajectory omega) m k n ∧
        trajectory omega ∈ allCreationScreenFiber fiber cap predicate} := by
  apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
  apply measurableSet_incrementFiltration_of_stepPrefix_dependent n
  intro omega omega' hp
  have hpPath : pathPrefix (trajectory omega) n =
      pathPrefix (trajectory omega') n := by
    simpa only [trajectoryPrefix_stepPrefix] using congrArg trajectoryPrefix hp
  have hcreationIff :=
    TilingDistinguishedTraceInvariant.thresholdCreation_iff_of_pathPrefix_eq
      (m := m) (rank := k) hpPath le_rfl
  constructor
  · rintro ⟨hcreation, hscreen⟩
    have hcreation' := hcreationIff.mp hcreation
    exact ⟨hcreation',
      (allCreationScreenFiber_preimage_iff_of_stepPrefix_eq fiber cap predicate
        hstopping hp hcreation hcreation').mp hscreen⟩
  · rintro ⟨hcreation', hscreen'⟩
    have hcreation := hcreationIff.mpr hcreation'
    exact ⟨hcreation,
      (allCreationScreenFiber_preimage_iff_of_stepPrefix_eq fiber cap predicate
        hstopping hp hcreation hcreation').mpr hscreen'⟩

end

end Erdos1165.HLOZPrefixedAllCreationScreenObservability
