/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaCreationSlots
import ErdosProblems.Erdos1165.TilingOrientedExternalAllCreationStoppedCoordinate

/-!
# One-coordinate stopped supports for the oriented Theta slots

For a fixed retained-word slot, only the selected domino is exposed as an
away coordinate.  Every other represented domino stays in the distinguished
carrier.  The selector below is a literal function of the oriented retained
word at the creation clock, hence it is stopped-prefix observable and is
represented by that same word.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZSourceOrientedThetaSlotSupport

open ExternalProposition44 HLOZGapEstimate HLOZPathEvents
open HLOZSourceOrientedThetaCreationSlots LazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

local instance {t : DominoTiling} :
    MeasurableSpace (OrientedTilingTypedExternalWordCode t) := ⊤

local instance {t : DominoTiling} :
    MeasurableSingletonClass (OrientedTilingTypedExternalWordCode t) :=
  ⟨fun _ ↦ trivial⟩

/-- Singleton support selected by a high-external retained-word slot. -/
def highSlotSupportOfCode (t : DominoTiling) (o : Orientation) (m : ℕ)
    (slot : Fin (hlozSiteBudget44 m))
    (z : OrientedTilingTypedExternalWordCode t) : Finset Point :=
  match finsetSlot (orientedThetaCodeCandidateSites44 t o m z) slot with
  | some b => {b}
  | none => ∅

/-- Singleton support selected by a low-external retained-word slot. -/
def lowSlotSupportOfCode (t : DominoTiling) (o : Orientation) (m : ℕ)
    (slot : Fin (hlozCutoff44 m + 1))
    (z : OrientedTilingTypedExternalWordCode t) : Finset Point :=
  match finsetSlot (orientedThetaCodeBases t o z) slot with
  | some b => {b}
  | none => ∅

def highSlotSupportAt (t : DominoTiling) (o : Orientation) (m : ℕ)
    (slot : Fin (hlozSiteBudget44 m)) (s : WalkPath) (n : ℕ) :
    Finset Point :=
  highSlotSupportOfCode t o m slot
    (fixedOrientedTypedExternalWordCode t o n s)

def lowSlotSupportAt (t : DominoTiling) (o : Orientation) (m : ℕ)
    (slot : Fin (hlozCutoff44 m + 1)) (s : WalkPath) (n : ℕ) :
    Finset Point :=
  lowSlotSupportOfCode t o m slot
    (fixedOrientedTypedExternalWordCode t o n s)

private theorem measurable_externalCodeAtCreation
    (t : DominoTiling) (o : Orientation) (m k : ℕ) :
    Measurable fun s ↦ fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k s) s := by
  exact measurable_natIndexed (creationTimeNat m k)
    (measurable_creationTimeNat m k)
    (fixedOrientedTypedExternalWordCode t o)
    (fun n ↦ measurable_of_pathPrefix_invariant n _
      (fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o))

theorem highSlotSupportData (t : DominoTiling) (o : Orientation)
    (m k : ℕ) (slot : Fin (hlozSiteBudget44 m)) :
    OrientedAllCreationSupportSelectorData t o m k
      (highSlotSupportAt t o m slot) where
  measurableAtCreation :=
    (measurable_of_countable (highSlotSupportOfCode t o m slot)).comp
      (measurable_externalCodeAtCreation t o m k)
  prefix_invariant := by
    intro s s' n hp
    unfold highSlotSupportAt
    rw [fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp]
  represented := by
    intro s n _hvalid b hb
    unfold highSlotSupportAt highSlotSupportOfCode at hb
    split at hb
    next x hx =>
      simp only [Finset.mem_singleton] at hb
      subst x
      exact (mem_orientedThetaCodeCandidateSites44_iff.mp
        (finsetSlot_eq_some_mem hx)).choose
    next hx => simp at hb

theorem lowSlotSupportData (t : DominoTiling) (o : Orientation)
    (m k : ℕ) (slot : Fin (hlozCutoff44 m + 1)) :
    OrientedAllCreationSupportSelectorData t o m k
      (lowSlotSupportAt t o m slot) where
  measurableAtCreation :=
    (measurable_of_countable (lowSlotSupportOfCode t o m slot)).comp
      (measurable_externalCodeAtCreation t o m k)
  prefix_invariant := by
    intro s s' n hp
    unfold lowSlotSupportAt
    rw [fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp]
  represented := by
    intro s n _hvalid b hb
    unfold lowSlotSupportAt lowSlotSupportOfCode at hb
    split at hb
    next x hx =>
      simp only [Finset.mem_singleton] at hb
      subst x
      exact (mem_orientedThetaCodeBases_iff.mp
        (finsetSlot_eq_some_mem hx)).1
    next hx => simp at hb

theorem highSlotSupportAt_creation_eq_singleton
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {slot : Fin (hlozSiteBudget44 m)} {s : WalkPath} {b : Point}
    (hslot : finsetSlot
      (orientedThetaCreationCandidateSites44 t o m k s) slot = some b) :
    highSlotSupportAt t o m slot s (creationTimeNat m k s) = {b} := by
  unfold highSlotSupportAt highSlotSupportOfCode
  change (match finsetSlot
      (orientedThetaCreationCandidateSites44 t o m k s) slot with
    | some x => {x}
    | none => ∅) = {b}
  rw [hslot]

theorem lowSlotSupportAt_creation_eq_singleton
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {slot : Fin (hlozCutoff44 m + 1)} {s : WalkPath} {b : Point}
    (hslot : finsetSlot (orientedThetaCreationBases t o m k s) slot = some b) :
    lowSlotSupportAt t o m slot s (creationTimeNat m k s) = {b} := by
  unfold lowSlotSupportAt lowSlotSupportOfCode
  change (match finsetSlot (orientedThetaCreationBases t o m k s) slot with
    | some x => {x}
    | none => ∅) = {b}
  rw [hslot]

end

end Erdos1165.HLOZSourceOrientedThetaSlotSupport
