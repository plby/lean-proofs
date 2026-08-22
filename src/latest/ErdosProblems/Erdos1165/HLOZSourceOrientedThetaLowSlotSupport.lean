/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSlotSupport

/-!
# Low-external retained-word slots

The low part of Proposition 4.5 is indexed by physical-time slots, but its
one-coordinate product must only expose a base whose retained multiplicity
is below the Proposition 4.4 thick threshold.  Keeping that test in the
support selector prevents the high-coordinate cost from being paid once for
every clock slot.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZSourceOrientedThetaLowSlotSupport

open ExternalProposition44 HLOZGapEstimate HLOZPathEvents
open HLOZSourceOrientedExternalLocalTime
open HLOZSourceOrientedThetaBalance HLOZSourceOrientedThetaCreationSlots
open HLOZSourceOrientedThetaSlotSupport LazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedRetainedSourceLocalTime
open TilingOrientedShellZeroSourcePartition
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

local instance {t : DominoTiling} :
    MeasurableSpace (OrientedTilingTypedExternalWordCode t) := ⊤

local instance {t : DominoTiling} :
    MeasurableSingletonClass (OrientedTilingTypedExternalWordCode t) :=
  ⟨fun _ ↦ trivial⟩

/-- A clock slot exposes its represented base precisely in the low-external
regime. -/
def lowFilteredSlotSupportOfCode (t : DominoTiling) (o : Orientation)
    (m : ℕ) (slot : Fin (hlozCutoff44 m + 1))
    (z : OrientedTilingTypedExternalWordCode t) : Finset Point :=
  match finsetSlot (orientedThetaCodeBases t o z) slot with
  | some b =>
      if orientedThetaCodeExternalCount t z b < hlozThickLevel44 m then
        {b}
      else
        ∅
  | none => ∅

def lowFilteredSlotSupportAt (t : DominoTiling) (o : Orientation)
    (m : ℕ) (slot : Fin (hlozCutoff44 m + 1))
    (s : WalkPath) (n : ℕ) : Finset Point :=
  lowFilteredSlotSupportOfCode t o m slot
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

theorem lowFilteredSlotSupportData (t : DominoTiling) (o : Orientation)
    (m k : ℕ) (slot : Fin (hlozCutoff44 m + 1)) :
    OrientedAllCreationSupportSelectorData t o m k
      (lowFilteredSlotSupportAt t o m slot) where
  measurableAtCreation :=
    (measurable_of_countable (lowFilteredSlotSupportOfCode t o m slot)).comp
      (measurable_externalCodeAtCreation t o m k)
  prefix_invariant := by
    intro s s' n hp
    unfold lowFilteredSlotSupportAt
    rw [fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp]
  represented := by
    intro s n _hvalid b hb
    unfold lowFilteredSlotSupportAt lowFilteredSlotSupportOfCode at hb
    split at hb
    next x hx =>
      split at hb
      next hlow =>
        simp only [Finset.mem_singleton] at hb
        subst x
        exact (mem_orientedThetaCodeBases_iff.mp
          (finsetSlot_eq_some_mem hx)).1
      next hhigh => simp at hb
    next hx => simp at hb

/-- A physical low restricted-Theta slot selects the same singleton on its
retained creation code. -/
theorem lowFilteredSlotSupportAt_creation_eq_singleton
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {w externalLow externalHigh : ℕ}
    {slot : Fin (hlozCutoff44 m + 1)} {s : WalkPath} {b : Point}
    (hvalid : s ∈ (validStepWalk : Set WalkPath))
    (hcreation : 0 < creationTimeNat m k s)
    (hslot : finsetSlot (orientedThetaCreationBases t o m k s) slot =
      some b)
    (hlow : b ∈ orientedRestrictedThetaLowAtCreation
      t o m k w externalLow externalHigh s) :
    lowFilteredSlotSupportAt t o m slot s (creationTimeNat m k s) =
      {b} := by
  classical
  have hbcode := finsetSlot_eq_some_mem hslot
  have hrepresented := (mem_orientedThetaCodeBases_iff.mp hbcode).1
  have hcompat := (mem_orientedThetaCodeBases_iff.mp hbcode).2
  have hcard :=
    card_tilingCoordinatesAt_fixedOrientedTypedExternalWordCode_eq_source
      t o s (creationTimeNat m k s) hvalid hcreation
        ⟨b, hrepresented⟩ hcompat
  have hlowSource : tilingSourceExternalBaseLocalTime t o s
      (creationTimeNat m k s) b < hlozThickLevel44 m :=
    (Finset.mem_filter.mp hlow).2
  have hlowCode : orientedThetaCodeExternalCount t
      (fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s) b <
        hlozThickLevel44 m := by
    simpa [orientedThetaCodeExternalCount, hrepresented, hcard] using
      hlowSource
  unfold lowFilteredSlotSupportAt lowFilteredSlotSupportOfCode
  unfold orientedThetaCreationBases at hslot
  simp [hslot, hlowCode]

/-- Membership in a nonempty filtered support records the low-external code
inequality, independently of any physical path. -/
theorem externalCount_lt_of_mem_lowFilteredSlotSupportOfCode
    {t : DominoTiling} {o : Orientation} {m : ℕ}
    {slot : Fin (hlozCutoff44 m + 1)}
    {z : OrientedTilingTypedExternalWordCode t} {b : Point}
    (hb : b ∈ lowFilteredSlotSupportOfCode t o m slot z) :
    orientedThetaCodeExternalCount t z b < hlozThickLevel44 m := by
  unfold lowFilteredSlotSupportOfCode at hb
  split at hb
  next x hx =>
    split at hb
    next hlow =>
      simp only [Finset.mem_singleton] at hb
      subst x
      exact hlow
    next hhigh => simp at hb
  next hx => simp at hb

end

end Erdos1165.HLOZSourceOrientedThetaLowSlotSupport
