/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedExternalAllCreationStoppedCoordinate

/-!
# External creation fibres with every represented domino away

For the absolute `Theta` estimate the finite product must see every domino
represented by the retained external word.  This module uses the literal
represented-base set as the support selector.  Its distinguished complement
is therefore empty, while the creation atom still fixes only the oriented
external word and sums honestly over current-favorite data.
-/

open MeasureTheory Set

namespace Erdos1165.TilingOrientedAllRepresentedExternalFiber

open HLOZPathEvents LazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

local instance {t : DominoTiling} :
    MeasurableSpace (OrientedTilingTypedExternalWordCode t) := ⊤

local instance {t : DominoTiling} :
    MeasurableSingletonClass (OrientedTilingTypedExternalWordCode t) :=
  ⟨fun _ ↦ trivial⟩

/-- Every base represented by the oriented retained external word. -/
def allRepresentedSupportAt (t : DominoTiling) (o : Orientation)
    (s : WalkPath) (n : ℕ) : Finset Point :=
  let z := fixedOrientedTypedExternalWordCode t o n s
  tilingExternalDominoBases t z.start z.retained

/-- The represented-base selector is a stopped-prefix observable and is
tautologically represented by its own retained word. -/
theorem allRepresentedSupportData
    (t : DominoTiling) (o : Orientation) (m k : ℕ) :
    OrientedAllCreationSupportSelectorData t o m k
      (allRepresentedSupportAt t o) where
  measurableAtCreation := by
    let externalAtCreation : WalkPath → OrientedTilingTypedExternalWordCode t :=
      fun s ↦ fixedOrientedTypedExternalWordCode t o
        (creationTimeNat m k s) s
    have hexternal : Measurable externalAtCreation := by
      exact measurable_natIndexed (creationTimeNat m k)
        (measurable_creationTimeNat m k)
        (fixedOrientedTypedExternalWordCode t o)
        (fun n ↦ measurable_of_pathPrefix_invariant n _
          (fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o))
    let represented : OrientedTilingTypedExternalWordCode t → Finset Point :=
      fun z ↦ tilingExternalDominoBases t z.start z.retained
    exact (measurable_of_countable represented).comp hexternal
  prefix_invariant := by
    intro s s' n hp
    unfold allRepresentedSupportAt
    rw [fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp]
  represented := by
    intro s n _hvalid
    exact Finset.Subset.rfl

/-- The exact valid rank-creation atom fixing only the physical oriented
external word. -/
def allRepresentedExternalCreationTraceAtom
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) : Set WalkPath :=
  {s | s ∈ validStepWalk ∧ ReachesThreshold s m k ∧
    fixedOrientedTypedExternalWordCode t o (creationTimeNat m k s) s = z}

theorem allRepresentedExternalCreationTraceAtom_eq_supportAtom
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (z : OrientedTilingTypedExternalWordCode t) :
    allRepresentedExternalCreationTraceAtom t o m k z =
      orientedExternalAllCreationSupportTraceAtom t o m k
        (allRepresentedSupportAt t o) z
        (tilingExternalDominoBases t z.start z.retained) := by
  rw [orientedExternalAllCreationSupportTraceAtom_eq]
  ext s
  simp only [allRepresentedExternalCreationTraceAtom, Set.mem_ofPred_eq,
    allRepresentedSupportAt]
  constructor
  · rintro ⟨hvalid, hreach, hcode⟩
    refine ⟨hvalid, hreach, hcode, ?_⟩
    rw [hcode]
  · rintro ⟨hvalid, hreach, hcode, _hsupport⟩
    exact ⟨hvalid, hreach, hcode⟩

/-- Nonempty all-represented external-word atoms. -/
abbrev SupportedIndex (t : DominoTiling) (o : Orientation) (m k : ℕ) :=
  {z : OrientedTilingTypedExternalWordCode t //
    (allRepresentedExternalCreationTraceAtom t o m k z).Nonempty}

/-- The corresponding `(external word, represented support)` index. -/
noncomputable def toSupportedIndex
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) :
    TilingOrientedExternalAllCreationStoppedCoordinate.SupportedIndex
      t o m k (allRepresentedSupportAt t o) := by
  refine ⟨⟨eta.1,
    tilingExternalDominoBases t eta.1.start eta.1.retained⟩, ?_⟩
  rw [← allRepresentedExternalCreationTraceAtom_eq_supportAtom]
  exact eta.2

/-- Concrete physical-prefix fibre with empty distinguished complement. -/
noncomputable def allRepresentedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) :=
  concreteFiber o m k (allRepresentedSupportAt t o)
    (allRepresentedSupportData t o m k) (toSupportedIndex eta)

@[simp] theorem allRepresentedFiber_distinguished
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) :
    supportComplementDistinguished t eta.1.start eta.1.retained
      (tilingExternalDominoBases t eta.1.start eta.1.retained) = ∅ := by
  simp [supportComplementDistinguished]

end

end Erdos1165.TilingOrientedAllRepresentedExternalFiber
