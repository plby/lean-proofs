/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePartitionCutCoordinates

/-!
# Restricting cut coordinates while retaining every recorded parent

The finite branch enumeration changes no owner, side or rooted colour.
This source-only transport is used for leaf and pendant-path deletion.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceRestrictedCutCoordinates

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoSourceGlobalPrefixState

variable {r b k : ℕ} (F : OrderedBranchForest r b) (keep : Finset (Fin b))

def retained (x : F.Vertex) : Prop :=
  match x with
  | Sum.inl _ => True
  | Sum.inr a => a.1 ∈ keep

def coordinateInclusion : (OrderedBranchForest.restrict F keep).Vertex → F.Vertex
  | Sum.inl i => Sum.inl i
  | Sum.inr a => Sum.inr ⟨OrderedBranchForest.selectedEquiv keep a.1, a.2⟩

theorem coordinateInclusion_injective : Function.Injective (coordinateInclusion F keep) := by
  rintro (i | ⟨i, a⟩) (j | ⟨j, d⟩) heq
  · exact congrArg Sum.inl (Sum.inl.inj heq)
  · cases heq
  · cases heq
  · have hbranch := Sum.inr.inj heq
    have hij : i = j := (OrderedBranchForest.selectedEquiv keep).injective
      (Subtype.ext (Sigma.mk.inj_iff.mp hbranch).1)
    subst j
    have had : a = d := eq_of_heq (Sigma.mk.inj_iff.mp hbranch).2
    subst d
    rfl

theorem coordinateInclusion_retained (x : (OrderedBranchForest.restrict F keep).Vertex) :
    retained F keep (coordinateInclusion F keep x) := by
  cases x with
  | inl i => trivial
  | inr a => exact (OrderedBranchForest.selectedEquiv keep a.1).2

theorem exists_coordinate_of_retained (x : F.Vertex) (hx : retained F keep x) :
    ∃ y, coordinateInclusion F keep y = x := by
  cases x with
  | inl i => exact ⟨Sum.inl i, rfl⟩
  | inr a =>
      rcases a with ⟨i, a⟩
      obtain ⟨j, hj⟩ := (OrderedBranchForest.selectedEquiv keep).surjective ⟨i, hx⟩
      have hi : (OrderedBranchForest.selectedEquiv keep j).val = i := congrArg Subtype.val hj
      subst i
      exact ⟨Sum.inr ⟨j, a⟩, rfl⟩

def coordinateEquiv : (OrderedBranchForest.restrict F keep).Vertex ≃ {x : F.Vertex // retained F keep x} :=
  Equiv.ofBijective (fun x => ⟨coordinateInclusion F keep x, coordinateInclusion_retained F keep x⟩)
    ⟨fun x y h => coordinateInclusion_injective F keep (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨y, hy⟩ := exists_coordinate_of_retained F keep x hx
      exact ⟨y, Subtype.ext hy⟩⟩

def lowerCoordinate (x : F.Vertex) (hx : retained F keep x) :
    (OrderedBranchForest.restrict F keep).Vertex := (coordinateEquiv F keep).symm ⟨x, hx⟩

theorem coordinateInclusion_lower (x : F.Vertex) (hx : retained F keep x) :
    coordinateInclusion F keep (lowerCoordinate F keep x hx) = x :=
  congrArg Subtype.val ((coordinateEquiv F keep).apply_symm_apply ⟨x, hx⟩)

theorem coordinateOwner_inclusion (x : (OrderedBranchForest.restrict F keep).Vertex) :
    coordinateOwner F.branches F.owner (coordinateInclusion F keep x) =
      coordinateOwner (OrderedBranchForest.restrict F keep).branches (OrderedBranchForest.restrict F keep).owner x := by
  cases x <;> rfl

def restrictedLocate (locate : Fin b → Fin 2 × Fin k) : Fin keep.card → Fin 2 × Fin k :=
  fun i => locate (OrderedBranchForest.selectedEquiv keep i)

theorem coordinateSide_inclusion (rootSide : Fin r → Fin 2) (locate : Fin b → Fin 2 × Fin k)
    (x : (OrderedBranchForest.restrict F keep).Vertex) :
    coordinateSide F.branches rootSide locate (coordinateInclusion F keep x) =
      coordinateSide (OrderedBranchForest.restrict F keep).branches rootSide (restrictedLocate keep locate) x := by
  cases x <;> rfl

theorem coordinateColor_inclusion (x : (OrderedBranchForest.restrict F keep).Vertex) :
    coordinateColor F.branches (coordinateInclusion F keep x) ↔
      coordinateColor (OrderedBranchForest.restrict F keep).branches x := by
  cases x <;> rfl

def restrictCutSource (rootSide : Fin r → Fin 2) (locate : Fin b → Fin 2 × Fin k)
    (L : CutSource F.branches F.owner rootSide locate)
    (hparent : ∀ i hi, retained F keep (L.parent i hi)) :
    CutSource (OrderedBranchForest.restrict F keep).branches (OrderedBranchForest.restrict F keep).owner
      rootSide (restrictedLocate keep locate) where
  parent i hi := lowerCoordinate F keep (L.parent i hi) (hparent i hi)
  before i hi := by
    rw [← coordinateOwner_inclusion, coordinateInclusion_lower]
    exact L.before i hi
  side i hi := by
    rw [← coordinateSide_inclusion, coordinateInclusion_lower]
    exact L.side i hi
  color i hi := by
    rw [← coordinateColor_inclusion, coordinateInclusion_lower]
    exact L.color i hi

end Erdos547b.ZhaoSourceRestrictedCutCoordinates

#print axioms Erdos547b.ZhaoSourceRestrictedCutCoordinates.coordinateInclusion_injective
#print axioms Erdos547b.ZhaoSourceRestrictedCutCoordinates.coordinateInclusion_lower
#print axioms Erdos547b.ZhaoSourceRestrictedCutCoordinates.restrictCutSource
