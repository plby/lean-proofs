/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615HierarchicalCoordinateSourceLayout
import ErdosProblems.Erdos547b.Claim616CoordinateSegmentColor
import ErdosProblems.Erdos547b.HierarchicalCoordinateMixedDynamicOnline

/-!
# Claim 6.15 mixed dynamic coordinate layout

The canonical optional marks cut the source at every future attachment, but
no branch vertex is redirected to a distinguished reservoir.  Component-root
segments are singleton root-only steps.  Every branch segment, including the
selected exceptional family, has both its root and its non-root coordinates
in the matching pair assigned to its canonical branch.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615CoordinateMixedDynamicLayout

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616CoordinateSegmentColor
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

section Allocated

variable
    {K0 K1 Kb Edge : Type*}
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    [DecidableEq Edge]

variable
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    (S : SelectedF0 P available target slack)
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (edge0 : K0 → Edge) (edge1 : K1 → Edge) (edgeb : Kb → Edge)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)

/-- Component-root hierarchy segments are the root-only local steps. -/
def mixedCoordinateRootOnly (i : SegmentIndex hT P optional) : Prop :=
  i ∈ rootSegments hT P optional

/-- Claim 6.15 has no two-pair selected step: selected branch roots remain in
their exceptional matching endpoint. -/
def mixedCoordinateSelected (_i : SegmentIndex hT P optional) : Prop := False

/-- Local orientation inherited from the canonical branch. -/
def mixedCoordinateOrient (i : SegmentIndex hT P optional) : Fin 2 ≃ Fin 2 :=
  match segmentSourceClass hT P optional i with
  | Sum.inl _ => Equiv.refl _
  | Sum.inr j => orient j

/-- The two endpoint pools used by one local matching-pair step. -/
def mixedCoordinatePairPool (i : SegmentIndex hT P optional) (c : Fin 2) :
    RootSlot Edge :=
  match segmentSourceClass hT P optional i with
  | Sum.inl q => Sum.inl (componentReservoirSide P q)
  | Sum.inr j =>
      Sum.inr ⟨coordinateBranchEdge P S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb j, c⟩

/-- Every root-only segment is a singleton. -/
theorem mixedCoordinateRootOnly_size
    (i : SegmentIndex hT P optional)
    (hi : mixedCoordinateRootOnly hT P optional i) :
    (AllocationHierarchy hT P optional).segments.size i = 1 := by
  exact rootSegment_size_eq_one hT P optional i hi

/-- A non-root-only segment has its root in local endpoint zero of its
assigned matching pair.  The empty distinguished set is essential here. -/
theorem mixedCoordinateRootPair
    (hparity : OptionalBranchRootParity P optional)
    (i : SegmentIndex hT P optional)
    (hroot : ¬ mixedCoordinateRootOnly hT P optional i) :
    coordinateHierarchyRootSlot hT P optional ∅
        (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb orient i =
      mixedCoordinatePairPool hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb i (mixedCoordinateOrient hT P optional orient i 0) := by
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      exfalso
      exact hroot ((mem_rootSegments_iff hT P optional i).2 ⟨q, hclass⟩)
  | inr j =>
      have hiEmpty : SegmentRootOriginal hT P optional i ∉ (∅ : Finset V) :=
        by simp
      rw [coordinateHierarchyRootSlot_branch hT P optional ∅
        (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A edge0
        edge1 edgeb orient i j hiEmpty hclass]
      have hside := segmentEndpointSide_root_zero_of_optionalParity
        hT P optional hparity i j hclass
      unfold coordinateBranchSlot mixedCoordinatePairPool mixedCoordinateOrient
      rw [hclass, hside]

/-- Every coordinate of a branch segment is sent to the endpoint prescribed
by the intrinsic rooted two-coloring of that segment. -/
theorem mixedCoordinateInteriorPair
    (hparity : OptionalBranchRootParity P optional)
    (i : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    coordinateHierarchyInteriorSlot hT P optional S capacity0 capacity1
        capacityb A edge0 edge1 edgeb orient i a =
      mixedCoordinatePairPool hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb i
          (mixedCoordinateOrient hT P optional orient i
            (((AllocationHierarchy hT P optional).segments.isTree i
              ).coloringTwoOfVert
                ((AllocationHierarchy hT P optional).segments.root i) a)) := by
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      unfold coordinateHierarchyInteriorSlot mixedCoordinatePairPool
        mixedCoordinateOrient
      rw [hclass]
  | inr j =>
      have hside := segmentEndpointSide_eq_coloringTwoOfVert
        hT P optional hparity i j hclass a
      rw [coordinateHierarchyInteriorSlot_branch hT P optional S capacity0
        capacity1 capacityb A edge0 edge1 edgeb orient i j hclass a]
      unfold coordinateBranchSlot mixedCoordinatePairPool mixedCoordinateOrient
      rw [hclass]
      exact congrArg (fun c : Fin 2 =>
        (Sum.inr
          ⟨coordinateBranchEdge P S capacity0 capacity1 capacityb A edge0
            edge1 edgeb j, orient j c⟩ : RootSlot Edge)) hside

end Allocated

end Erdos547b.ZhaoClaim615CoordinateMixedDynamicLayout

#print axioms Erdos547b.ZhaoClaim615CoordinateMixedDynamicLayout.mixedCoordinateRootPair
#print axioms Erdos547b.ZhaoClaim615CoordinateMixedDynamicLayout.mixedCoordinateInteriorPair
