/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616CoordinateSegmentColor
import ErdosProblems.Erdos547b.HierarchicalCoordinateMixedDynamicOnline

/-!
# Claim 6.16 mixed dynamic coordinate layout

This file identifies the literal Claim 6.16 coordinate pools with the three
local cases of the mixed dynamic hierarchy constructor.  Component-root
segments are singleton root-only steps.  Selected branch segments keep their
root in the assigned selected cluster and put every non-root vertex in the
assigned matching pair.  Residual and minor segments use their assigned
matching pair for both root and non-root vertices.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateMixedDynamicLayout

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoClaim616HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim616CoordinateSegmentColor

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

section Allocated

variable
    {CIndex K0 K1 Kb Edge : Type*}
    [Fintype CIndex] [DecidableEq CIndex]
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    [DecidableEq Edge]

variable
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCapacity : CIndex → ℕ)
    (allowed0 : CIndex → Finset K0)
    (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ) (base0 : ℕ)
    (A : SourceSegmentAllocation hT P optional S clusterCapacity allowed0
      capacity1 capacityb base0)
    (edge0 : K0 → Edge) (edge1 : K1 → Edge) (edgeb : Kb → Edge)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)

/-- Component-root hierarchy segments are the root-only local steps. -/
def mixedCoordinateRootOnly (i : SegmentIndex hT P optional) : Prop :=
  i ∈ rootSegments hT P optional

/-- Selected hierarchy segments use the two-pair selected local step. -/
def mixedCoordinateSelected (i : SegmentIndex hT P optional) : Prop :=
  i ∈ F0Segments hT P optional S

/-- Local orientation inherited from the canonical branch.  The value on a
component-root segment is immaterial because that segment is root-only. -/
def mixedCoordinateOrient (i : SegmentIndex hT P optional) : Fin 2 ≃ Fin 2 :=
  match segmentSourceClass hT P optional i with
  | Sum.inl _ => Equiv.refl _
  | Sum.inr j => orient j

/-- The two endpoint pools used by one dynamic local step.  The value on a
component-root segment is immaterial because that segment is root-only. -/
def mixedCoordinatePairPool (i : SegmentIndex hT P optional) (c : Fin 2) :
    RootSlot CIndex Edge :=
  match segmentSourceClass hT P optional i with
  | Sum.inl q => Sum.inl (componentReservoirSide P q)
  | Sum.inr j =>
      Sum.inr (Sum.inr
        ⟨coordinateBranchEdge hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb j, c⟩)

/-- Every root-only segment is a singleton. -/
theorem mixedCoordinateRootOnly_size
    (i : SegmentIndex hT P optional)
    (hi : mixedCoordinateRootOnly hT P optional i) :
    (AllocationHierarchy hT P optional).segments.size i = 1 := by
  exact rootSegment_size_eq_one hT P optional i hi

/-- A non-selected, non-root-only segment has its root in local endpoint
zero of its assigned matching pair. -/
theorem mixedCoordinateRootPair
    (i : SegmentIndex hT P optional)
    (hroot : ¬ mixedCoordinateRootOnly hT P optional i)
    (hselected : ¬ mixedCoordinateSelected hT P optional S i) :
    coordinateHierarchyRootSlot hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge1 edgeb orient i =
      mixedCoordinatePairPool hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge0 edge1 edgeb i
          (mixedCoordinateOrient hT P optional orient i 0) := by
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      exfalso
      exact hroot ((mem_rootSegments_iff hT P optional i).2 ⟨q, hclass⟩)
  | inr j =>
      have hj0 : j ∉ S.selected := by
        intro hj
        exact hselected ((mem_F0Segments_iff hT P optional S i).2
          ⟨j, hj, hclass⟩)
      by_cases hj1 : j ∈ majorResidualBranches P S <;>
        simp [coordinateHierarchyRootSlot, coordinateBranchRootSlot,
          mixedCoordinatePairPool, mixedCoordinateOrient,
          coordinateBranchEdge, hclass, hj0, hj1]

/-- Every coordinate of a branch segment is sent to the endpoint prescribed
by the intrinsic rooted two-coloring of that segment. -/
theorem mixedCoordinateInteriorPair
    (hparity : OptionalBranchRootParity P optional)
    (i : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    coordinateHierarchyInteriorSlot hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge0 edge1 edgeb orient i a =
      mixedCoordinatePairPool hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge0 edge1 edgeb i
          (mixedCoordinateOrient hT P optional orient i
            (((AllocationHierarchy hT P optional).segments.isTree i).coloringTwoOfVert
              ((AllocationHierarchy hT P optional).segments.root i) a)) := by
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      unfold coordinateHierarchyInteriorSlot mixedCoordinatePairPool
        mixedCoordinateOrient
      rw [hclass]
  | inr j =>
      have hside := segmentEndpointSide_eq_coloringTwoOfVert
        hT P optional hparity i j hclass a
      rw [coordinateHierarchyInteriorSlot_branch hT P optional S
        clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
        edgeb orient i j hclass a]
      unfold mixedCoordinatePairPool mixedCoordinateOrient
      rw [hclass]
      dsimp only
      rw [hside]
      by_cases hj0 : j ∈ S.selected
      · simp [coordinateBranchEdge, hj0]
      · by_cases hj1 : j ∈ majorResidualBranches P S
        · simp [coordinateBranchEdge, hj0, hj1]
        · simp [coordinateBranchEdge, hj0, hj1]

end Allocated

end Erdos547b.ZhaoClaim616CoordinateMixedDynamicLayout

#print axioms Erdos547b.ZhaoClaim616CoordinateMixedDynamicLayout.mixedCoordinateInteriorPair
