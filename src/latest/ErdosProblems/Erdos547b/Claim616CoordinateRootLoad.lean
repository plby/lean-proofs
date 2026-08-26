/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchyLoadBounds
import ErdosProblems.Erdos547b.Claim616HierarchicalCoordinateSourceLayout
import ErdosProblems.Erdos547b.HierarchicalCoordinatePools

/-!
# Distinguished and selected-root loads in the coordinate Claim 6.16 layout

The coordinate-sensitive accounting differs from the earlier coarse pool
accounting only on matching endpoints.  Distinguished component reservoirs
still receive exactly their singleton root segments, while a selected `C`
cluster receives exactly the roots assigned to that cluster.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateRootLoad

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616HierarchyLoadBounds
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoClaim616HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

section

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

/-- Root-class hierarchy segments whose singleton lies in distinguished
reservoir `side`. -/
def rootReservoirSegments (side : Fin 2) :
    Finset (SegmentIndex hT P optional) :=
  Finset.univ.filter fun i ↦ ∃ q,
    segmentSourceClass hT P optional i = Sum.inl q ∧
      componentReservoirSide P q = side

private abbrev sourceRootPool :=
  coordinateHierarchyRootSlot hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge1 edgeb orient

private abbrev sourceInteriorPool :=
  coordinateHierarchyInteriorSlot hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge0 edge1 edgeb orient

private theorem interiorCoordinatesAt_rootReservoir_eq_empty
    (i : SegmentIndex hT P optional) (side : Fin 2) :
    interiorCoordinatesAtPool (AllocationHierarchy hT P optional)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb orient) i
        (Sum.inl side : RootSlot CIndex Edge) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have ha' := Finset.mem_filter.mp ha
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      have hiRoot : i ∈ rootSegments hT P optional :=
        (mem_rootSegments_iff hT P optional i).2 ⟨q, hclass⟩
      have hsize := rootSegment_size_eq_one hT P optional i hiRoot
      exact ha'.2.1 (Fin.ext (by omega))
  | inr j =>
      have heq := ha'.2.2
      change coordinateHierarchyInteriorSlot hT P optional S clusterCapacity
        allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient i a =
          (Sum.inl side : RootSlot CIndex Edge) at heq
      rw [coordinateHierarchyInteriorSlot_branch hT P optional S
        clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
        edgeb orient i j hclass a] at heq
      by_cases hj0 : j ∈ S.selected
      · simp [hj0] at heq
      · by_cases hj1 : j ∈ majorResidualBranches P S
        · simp [hj0, hj1] at heq
        · simp [hj0, hj1] at heq

private theorem interiorCoordinatesAt_selectedCluster_eq_empty
    (i : SegmentIndex hT P optional) (C0 : CIndex) :
    interiorCoordinatesAtPool (AllocationHierarchy hT P optional)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb orient) i
        (Sum.inr (Sum.inl C0) : RootSlot CIndex Edge) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have heq := (Finset.mem_filter.mp ha).2.2
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      unfold sourceInteriorPool coordinateHierarchyInteriorSlot at heq
      rw [hclass] at heq
      simp at heq
  | inr j =>
      change coordinateHierarchyInteriorSlot hT P optional S clusterCapacity
        allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient i a =
          (Sum.inr (Sum.inl C0) : RootSlot CIndex Edge) at heq
      rw [coordinateHierarchyInteriorSlot_branch hT P optional S
        clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
        edgeb orient i j hclass a] at heq
      by_cases hj0 : j ∈ S.selected
      · simp [hj0] at heq
      · by_cases hj1 : j ∈ majorResidualBranches P S
        · simp [hj0, hj1] at heq
        · simp [hj0, hj1] at heq

theorem coordinatePoolLoad_rootReservoir (side : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb orient)
        (Sum.inl side : RootSlot CIndex Edge) =
      #(rootReservoirSegments hT P optional side) := by
  classical
  rw [coordinatePoolLoad, rootReservoirSegments, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      simp [coordinatePoolWeight, sourceRootPool,
        sourceInteriorPool, coordinateHierarchyRootSlot,
        coordinateHierarchyInteriorSlot, hclass,
        interiorCoordinatesAt_rootReservoir_eq_empty hT P optional S
          clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
          edgeb orient i side]
  | inr j =>
      by_cases hj0 : j ∈ S.selected
      · simp [coordinatePoolWeight, sourceRootPool,
          sourceInteriorPool, coordinateHierarchyRootSlot,
          coordinateHierarchyInteriorSlot, coordinateBranchRootSlot,
          hclass, hj0,
          interiorCoordinatesAt_rootReservoir_eq_empty hT P optional S
            clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
            edgeb orient i side]
      · by_cases hj1 : j ∈ majorResidualBranches P S
        · simp [coordinatePoolWeight, sourceRootPool,
            sourceInteriorPool, coordinateHierarchyRootSlot,
            coordinateHierarchyInteriorSlot, coordinateBranchRootSlot,
            hclass, hj0, hj1,
            interiorCoordinatesAt_rootReservoir_eq_empty hT P optional S
              clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
              edgeb orient i side]
        · simp [coordinatePoolWeight, sourceRootPool,
            sourceInteriorPool, coordinateHierarchyRootSlot,
            coordinateHierarchyInteriorSlot, coordinateBranchRootSlot,
            hclass, hj0, hj1,
            interiorCoordinatesAt_rootReservoir_eq_empty hT P optional S
              clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
              edgeb orient i side]

theorem coordinatePoolLoad_selectedCluster (C0 : CIndex) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb orient)
        (Sum.inr (Sum.inl C0) : RootSlot CIndex Edge) =
      #(F0clusterSegments hT P optional S A C0) := by
  classical
  rw [coordinatePoolLoad, F0clusterSegments, Finset.card_filter, F0Segments,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      simp [coordinatePoolWeight, sourceRootPool,
        sourceInteriorPool, coordinateHierarchyRootSlot,
        coordinateHierarchyInteriorSlot, F0Segments, hclass,
        interiorCoordinatesAt_selectedCluster_eq_empty hT P optional S
          clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
          edgeb orient i C0]
  | inr j =>
      by_cases hj0 : j ∈ S.selected
      · by_cases hjhalf : j ∈ halfBranches P
        · simp [coordinatePoolWeight,
            sourceRootPool, sourceInteriorPool, coordinateHierarchyRootSlot,
            coordinateHierarchyInteriorSlot, coordinateBranchRootSlot,
            F0Segments, hclass, hj0, hjhalf,
            interiorCoordinatesAt_selectedCluster_eq_empty hT P optional S
              clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
              edgeb orient i C0]
        · simp [coordinatePoolWeight,
            sourceRootPool, sourceInteriorPool, coordinateHierarchyRootSlot,
            coordinateHierarchyInteriorSlot, coordinateBranchRootSlot,
            F0Segments, hclass, hj0, hjhalf,
            interiorCoordinatesAt_selectedCluster_eq_empty hT P optional S
              clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
              edgeb orient i C0]
      · by_cases hjhalf : j ∈ halfBranches P
        · simp [coordinatePoolWeight, sourceRootPool,
            sourceInteriorPool, coordinateHierarchyRootSlot,
            coordinateHierarchyInteriorSlot, coordinateBranchRootSlot,
            F0Segments, hclass, hj0, hjhalf,
            interiorCoordinatesAt_selectedCluster_eq_empty hT P optional S
              clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
              edgeb orient i C0]
        · simp [coordinatePoolWeight, sourceRootPool,
            sourceInteriorPool, coordinateHierarchyRootSlot,
            coordinateHierarchyInteriorSlot, coordinateBranchRootSlot,
            F0Segments, hclass, hj0, hjhalf,
            interiorCoordinatesAt_selectedCluster_eq_empty hT P optional S
              clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
              edgeb orient i C0]

theorem coordinatePoolLoad_rootReservoir_le
    (side : Fin 2) (bound : ℕ)
    (hbound : #(rootReservoirSegments hT P optional side) ≤ bound) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb orient)
        (Sum.inl side : RootSlot CIndex Edge) ≤ bound := by
  rw [coordinatePoolLoad_rootReservoir hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge0 edge1 edgeb orient side]
  exact hbound

theorem coordinatePoolLoad_selectedCluster_le (C0 : CIndex) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb orient)
        (Sum.inr (Sum.inl C0) : RootSlot CIndex Edge) ≤ clusterCapacity C0 := by
  rw [coordinatePoolLoad_selectedCluster hT P optional S clusterCapacity
    allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient C0]
  exact F0clusterSegments_card hT P optional S A C0

end

end Erdos547b.ZhaoClaim616CoordinateRootLoad

#print axioms Erdos547b.ZhaoClaim616CoordinateRootLoad.coordinatePoolLoad_rootReservoir
#print axioms Erdos547b.ZhaoClaim616CoordinateRootLoad.coordinatePoolLoad_selectedCluster_le
