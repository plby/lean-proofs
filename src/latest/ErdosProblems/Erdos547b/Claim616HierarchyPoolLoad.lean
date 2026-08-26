/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchyLoadBounds
import ErdosProblems.Erdos547b.Claim616HierarchicalSourceLayout
import ErdosProblems.Erdos547b.HierarchicalUnifiedPools

/-!
# Aggregate physical-pool load of the Claim 6.16 source layout

The branch-coherent allocation bounds are transported through the tagged
source layout into the single `poolLoad` inequality consumed by the unified
online realization.  The `Mout` and `Mb` edge families may overlap; only the
edges actually assigned to selected `F₀` branches are required to avoid
`Mb`.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchyPoolLoad

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchyLoadBounds
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoLemma59HierarchicalUnified
open Erdos547b.ZhaoLemma59HierarchicalUnified.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma614HierarchicalFullTree

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
    (rootSide1 : K1 → Fin 2) (rootSideb : Kb → Fin 2)

def rootReservoirSegments (side : Fin 2) :
    Finset (SegmentIndex hT P optional) :=
  Finset.univ.filter fun i ↦ ∃ q,
    segmentSourceClass hT P optional i = Sum.inl q ∧
      componentReservoirSide P q = side

private abbrev sourceRootPool :=
  hierarchyRootPool hT P optional S clusterCapacity allowed0 capacity1
    capacityb base0 A edge1 edgeb rootSide1 rootSideb

private abbrev sourceInteriorPool :=
  hierarchyInteriorPool hT P optional S clusterCapacity allowed0 capacity1
    capacityb base0 A edge0 edge1 edgeb

theorem poolLoad_rootReservoir (side : Fin 2) :
    poolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb rootSide1 rootSideb)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb)
        (Sum.inl side) =
      #(rootReservoirSegments hT P optional side) := by
  classical
  rw [poolLoad, rootReservoirSegments, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      have hiRoot : i ∈ rootSegments hT P optional :=
        (mem_rootSegments_iff hT P optional i).2 ⟨q, hclass⟩
      have hsize := rootSegment_size_eq_one hT P optional i hiRoot
      simp [poolWeight, sourceRootPool, sourceInteriorPool,
        hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
        rootSlotPool, hclass, hsize]
  | inr j =>
      by_cases hj0 : j ∈ S.selected
      · simp [poolWeight, sourceRootPool, sourceInteriorPool,
          hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
          branchRootSlot, branchEdge, rootSlotPool, hclass, hj0]
      · by_cases hj1 : j ∈ majorResidualBranches P S
        · simp [poolWeight, sourceRootPool, sourceInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool, hclass, hj0, hj1]
        · simp [poolWeight, sourceRootPool, sourceInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool, hclass, hj0, hj1]

theorem poolLoad_selectedCluster (C0 : CIndex) :
    poolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb rootSide1 rootSideb)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb)
        (Sum.inr (Sum.inl C0)) =
      #(F0clusterSegments hT P optional S A C0) := by
  classical
  rw [poolLoad, F0clusterSegments, Finset.card_filter, F0Segments,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      simp [poolWeight, sourceRootPool, sourceInteriorPool,
        hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
        rootSlotPool, F0Segments, hclass]
  | inr j =>
      by_cases hj0 : j ∈ S.selected
      · by_cases hjhalf : j ∈ halfBranches P
        · simp [poolWeight, sourceRootPool, sourceInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool, F0Segments,
            hclass, hj0, hjhalf]
        · simp [poolWeight, sourceRootPool, sourceInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool, F0Segments,
            hclass, hj0, hjhalf]
      · simp [poolWeight, sourceRootPool, sourceInteriorPool,
          hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
          branchRootSlot, branchEdge, rootSlotPool, F0Segments,
          hclass, hj0]

theorem poolLoad_edge0
    (hedge0 : Function.Injective edge0)
    (hdisj01 : Disjoint (Finset.univ.image edge0) (Finset.univ.image edge1))
    (hF0b : ∀ j ∈ S.selected, ∀ eb, edge0 (A.F0edge j) ≠ edgeb eb)
    (e : K0)
    (heAssigned : ∃ j ∈ S.selected, A.F0edge j = e) :
    poolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb rootSide1 rootSideb)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb)
        (Sum.inr (Sum.inr (edge0 e))) =
      ∑ i ∈ F0edgeSegments hT P optional S A e,
        segmentDeepWeight hT P optional i := by
  classical
  rw [poolLoad, F0edgeSegments, Finset.sum_filter, F0Segments,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      simp [poolWeight, sourceRootPool, sourceInteriorPool,
        hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
        rootSlotPool, F0Segments, hclass]
  | inr j =>
      by_cases hj0 : j ∈ S.selected
      · have heq : edge0 (A.F0edge j) = edge0 e ↔ A.F0edge j = e :=
          hedge0.eq_iff
        simp [poolWeight, sourceRootPool, sourceInteriorPool,
          hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
          branchRootSlot, branchEdge, rootSlotPool, F0Segments,
          segmentDeepWeight, hclass, hj0, heq]
      · by_cases hj1 : j ∈ majorResidualBranches P S
        · have hne : edge1 (A.F1edge j) ≠ edge0 e := by
            intro he
            exact Finset.disjoint_left.mp hdisj01
              (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
              (Finset.mem_image.mpr ⟨A.F1edge j, Finset.mem_univ _, he⟩)
          simp [poolWeight, sourceRootPool, sourceInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool, F0Segments,
            hclass, hj0, hj1, hne]
        · have hne : edgeb (A.Fbedge j) ≠ edge0 e := by
            obtain ⟨j0, hj0Selected, hj0Edge⟩ := heAssigned
            rw [← hj0Edge]
            exact (hF0b j0 hj0Selected (A.Fbedge j)).symm
          simp [poolWeight, sourceRootPool, sourceInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool, F0Segments,
            hclass, hj0, hj1, hne]

theorem poolLoad_edge1
    (hedge1 : Function.Injective edge1)
    (hdisj01 : Disjoint (Finset.univ.image edge0) (Finset.univ.image edge1))
    (hdisj1b : Disjoint (Finset.univ.image edge1) (Finset.univ.image edgeb))
    (e : K1) :
    poolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb rootSide1 rootSideb)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb)
        (Sum.inr (Sum.inr (edge1 e))) =
      ∑ i ∈ F1edgeSegments hT P optional S A e,
        (AllocationHierarchy hT P optional).segments.size i := by
  classical
  rw [poolLoad, F1edgeSegments, Finset.sum_filter, F1Segments,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have hpos := segmented_size_pos (wholeBranchForest T hT globalRoot)
    (AllocationSpecial hT P optional) i
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      simp [poolWeight, sourceRootPool, sourceInteriorPool,
        hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
        rootSlotPool, F1Segments, hclass]
  | inr j =>
      by_cases hj0 : j ∈ S.selected
      · have hne : edge0 (A.F0edge j) ≠ edge1 e := by
          intro he
          exact Finset.disjoint_left.mp hdisj01
            (Finset.mem_image.mpr ⟨A.F0edge j, Finset.mem_univ _, he⟩)
            (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
        simp [poolWeight, sourceRootPool, sourceInteriorPool,
          hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
          branchRootSlot, branchEdge, rootSlotPool, F1Segments,
          hclass, hj0, hne]
      · by_cases hj1 : j ∈ majorResidualBranches P S
        · have heq : edge1 (A.F1edge j) = edge1 e ↔ A.F1edge j = e :=
            hedge1.eq_iff
          have hone : 1 +
              ((AllocationHierarchy hT P optional).segments.size i - 1) =
              (AllocationHierarchy hT P optional).segments.size i := by omega
          simp [poolWeight, sourceRootPool, sourceInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool, F1Segments,
            hclass, hj0, hj1, heq, hone]
        · have hne : edgeb (A.Fbedge j) ≠ edge1 e := by
            intro he
            exact Finset.disjoint_left.mp hdisj1b
              (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
              (Finset.mem_image.mpr ⟨A.Fbedge j, Finset.mem_univ _, he⟩)
          simp [poolWeight, sourceRootPool, sourceInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool, F1Segments,
            hclass, hj0, hj1, hne]

theorem poolLoad_edgeb
    (hedgeb : Function.Injective edgeb)
    (hF0b : ∀ j ∈ S.selected, ∀ eb, edge0 (A.F0edge j) ≠ edgeb eb)
    (hdisj1b : Disjoint (Finset.univ.image edge1) (Finset.univ.image edgeb))
    (e : Kb) :
    poolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb rootSide1 rootSideb)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb)
        (Sum.inr (Sum.inr (edgeb e))) =
      ∑ i ∈ FbedgeSegments hT P optional S A e,
        (AllocationHierarchy hT P optional).segments.size i := by
  classical
  rw [poolLoad, FbedgeSegments, Finset.sum_filter, FbSegments,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have hpos := segmented_size_pos (wholeBranchForest T hT globalRoot)
    (AllocationSpecial hT P optional) i
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      simp [poolWeight, sourceRootPool, sourceInteriorPool,
        hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
        rootSlotPool, FbSegments, hclass]
  | inr j =>
      by_cases hj0 : j ∈ S.selected
      · have hne : edge0 (A.F0edge j) ≠ edgeb e := by
          exact hF0b j hj0 e
        simp [poolWeight, sourceRootPool, sourceInteriorPool,
          hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
          branchRootSlot, branchEdge, rootSlotPool, FbSegments,
          hclass, hj0, hne]
      · by_cases hj1 : j ∈ majorResidualBranches P S
        · have hne : edge1 (A.F1edge j) ≠ edgeb e := by
            intro he
            exact Finset.disjoint_left.mp hdisj1b
              (Finset.mem_image.mpr ⟨A.F1edge j, Finset.mem_univ _, he⟩)
              (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
          simp [poolWeight, sourceRootPool, sourceInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool, FbSegments,
            hclass, hj0, hj1, hne]
        · have hjb : j ∈ minorBranches P := by
            have hcover : j ∈ S.selected ∪ majorResidualBranches P S ∪
                minorBranches P := by
              rw [selected_union_residual_union_minor P S]
              exact Finset.mem_univ _
            simpa only [Finset.mem_union, hj0, hj1, false_or] using hcover
          have heq : edgeb (A.Fbedge j) = edgeb e ↔ A.Fbedge j = e :=
            hedgeb.eq_iff
          have hone : 1 +
              ((AllocationHierarchy hT P optional).segments.size i - 1) =
              (AllocationHierarchy hT P optional).segments.size i := by omega
          simp [poolWeight, sourceRootPool, sourceInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool, FbSegments,
            hclass, hj0, hj1, hjb, heq, hone]

theorem poolLoad_edge_none
    (e : Edge)
    (h0 : ∀ j ∈ S.selected, edge0 (A.F0edge j) ≠ e)
    (h1 : e ∉ Finset.univ.image edge1)
    (hb : e ∉ Finset.univ.image edgeb) :
    poolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb rootSide1 rootSideb)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb)
        (Sum.inr (Sum.inr e)) = 0 := by
  classical
  rw [poolLoad]
  apply Finset.sum_eq_zero
  intro i _
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      simp [poolWeight, sourceRootPool, sourceInteriorPool,
        hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
        rootSlotPool, hclass]
  | inr j =>
      have hne1 : edge1 (A.F1edge j) ≠ e := fun he ↦ h1
        (Finset.mem_image.mpr ⟨A.F1edge j, Finset.mem_univ _, he⟩)
      have hneb : edgeb (A.Fbedge j) ≠ e := fun he ↦ hb
        (Finset.mem_image.mpr ⟨A.Fbedge j, Finset.mem_univ _, he⟩)
      by_cases hj0 : j ∈ S.selected
      · have hne0 := h0 j hj0
        simp [poolWeight, sourceRootPool, sourceInteriorPool,
          hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
          branchRootSlot, branchEdge, rootSlotPool,
          hclass, hj0, hne0]
      · by_cases hj1 : j ∈ majorResidualBranches P S
        · simp [poolWeight, sourceRootPool, sourceInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool,
            hclass, hj0, hj1, hne1]
        · simp [poolWeight, sourceRootPool, sourceInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool,
            hclass, hj0, hj1, hneb]

/-- Single source-only load bound used by the rich online host theorem. -/
theorem poolLoad_le_poolCapacity
    (poolCapacity : PhysicalPool CIndex Edge → ℕ)
    (hedge0 : Function.Injective edge0)
    (hedge1 : Function.Injective edge1)
    (hedgeb : Function.Injective edgeb)
    (hdisj01 : Disjoint (Finset.univ.image edge0) (Finset.univ.image edge1))
    (hF0b : ∀ j ∈ S.selected, ∀ eb, edge0 (A.F0edge j) ≠ edgeb eb)
    (hdisj1b : Disjoint (Finset.univ.image edge1) (Finset.univ.image edgeb))
    (hroot : ∀ side, #(rootReservoirSegments hT P optional side) ≤
      poolCapacity (Sum.inl side))
    (hcluster : ∀ C0, clusterCapacity C0 ≤
      poolCapacity (Sum.inr (Sum.inl C0)))
    (hedge0Cap : ∀ e, base0 + small ≤
      poolCapacity (Sum.inr (Sum.inr (edge0 e))))
    (hedge1Cap : ∀ e, capacity1 e ≤
      poolCapacity (Sum.inr (Sum.inr (edge1 e))))
    (hedgebCap : ∀ e, capacityb e ≤
      poolCapacity (Sum.inr (Sum.inr (edgeb e))))
    (p : PhysicalPool CIndex Edge) :
    poolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb rootSide1 rootSideb)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb) p ≤ poolCapacity p := by
  classical
  rcases p with side | C_or_edge
  · rw [poolLoad_rootReservoir hT P optional S clusterCapacity allowed0
      capacity1 capacityb base0 A edge0 edge1 edgeb rootSide1
      rootSideb side]
    exact hroot side
  · rcases C_or_edge with C0 | e
    · rw [poolLoad_selectedCluster hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge0 edge1 edgeb rootSide1
        rootSideb C0]
      exact (F0clusterSegments_card hT P optional S A C0).trans (hcluster C0)
    · by_cases h0 : e ∈ S.selected.image (fun j ↦ edge0 (A.F0edge j))
      · obtain ⟨j, hjSelected, rfl⟩ := Finset.mem_image.mp h0
        rw [poolLoad_edge0 hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb rootSide1 rootSideb
          hedge0 hdisj01 hF0b (A.F0edge j) ⟨j, hjSelected, rfl⟩]
        exact (F0edgeSegments_deep_load hT P optional S A (A.F0edge j)).trans
          (hedge0Cap (A.F0edge j))
      · by_cases h1 : e ∈ Finset.univ.image edge1
        · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h1
          rw [poolLoad_edge1 hT P optional S clusterCapacity allowed0 capacity1
            capacityb base0 A edge0 edge1 edgeb rootSide1 rootSideb
            hedge1 hdisj01 hdisj1b k]
          exact (F1edgeSegments_load hT P optional S A k).trans
            (hedge1Cap k)
        · by_cases hb : e ∈ Finset.univ.image edgeb
          · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hb
            rw [poolLoad_edgeb hT P optional S clusterCapacity allowed0
              capacity1 capacityb base0 A edge0 edge1 edgeb rootSide1
              rootSideb hedgeb hF0b hdisj1b k]
            exact (FbedgeSegments_load hT P optional S A k).trans
              (hedgebCap k)
          · rw [poolLoad_edge_none hT P optional S clusterCapacity allowed0
              capacity1 capacityb base0 A edge0 edge1 edgeb rootSide1
              rootSideb e (by
                intro j hj he
                exact h0 (Finset.mem_image.mpr ⟨j, hj, he⟩)) h1 hb]
            exact Nat.zero_le _

end

end Erdos547b.ZhaoClaim616HierarchyPoolLoad

#print axioms Erdos547b.ZhaoClaim616HierarchyPoolLoad.poolLoad_le_poolCapacity
