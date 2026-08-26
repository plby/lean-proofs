/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchyCoordinatePoolLoad
import ErdosProblems.Erdos547b.HierarchicalUnifiedPools

/-!
# Exact selected-edge loads for the coordinate Claim 6.16 layout

Selected branch roots are placed in their assigned `C` clusters.  Hence an
endpoint of their assigned `M_out` edge is charged only non-root coordinates,
and its coordinate load is bounded by the `size - 1` load stored in
`SourceSegmentAllocation.F0_load`.  The more general oriented-side estimate
also counts the branch root and is intentionally not used for this capacity
step.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateF0Load

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
open Erdos547b.ZhaoClaim616HierarchyCoordinatePoolLoad
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma59HierarchicalUnified.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest

universe u

private theorem card_interiorCoordinatesAtPool_le
    {r s : ℕ} {Fine : Type*} [DecidableEq Fine]
    (F : Erdos547b.ZhaoLemma59Hierarchical.HierarchicalSegmentForest r s)
    (interiorPool : ∀ i, Fin (F.segments.size i) → Fine)
    (i : Fin s) (e : Fine) :
    #(interiorCoordinatesAtPool F interiorPool i e) ≤
      F.segments.size i - 1 := by
  have hsubset : interiorCoordinatesAtPool F interiorPool i e ⊆
      Finset.univ.erase (F.segments.root i) := by
    intro a ha
    have hne := (Finset.mem_filter.mp ha).2.1
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  calc
    #(interiorCoordinatesAtPool F interiorPool i e) ≤
        #(Finset.univ.erase (F.segments.root i)) :=
      Finset.card_le_card hsubset
    _ = F.segments.size i - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]

/-- Forgetting endpoint refinements cannot increase physical-pool load. -/
private theorem coordinatePoolLoad_le_poolLoad_of_forget
    {r s : ℕ} {Fine Coarse : Type*}
    [DecidableEq Fine] [DecidableEq Coarse]
    (F : Erdos547b.ZhaoLemma59Hierarchical.HierarchicalSegmentForest r s)
    (forget : Fine → Coarse)
    (rootFine : Fin s → Fine)
    (interiorFine : ∀ i, Fin (F.segments.size i) → Fine)
    (rootCoarse interiorCoarse : Fin s → Coarse)
    (hroot : ∀ i, forget (rootFine i) = rootCoarse i)
    (hinterior : ∀ i a, forget (interiorFine i a) = interiorCoarse i)
    (e : Fine) :
    coordinatePoolLoad F rootFine interiorFine e ≤
      poolLoad F rootCoarse interiorCoarse (forget e) := by
  classical
  rw [coordinatePoolLoad, poolLoad]
  apply Finset.sum_le_sum
  intro i _
  rw [coordinatePoolWeight, poolWeight]
  apply Nat.add_le_add
  · by_cases heq : rootFine i = e
    · have hcoarse : rootCoarse i = forget e := by
        rw [← hroot i, heq]
      simp [heq, hcoarse]
    · simp [heq]
  · by_cases hcoarse : interiorCoarse i = forget e
    · simp only [hcoarse, if_pos]
      exact card_interiorCoordinatesAtPool_le F interiorFine i e
    · have hfine : ∀ a, interiorFine i a ≠ e := by
        intro a heq
        apply hcoarse
        rw [← hinterior i a, heq]
      have hempty : interiorCoordinatesAtPool F interiorFine i e = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact hfine a (Finset.mem_filter.mp ha).2.2
      simp [hcoarse, hempty]

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

private abbrev coordinateRootPool :=
  coordinateHierarchyRootSlot hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge1 edgeb orient

private abbrev coordinateInteriorPool :=
  coordinateHierarchyInteriorSlot hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge0 edge1 edgeb orient

private abbrev physicalRootPool :=
  hierarchyRootPool hT P optional S clusterCapacity allowed0 capacity1
    capacityb base0 A edge1 edgeb (fun _ ↦ 0) (fun _ ↦ 0)

private abbrev physicalInteriorPool :=
  hierarchyInteriorPool hT P optional S clusterCapacity allowed0 capacity1
    capacityb base0 A edge0 edge1 edgeb

private theorem rootSlotPool_coordinateRootPool (i : SegmentIndex hT P optional) :
    rootSlotPool
        (coordinateRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient i) =
      physicalRootPool hT P optional S clusterCapacity allowed0 capacity1
        capacityb base0 A edge1 edgeb i := by
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      simp [coordinateRootPool, physicalRootPool, coordinateHierarchyRootSlot,
        hierarchyRootPool, hierarchyRootSlot, hclass, rootSlotPool]
  | inr j =>
      by_cases hj0 : j ∈ S.selected
      · simp [coordinateRootPool, physicalRootPool, coordinateHierarchyRootSlot,
          coordinateBranchRootSlot, hierarchyRootPool, hierarchyRootSlot,
          branchRootSlot, hclass, hj0, rootSlotPool]
      · by_cases hj1 : j ∈ majorResidualBranches P S
        · simp [coordinateRootPool, physicalRootPool,
            coordinateHierarchyRootSlot, coordinateBranchRootSlot,
            hierarchyRootPool, hierarchyRootSlot, branchRootSlot, hclass,
            hj0, hj1, rootSlotPool]
        · simp [coordinateRootPool, physicalRootPool,
            coordinateHierarchyRootSlot, coordinateBranchRootSlot,
            hierarchyRootPool, hierarchyRootSlot, branchRootSlot, hclass,
            hj0, hj1, rootSlotPool]

private theorem rootSlotPool_coordinateInteriorPool
    (i : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    rootSlotPool
        (coordinateInteriorPool hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb orient i a) =
      physicalInteriorPool hT P optional S clusterCapacity allowed0 capacity1
        capacityb base0 A edge0 edge1 edgeb i := by
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      change rootSlotPool
          (coordinateHierarchyInteriorSlot hT P optional S clusterCapacity
            allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient i a) =
        hierarchyInteriorPool hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb i
      unfold coordinateHierarchyInteriorSlot hierarchyInteriorPool
      rw [hclass]
      rfl
  | inr j =>
      change rootSlotPool
          (coordinateHierarchyInteriorSlot hT P optional S clusterCapacity
            allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb orient i a) =
        hierarchyInteriorPool hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb i
      rw [coordinateHierarchyInteriorSlot_branch hT P optional S
        clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1 edgeb
        orient i j hclass a]
      unfold hierarchyInteriorPool
      rw [hclass]
      by_cases hj0 : j ∈ S.selected
      · simp [branchEdge, hj0, rootSlotPool]
      · by_cases hj1 : j ∈ majorResidualBranches P S
        · simp [branchEdge, hj0, hj1, rootSlotPool]
        · simp [branchEdge, hj0, hj1, rootSlotPool]

/-- The only physical-pool identity needed below, proved locally so the
coordinate route does not depend on the obsolete coarse host pipeline. -/
private theorem physicalPoolLoad_edge0
    (hedge0 : Function.Injective edge0)
    (hdisj01 : Disjoint (Finset.univ.image edge0) (Finset.univ.image edge1))
    (hF0b : ∀ j ∈ S.selected, ∀ eb, edge0 (A.F0edge j) ≠ edgeb eb)
    (e : K0) (heAssigned : ∃ j ∈ S.selected, A.F0edge j = e) :
    poolLoad (AllocationHierarchy hT P optional)
        (physicalRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb)
        (physicalInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb)
        (Sum.inr (Sum.inr (edge0 e)) : PhysicalPool CIndex Edge) =
      ∑ i ∈ F0edgeSegments hT P optional S A e,
        segmentDeepWeight hT P optional i := by
  classical
  rw [poolLoad, F0edgeSegments, Finset.sum_filter, F0Segments,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hclass : segmentSourceClass hT P optional i with
  | inl q =>
      simp [poolWeight, physicalRootPool, physicalInteriorPool,
        hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
        rootSlotPool, F0Segments, hclass]
  | inr j =>
      by_cases hj0 : j ∈ S.selected
      · have heq : edge0 (A.F0edge j) = edge0 e ↔ A.F0edge j = e :=
          hedge0.eq_iff
        simp [poolWeight, physicalRootPool, physicalInteriorPool,
          hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
          branchRootSlot, branchEdge, rootSlotPool, F0Segments,
          segmentDeepWeight, hclass, hj0, heq]
      · by_cases hj1 : j ∈ majorResidualBranches P S
        · have hne : edge1 (A.F1edge j) ≠ edge0 e := by
            intro he
            exact Finset.disjoint_left.mp hdisj01
              (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
              (Finset.mem_image.mpr ⟨A.F1edge j, Finset.mem_univ _, he⟩)
          simp [poolWeight, physicalRootPool, physicalInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool, F0Segments,
            hclass, hj0, hj1, hne]
        · have hne : edgeb (A.Fbedge j) ≠ edge0 e := by
            obtain ⟨j0, hj0Selected, hj0Edge⟩ := heAssigned
            rw [← hj0Edge]
            exact (hF0b j0 hj0Selected (A.Fbedge j)).symm
          simp [poolWeight, physicalRootPool, physicalInteriorPool,
            hierarchyRootPool, hierarchyRootSlot, hierarchyInteriorPool,
            branchRootSlot, branchEdge, rootSlotPool, F0Segments,
            hclass, hj0, hj1, hne]
/-- An endpoint of an actually assigned selected edge carries at most the
stored selected deep load `base0 + small`; selected branch roots are not
charged here because their root slots are the assigned `C` clusters. -/
theorem coordinatePoolLoad_edge0_le_deep
    (hedge0 : Function.Injective edge0)
    (hdisj01 : Disjoint (Finset.univ.image edge0) (Finset.univ.image edge1))
    (hF0b : ∀ j ∈ S.selected, ∀ eb, edge0 (A.F0edge j) ≠ edgeb eb)
    (e : K0) (heAssigned : ∃ j ∈ S.selected, A.F0edge j = e)
    (c : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (coordinateRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient)
        (coordinateInteriorPool hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb orient)
        (Sum.inr (Sum.inr ⟨edge0 e, c⟩) : RootSlot CIndex Edge) ≤
      base0 + small := by
  calc
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (coordinateRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient)
        (coordinateInteriorPool hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb orient)
        (Sum.inr (Sum.inr ⟨edge0 e, c⟩) : RootSlot CIndex Edge) ≤
      poolLoad (AllocationHierarchy hT P optional)
        (physicalRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb)
        (physicalInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb)
        (Sum.inr (Sum.inr (edge0 e)) : PhysicalPool CIndex Edge) := by
          apply coordinatePoolLoad_le_poolLoad_of_forget
            (AllocationHierarchy hT P optional) rootSlotPool
            (coordinateRootPool hT P optional S clusterCapacity allowed0
              capacity1 capacityb base0 A edge1 edgeb orient)
            (coordinateInteriorPool hT P optional S clusterCapacity allowed0
              capacity1 capacityb base0 A edge0 edge1 edgeb orient)
            (physicalRootPool hT P optional S clusterCapacity allowed0 capacity1
              capacityb base0 A edge1 edgeb)
            (physicalInteriorPool hT P optional S clusterCapacity allowed0
              capacity1 capacityb base0 A edge0 edge1 edgeb)
          · exact rootSlotPool_coordinateRootPool hT P optional S clusterCapacity
              allowed0 capacity1 capacityb base0 A edge1 edgeb orient
          · exact rootSlotPool_coordinateInteriorPool hT P optional S
              clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
              edgeb orient
    _ = ∑ i ∈ F0edgeSegments hT P optional S A e,
          segmentDeepWeight hT P optional i := by
      exact physicalPoolLoad_edge0 hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge0 edge1 edgeb hedge0 hdisj01 hF0b e
        heAssigned
    _ ≤ base0 + small := F0edgeSegments_deep_load hT P optional S A e

private theorem orientedClassSize_le_branchSize
    (j : BranchIndex P) (c : Fin 2) :
    orientedClassSize (branchForest P).branches orient j c ≤
      (branchForest P).branches.size j := by
  unfold orientedClassSize
  calc
    #(Finset.univ.filter fun a : Fin ((branchForest P).branches.size j) ↦
        orient j (((branchForest P).branches.isTree j).coloringTwoOfVert
          ((branchForest P).branches.root j) a) = c) ≤
        #(Finset.univ : Finset (Fin ((branchForest P).branches.size j))) :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = (branchForest P).branches.size j := by
      simpa only [Finset.card_univ, Fintype.card_fin]

/-- One residual endpoint carries at most the allocation capacity of its
literal `M₁` edge. -/
theorem coordinatePoolLoad_edge1_le_capacity
    (hparity : OptionalBranchRootParity P optional)
    (hedge1 : Function.Injective edge1)
    (hdisj01 : Disjoint (Finset.univ.image edge0) (Finset.univ.image edge1))
    (hdisj1b : Disjoint (Finset.univ.image edge1) (Finset.univ.image edgeb))
    (e : K1) (c : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (coordinateRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient)
        (coordinateInteriorPool hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb orient)
        (Sum.inr (Sum.inr ⟨edge1 e, c⟩) : RootSlot CIndex Edge) ≤
      capacity1 e := by
  calc
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (coordinateRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient)
        (coordinateInteriorPool hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb orient)
        (Sum.inr (Sum.inr ⟨edge1 e, c⟩) : RootSlot CIndex Edge) ≤
      ∑ j ∈ (majorResidualBranches P S).filter (A.F1edge · = e),
        orientedClassSize (branchForest P).branches orient j c :=
      coordinatePoolLoad_edge1_le hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge0 edge1 edgeb orient hparity hedge1
        hdisj01 hdisj1b e c
    _ ≤ ∑ j ∈ (majorResidualBranches P S).filter (A.F1edge · = e),
        (branchForest P).branches.size j := by
      apply Finset.sum_le_sum
      intro j _
      exact orientedClassSize_le_branchSize P orient j c
    _ ≤ capacity1 e := A.F1_load e

/-- One reserved endpoint carries at most the allocation capacity of its
literal `M_b` edge. -/
theorem coordinatePoolLoad_edgeb_le_capacity
    (hparity : OptionalBranchRootParity P optional)
    (hedgeb : Function.Injective edgeb)
    (hF0b : ∀ j ∈ S.selected, ∀ eb, edge0 (A.F0edge j) ≠ edgeb eb)
    (hdisj1b : Disjoint (Finset.univ.image edge1) (Finset.univ.image edgeb))
    (e : Kb) (c : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (coordinateRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient)
        (coordinateInteriorPool hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb orient)
        (Sum.inr (Sum.inr ⟨edgeb e, c⟩) : RootSlot CIndex Edge) ≤
      capacityb e := by
  calc
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (coordinateRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient)
        (coordinateInteriorPool hT P optional S clusterCapacity allowed0
          capacity1 capacityb base0 A edge0 edge1 edgeb orient)
        (Sum.inr (Sum.inr ⟨edgeb e, c⟩) : RootSlot CIndex Edge) ≤
      ∑ j ∈ (minorBranches P).filter (A.Fbedge · = e),
        orientedClassSize (branchForest P).branches orient j c :=
      coordinatePoolLoad_edgeb_le hT P optional S clusterCapacity allowed0
        capacity1 capacityb base0 A edge0 edge1 edgeb orient hparity hedgeb
        hF0b hdisj1b e c
    _ ≤ ∑ j ∈ (minorBranches P).filter (A.Fbedge · = e),
        (branchForest P).branches.size j := by
      apply Finset.sum_le_sum
      intro j _
      exact orientedClassSize_le_branchSize P orient j c
    _ ≤ capacityb e := A.Fb_load e

end

end Erdos547b.ZhaoClaim616CoordinateF0Load

#print axioms Erdos547b.ZhaoClaim616CoordinateF0Load.coordinatePoolLoad_edge0_le_deep
#print axioms Erdos547b.ZhaoClaim616CoordinateF0Load.coordinatePoolLoad_edge1_le_capacity
#print axioms Erdos547b.ZhaoClaim616CoordinateF0Load.coordinatePoolLoad_edgeb_le_capacity
