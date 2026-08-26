/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchyCoordinateSide
import ErdosProblems.Erdos547b.Claim616HierarchyLoadBounds
import ErdosProblems.Erdos547b.Claim616HierarchicalCoordinateSourceLayout

/-!
# Matching-endpoint loads of the Claim 6.16 coordinate layout

For a residual (`F₁`) or minor (`F_b`) matching edge and one of its two
physical endpoints, the literal coordinate-pool load is bounded by the sum of
the corresponding oriented colour classes of the canonical branches assigned
to that edge.  These are exactly the side loads constructed by Zhao's
threshold-switch and Appendix-A realizations.

The proof only classifies source coordinates and uses injectivity/disjointness
of the three literal matching-edge maps.  It has no host graph, embedding, or
capacity premise.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchyCoordinatePoolLoad

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
open Erdos547b.ZhaoClaim616HierarchyCoordinateSide
open Erdos547b.ZhaoLemma58GroupedSmallForest
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

private abbrev sourceRootPool :=
  coordinateHierarchyRootSlot hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge1 edgeb orient

private abbrev sourceInteriorPool :=
  coordinateHierarchyInteriorSlot hT P optional S clusterCapacity allowed0
    capacity1 capacityb base0 A edge0 edge1 edgeb orient

theorem coordinatePoolLoad_edge0_le
    (hedge0 : Function.Injective edge0)
    (hdisj01 : Disjoint (Finset.univ.image edge0) (Finset.univ.image edge1))
    (hF0b : ∀ j ∈ S.selected, ∀ eb, edge0 (A.F0edge j) ≠ edgeb eb)
    (e : K0)
    (heAssigned : ∃ j ∈ S.selected, A.F0edge j = e)
    (c : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb orient)
        (Sum.inr (Sum.inr ⟨edge0 e, c⟩) : RootSlot CIndex Edge) ≤
      ∑ j ∈ S.selected.filter (A.F0edge · = e),
        orientedClassSize (branchForest P).branches orient j c := by
  classical
  let I := F0edgeSegments hT P optional S A e
  let B := S.selected.filter (A.F0edge · = e)
  apply coordinatePoolLoad_le_branch_side_load hT P optional
    (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
      capacityb base0 A edge1 edgeb orient)
    (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
      capacityb base0 A edge0 edge1 edgeb orient)
    (Sum.inr (Sum.inr ⟨edge0 e, c⟩) : RootSlot CIndex Edge)
    I B orient c
  · intro i hi
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        simp [sourceRootPool, coordinateHierarchyRootSlot, hclass] at hi
    | inr j =>
        by_cases hj0 : j ∈ S.selected
        · simp [sourceRootPool, coordinateHierarchyRootSlot,
            coordinateBranchRootSlot, hclass, hj0] at hi
        · by_cases hj1 : j ∈ majorResidualBranches P S
          · have hne : edge1 (A.F1edge j) ≠ edge0 e := by
              intro heq
              exact Finset.disjoint_left.mp hdisj01
                (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
                (Finset.mem_image.mpr
                  ⟨A.F1edge j, Finset.mem_univ _, heq⟩)
            simp [sourceRootPool, coordinateHierarchyRootSlot,
              coordinateBranchRootSlot, hclass, hj0, hj1, hne] at hi
          · have hne : edgeb (A.Fbedge j) ≠ edge0 e := by
              obtain ⟨j0, hj0Selected, hj0Edge⟩ := heAssigned
              rw [← hj0Edge]
              exact (hF0b j0 hj0Selected (A.Fbedge j)).symm
            simp [sourceRootPool, coordinateHierarchyRootSlot,
              coordinateBranchRootSlot, hclass, hj0, hj1, hne] at hi
  · intro i a haroot hi
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        unfold sourceInteriorPool coordinateHierarchyInteriorSlot at hi
        rw [hclass] at hi
        simp at hi
    | inr j =>
        unfold sourceInteriorPool at hi
        rw [coordinateHierarchyInteriorSlot_branch hT P optional S
          clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
          edgeb orient i j hclass a] at hi
        by_cases hj0 : j ∈ S.selected
        · have hedgeSide : edge0 (A.F0edge j) = edge0 e ∧
              orient j (segmentEndpointSide hT P optional i j a) = c := by
            simpa [hj0] using hi
          have hedge : A.F0edge j = e := hedge0 hedgeSide.1
          rw [hierarchyCoordinatesAtSide, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_, ?_⟩
          · apply Finset.mem_filter.mpr
            refine ⟨(mem_F0Segments_iff hT P optional S i).2
              ⟨j, hj0, hclass⟩, ?_⟩
            exact ⟨j, hclass, hedge⟩
          · rw [hclass]
            exact hedgeSide.2
        · by_cases hj1 : j ∈ majorResidualBranches P S
          · have hne : edge1 (A.F1edge j) ≠ edge0 e := by
              intro heq
              exact Finset.disjoint_left.mp hdisj01
                (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
                (Finset.mem_image.mpr
                  ⟨A.F1edge j, Finset.mem_univ _, heq⟩)
            simp [hj0, hj1, hne] at hi
          · have hne : edgeb (A.Fbedge j) ≠ edge0 e := by
              obtain ⟨j0, hj0Selected, hj0Edge⟩ := heAssigned
              rw [← hj0Edge]
              exact (hF0b j0 hj0Selected (A.Fbedge j)).symm
            simp [hj0, hj1, hne] at hi
  · intro i hi
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨j, hjClass, -⟩ := hi'.2
    exact ⟨j, hjClass⟩
  · intro i hi j hjClass
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨k, hkSelected, hkClass⟩ :=
      (mem_F0Segments_iff hT P optional S i).mp hi'.1
    obtain ⟨l, hlClass, hlEdge⟩ := hi'.2
    have hkj : k = j := Sum.inr.inj (hkClass.symm.trans hjClass)
    have hlj : l = j := Sum.inr.inj (hlClass.symm.trans hjClass)
    subst k
    subst l
    exact Finset.mem_filter.mpr ⟨hkSelected, hlEdge⟩

theorem coordinatePoolLoad_edge1_le
    (hparity : OptionalBranchRootParity P optional)
    (hedge1 : Function.Injective edge1)
    (hdisj01 : Disjoint (Finset.univ.image edge0) (Finset.univ.image edge1))
    (hdisj1b : Disjoint (Finset.univ.image edge1) (Finset.univ.image edgeb))
    (e : K1) (c : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb orient)
        (Sum.inr (Sum.inr ⟨edge1 e, c⟩) : RootSlot CIndex Edge) ≤
      ∑ j ∈ (majorResidualBranches P S).filter (A.F1edge · = e),
        orientedClassSize (branchForest P).branches orient j c := by
  classical
  let I := F1edgeSegments hT P optional S A e
  let B := (majorResidualBranches P S).filter (A.F1edge · = e)
  apply coordinatePoolLoad_le_branch_side_load hT P optional
    (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
      capacityb base0 A edge1 edgeb orient)
    (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
      capacityb base0 A edge0 edge1 edgeb orient)
    (Sum.inr (Sum.inr ⟨edge1 e, c⟩) : RootSlot CIndex Edge)
    I B orient c
  · intro i hi
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        simp [sourceRootPool, coordinateHierarchyRootSlot, hclass] at hi
    | inr j =>
        by_cases hj0 : j ∈ S.selected
        · simp [sourceRootPool, coordinateHierarchyRootSlot,
            coordinateBranchRootSlot, hclass, hj0] at hi
        · by_cases hj1 : j ∈ majorResidualBranches P S
          · have hside := segmentEndpointSide_root_zero_of_optionalParity
              hT P optional hparity i j hclass
            have hedgeSide : edge1 (A.F1edge j) = edge1 e ∧ orient j 0 = c := by
              simpa [sourceRootPool, coordinateHierarchyRootSlot,
                coordinateBranchRootSlot, hclass, hj0, hj1] using hi
            have hedge : A.F1edge j = e := hedge1 hedgeSide.1
            rw [hierarchyCoordinatesAtSide, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_, ?_⟩
            · apply Finset.mem_filter.mpr
              refine ⟨(mem_F1Segments_iff hT P optional S i).2
                ⟨j, hj1, hclass⟩, ?_⟩
              exact ⟨j, hclass, hedge⟩
            · rw [hclass]
              change orient j
                (segmentEndpointSide hT P optional i j
                  ((AllocationHierarchy hT P optional).segments.root i)) = c
              rw [hside]
              exact hedgeSide.2
          · have hne : edgeb (A.Fbedge j) ≠ edge1 e := by
              intro heq
              exact Finset.disjoint_left.mp hdisj1b
                (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
                (Finset.mem_image.mpr
                  ⟨A.Fbedge j, Finset.mem_univ _, heq⟩)
            simp [sourceRootPool, coordinateHierarchyRootSlot,
              coordinateBranchRootSlot, hclass, hj0, hj1, hne] at hi
  · intro i a haroot hi
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        unfold sourceInteriorPool coordinateHierarchyInteriorSlot at hi
        rw [hclass] at hi
        simp at hi
    | inr j =>
        unfold sourceInteriorPool at hi
        rw [coordinateHierarchyInteriorSlot_branch hT P optional S
          clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
          edgeb orient i j hclass a] at hi
        by_cases hj0 : j ∈ S.selected
        · have hne : edge0 (A.F0edge j) ≠ edge1 e := by
            intro heq
            exact Finset.disjoint_left.mp hdisj01
              (Finset.mem_image.mpr
                ⟨A.F0edge j, Finset.mem_univ _, heq⟩)
              (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
          simp [hj0, hne] at hi
        · by_cases hj1 : j ∈ majorResidualBranches P S
          · have hedgeSide : edge1 (A.F1edge j) = edge1 e ∧
                orient j (segmentEndpointSide hT P optional i j a) = c := by
              simpa [hj0, hj1] using hi
            have hedge : A.F1edge j = e := hedge1 hedgeSide.1
            rw [hierarchyCoordinatesAtSide, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_, ?_⟩
            · apply Finset.mem_filter.mpr
              refine ⟨(mem_F1Segments_iff hT P optional S i).2
                ⟨j, hj1, hclass⟩, ?_⟩
              exact ⟨j, hclass, hedge⟩
            · rw [hclass]
              exact hedgeSide.2
          · have hne : edgeb (A.Fbedge j) ≠ edge1 e := by
              intro heq
              exact Finset.disjoint_left.mp hdisj1b
                (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
                (Finset.mem_image.mpr
                  ⟨A.Fbedge j, Finset.mem_univ _, heq⟩)
            simp [hj0, hj1, hne] at hi
  · intro i hi
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨j, hjClass, -⟩ := hi'.2
    exact ⟨j, hjClass⟩
  · intro i hi j hjClass
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨k, hkResidual, hkClass⟩ :=
      (mem_F1Segments_iff hT P optional S i).mp hi'.1
    obtain ⟨l, hlClass, hlEdge⟩ := hi'.2
    have hkj : k = j := Sum.inr.inj (hkClass.symm.trans hjClass)
    have hlj : l = j := Sum.inr.inj (hlClass.symm.trans hjClass)
    subst k
    subst l
    exact Finset.mem_filter.mpr ⟨hkResidual, hlEdge⟩

theorem coordinatePoolLoad_edgeb_le
    (hparity : OptionalBranchRootParity P optional)
    (hedgeb : Function.Injective edgeb)
    (hF0b : ∀ j ∈ S.selected, ∀ eb, edge0 (A.F0edge j) ≠ edgeb eb)
    (hdisj1b : Disjoint (Finset.univ.image edge1) (Finset.univ.image edgeb))
    (e : Kb) (c : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge1 edgeb orient)
        (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
          capacityb base0 A edge0 edge1 edgeb orient)
        (Sum.inr (Sum.inr ⟨edgeb e, c⟩) : RootSlot CIndex Edge) ≤
      ∑ j ∈ (minorBranches P).filter (A.Fbedge · = e),
        orientedClassSize (branchForest P).branches orient j c := by
  classical
  let I := FbedgeSegments hT P optional S A e
  let B := (minorBranches P).filter (A.Fbedge · = e)
  apply coordinatePoolLoad_le_branch_side_load hT P optional
    (sourceRootPool hT P optional S clusterCapacity allowed0 capacity1
      capacityb base0 A edge1 edgeb orient)
    (sourceInteriorPool hT P optional S clusterCapacity allowed0 capacity1
      capacityb base0 A edge0 edge1 edgeb orient)
    (Sum.inr (Sum.inr ⟨edgeb e, c⟩) : RootSlot CIndex Edge)
    I B orient c
  · intro i hi
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        simp [sourceRootPool, coordinateHierarchyRootSlot, hclass] at hi
    | inr j =>
        by_cases hj0 : j ∈ S.selected
        · simp [sourceRootPool, coordinateHierarchyRootSlot,
            coordinateBranchRootSlot, hclass, hj0] at hi
        · by_cases hj1 : j ∈ majorResidualBranches P S
          · have hne : edge1 (A.F1edge j) ≠ edgeb e := by
              intro heq
              exact Finset.disjoint_left.mp hdisj1b
                (Finset.mem_image.mpr
                  ⟨A.F1edge j, Finset.mem_univ _, heq⟩)
                (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
            simp [sourceRootPool, coordinateHierarchyRootSlot,
              coordinateBranchRootSlot, hclass, hj0, hj1, hne] at hi
          · have hside := segmentEndpointSide_root_zero_of_optionalParity
              hT P optional hparity i j hclass
            have hedgeSide : edgeb (A.Fbedge j) = edgeb e ∧ orient j 0 = c := by
              simpa [sourceRootPool, coordinateHierarchyRootSlot,
                coordinateBranchRootSlot, hclass, hj0, hj1] using hi
            have hedge : A.Fbedge j = e := hedgeb hedgeSide.1
            rw [hierarchyCoordinatesAtSide, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_, ?_⟩
            · apply Finset.mem_filter.mpr
              refine ⟨(mem_FbSegments_iff hT P optional i).2
                ⟨j, ?_, hclass⟩, ?_⟩
              · have hjNotHalf : j ∉ halfBranches P := by
                  intro hjHalf
                  exact hj1 ((mem_majorResidualBranches P S j).2
                    ⟨hjHalf, hj0⟩)
                have hjCover : j ∈ halfBranches P ∪ minorBranches P := by
                  rw [halfBranches_union_minorBranches P]
                  exact Finset.mem_univ _
                exact (Finset.mem_union.mp hjCover).resolve_left hjNotHalf
              · exact ⟨j, hclass, hedge⟩
            · rw [hclass]
              change orient j
                (segmentEndpointSide hT P optional i j
                  ((AllocationHierarchy hT P optional).segments.root i)) = c
              rw [hside]
              exact hedgeSide.2
  · intro i a haroot hi
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        unfold sourceInteriorPool coordinateHierarchyInteriorSlot at hi
        rw [hclass] at hi
        simp at hi
    | inr j =>
        unfold sourceInteriorPool at hi
        rw [coordinateHierarchyInteriorSlot_branch hT P optional S
          clusterCapacity allowed0 capacity1 capacityb base0 A edge0 edge1
          edgeb orient i j hclass a] at hi
        by_cases hj0 : j ∈ S.selected
        · have hne : edge0 (A.F0edge j) ≠ edgeb e :=
            hF0b j hj0 e
          simp [hj0, hne] at hi
        · by_cases hj1 : j ∈ majorResidualBranches P S
          · have hne : edge1 (A.F1edge j) ≠ edgeb e := by
              intro heq
              exact Finset.disjoint_left.mp hdisj1b
                (Finset.mem_image.mpr
                  ⟨A.F1edge j, Finset.mem_univ _, heq⟩)
                (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
            simp [hj0, hj1, hne] at hi
          · have hedgeSide : edgeb (A.Fbedge j) = edgeb e ∧
                orient j (segmentEndpointSide hT P optional i j a) = c := by
              simpa [hj0, hj1] using hi
            have hedge : A.Fbedge j = e := hedgeb hedgeSide.1
            rw [hierarchyCoordinatesAtSide, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_, ?_⟩
            · apply Finset.mem_filter.mpr
              refine ⟨(mem_FbSegments_iff hT P optional i).2
                ⟨j, ?_, hclass⟩, ?_⟩
              · have hjNotHalf : j ∉ halfBranches P := by
                  intro hjHalf
                  exact hj1 ((mem_majorResidualBranches P S j).2
                    ⟨hjHalf, hj0⟩)
                have hjCover : j ∈ halfBranches P ∪ minorBranches P := by
                  rw [halfBranches_union_minorBranches P]
                  exact Finset.mem_univ _
                exact (Finset.mem_union.mp hjCover).resolve_left hjNotHalf
              · exact ⟨j, hclass, hedge⟩
            · rw [hclass]
              exact hedgeSide.2
  · intro i hi
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨j, hjClass, -⟩ := hi'.2
    exact ⟨j, hjClass⟩
  · intro i hi j hjClass
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨k, hkMinor, hkClass⟩ :=
      (mem_FbSegments_iff hT P optional i).mp hi'.1
    obtain ⟨l, hlClass, hlEdge⟩ := hi'.2
    have hkj : k = j := Sum.inr.inj (hkClass.symm.trans hjClass)
    have hlj : l = j := Sum.inr.inj (hlClass.symm.trans hjClass)
    subst k
    subst l
    exact Finset.mem_filter.mpr ⟨hkMinor, hlEdge⟩

end

end Erdos547b.ZhaoClaim616HierarchyCoordinatePoolLoad

#print axioms Erdos547b.ZhaoClaim616HierarchyCoordinatePoolLoad.coordinatePoolLoad_edge1_le
#print axioms Erdos547b.ZhaoClaim616HierarchyCoordinatePoolLoad.coordinatePoolLoad_edgeb_le
