/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615HierarchicalCoordinateSourceLayout
import ErdosProblems.Erdos547b.Claim616HierarchyCoordinateSide

/-!
# Endpoint loads for the coordinate version of Zhao Lemma 6.15

Every matching endpoint is charged only for the hierarchy coordinates that
actually land in that endpoint.  The generic theorem first bounds a physical
endpoint by the corresponding oriented colour-class sum.  Three corollaries
identify the selected, residual-major, and minor fibers of the finite source
allocation.  No host graph or embedding is used.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615HierarchyCoordinatePoolLoad

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchyCoordinateSide
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

section

variable
    {K0 K1 Kb Edge : Type*}
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    [DecidableEq Edge]

variable
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional distinguished : Finset V)
    (distinguishedSide : V → Fin 2)
    {available : Finset (BranchIndex P)} {target slack : ℕ}
    (S : ZhaoClaim615SourceSelection.SelectedF0 P available target slack)
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ)
    (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (edge0 : K0 → Edge) (edge1 : K1 → Edge) (edgeb : Kb → Edge)
    (orient : BranchIndex P → Fin 2 ≃ Fin 2)

private abbrev sourceRootPool :=
  coordinateHierarchyRootSlot hT P optional distinguished distinguishedSide S
    capacity0 capacity1 capacityb A edge0 edge1 edgeb orient

private abbrev sourceInteriorPool :=
  coordinateHierarchyInteriorSlot hT P optional S capacity0 capacity1
    capacityb A edge0 edge1 edgeb orient

/-- Hierarchy segments whose source class belongs to a displayed branch
family. -/
noncomputable def familySegments (B : Finset (BranchIndex P)) :
    Finset (SegmentIndex hT P optional) :=
  Finset.univ.filter fun i ↦ ∃ j ∈ B,
    segmentSourceClass hT P optional i = Sum.inr j

/-- Generic endpoint accounting once the branches using one physical edge
have been identified exactly. -/
theorem coordinatePoolLoad_le_family_side_load
    (physicalEdge : Edge) (B : Finset (BranchIndex P)) (c : Fin 2)
    (hedge : ∀ j, coordinateBranchEdge P S capacity0 capacity1 capacityb A
      edge0 edge1 edgeb j = physicalEdge ↔ j ∈ B) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional distinguished distinguishedSide S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
        (sourceInteriorPool hT P optional S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb orient)
        (Sum.inr ⟨physicalEdge, c⟩ : RootSlot Edge) ≤
      ∑ j ∈ B, orientedClassSize (branchForest P).branches orient j c := by
  classical
  apply coordinatePoolLoad_le_branch_side_load hT P optional
    (sourceRootPool hT P optional distinguished distinguishedSide S capacity0
      capacity1 capacityb A edge0 edge1 edgeb orient)
    (sourceInteriorPool hT P optional S capacity0 capacity1 capacityb A edge0
      edge1 edgeb orient)
    (Sum.inr ⟨physicalEdge, c⟩ : RootSlot Edge)
    (familySegments hT P optional B) B orient c
  · intro i hi
    by_cases hid : SegmentRootOriginal hT P optional i ∈ distinguished
    · simp [sourceRootPool, coordinateHierarchyRootSlot, hid] at hi
    · cases hclass : segmentSourceClass hT P optional i with
      | inl q =>
          unfold sourceRootPool at hi
          rw [coordinateHierarchyRootSlot_component hT P optional distinguished
            distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1
            edgeb orient i q hid hclass] at hi
          cases hi
      | inr j =>
          unfold sourceRootPool at hi
          rw [coordinateHierarchyRootSlot_branch hT P optional distinguished
            distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1
            edgeb orient i j hid hclass] at hi
          have hpair :
              coordinateBranchEdge P S capacity0 capacity1 capacityb A edge0
                    edge1 edgeb j = physicalEdge ∧
                orient j (segmentEndpointSide hT P optional i j
                  ((AllocationHierarchy hT P optional).segments.root i)) = c := by
            simpa [coordinateBranchSlot] using hi
          rw [hierarchyCoordinatesAtSide, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_, ?_⟩
          · rw [familySegments, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, j, (hedge j).mp hpair.1, hclass⟩
          · rw [hclass]
            exact hpair.2
  · intro i a _ha hi
    cases hclass : segmentSourceClass hT P optional i with
    | inl q =>
        unfold sourceInteriorPool at hi
        rw [coordinateHierarchyInteriorSlot_component hT P optional S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i q hclass
          a] at hi
        cases hi
    | inr j =>
        unfold sourceInteriorPool at hi
        rw [coordinateHierarchyInteriorSlot_branch hT P optional S capacity0
          capacity1 capacityb A edge0 edge1 edgeb orient i j hclass a] at hi
        have hpair :
            coordinateBranchEdge P S capacity0 capacity1 capacityb A edge0
                  edge1 edgeb j = physicalEdge ∧
              orient j (segmentEndpointSide hT P optional i j a) = c := by
          simpa [coordinateBranchSlot] using hi
        rw [hierarchyCoordinatesAtSide, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · rw [familySegments, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, j, (hedge j).mp hpair.1, hclass⟩
        · rw [hclass]
          exact hpair.2
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    exact hi'.elim fun j hj ↦ ⟨j, hj.2⟩
  · intro i hi j hclass
    have hi' := (Finset.mem_filter.mp hi).2
    obtain ⟨k, hkB, hkclass⟩ := hi'
    have hkj : k = j := Sum.inr.inj (hkclass.symm.trans hclass)
    exact hkj ▸ hkB

private theorem branchEdge_eq_edge0_iff
    (hedge0 : Function.Injective edge0)
    (h01 : ∀ e0 e1, edge0 e0 ≠ edge1 e1)
    (h0b : ∀ e0 eb, edge0 e0 ≠ edgeb eb)
    (e : K0) (j : BranchIndex P) :
    coordinateBranchEdge P S capacity0 capacity1 capacityb A edge0 edge1
        edgeb j = edge0 e ↔
      j ∈ S.selected.filter (A.F0edge · = e) := by
  by_cases hj0 : j ∈ S.selected
  · simp only [coordinateBranchEdge, hj0, dite_true, Finset.mem_filter, hj0,
      true_and]
    exact hedge0.eq_iff
  · by_cases hj1 : j ∈ majorResidualBranches P S
    · constructor
      · intro heq
        rw [coordinateBranchEdge, dif_neg hj0, dif_pos hj1] at heq
        exact False.elim (h01 e (A.F1edge j) heq.symm)
      · simp [hj0]
    · constructor
      · intro heq
        rw [coordinateBranchEdge, dif_neg hj0, dif_neg hj1] at heq
        exact False.elim (h0b e (A.Fbedge j) heq.symm)
      · simp [hj0]

private theorem branchEdge_eq_edge1_iff
    (hedge1 : Function.Injective edge1)
    (h01 : ∀ e0 e1, edge0 e0 ≠ edge1 e1)
    (h1b : ∀ e1 eb, edge1 e1 ≠ edgeb eb)
    (e : K1) (j : BranchIndex P) :
    coordinateBranchEdge P S capacity0 capacity1 capacityb A edge0 edge1
        edgeb j = edge1 e ↔
      j ∈ (majorResidualBranches P S).filter (A.F1edge · = e) := by
  by_cases hj0 : j ∈ S.selected
  · constructor
    · intro heq
      rw [coordinateBranchEdge, dif_pos hj0] at heq
      exact False.elim (h01 (A.F0edge j) e heq)
    · simp [hj0]
  · by_cases hj1 : j ∈ majorResidualBranches P S
    · simp only [coordinateBranchEdge, hj0, dite_false, hj1, dite_true,
        Finset.mem_filter, hj1, true_and]
      exact hedge1.eq_iff
    · constructor
      · intro heq
        rw [coordinateBranchEdge, dif_neg hj0, dif_neg hj1] at heq
        exact False.elim (h1b e (A.Fbedge j) heq.symm)
      · simp [hj1]

private theorem branchEdge_eq_edgeb_iff
    (havailable : available ⊆ halfBranches P)
    (hedgeb : Function.Injective edgeb)
    (h0b : ∀ e0 eb, edge0 e0 ≠ edgeb eb)
    (h1b : ∀ e1 eb, edge1 e1 ≠ edgeb eb)
    (e : Kb) (j : BranchIndex P) :
    coordinateBranchEdge P S capacity0 capacity1 capacityb A edge0 edge1
        edgeb j = edgeb e ↔
      j ∈ (ZhaoClaim616ResidualAllocation.minorBranches P).filter
        (A.Fbedge · = e) := by
  have hselectedHalf : S.selected ⊆ halfBranches P :=
    S.selected_available.trans havailable
  by_cases hj0 : j ∈ S.selected
  · constructor
    · intro heq
      rw [coordinateBranchEdge, dif_pos hj0] at heq
      exact False.elim (h0b (A.F0edge j) e heq)
    · intro hj
      exact (Finset.disjoint_left.mp
        (ZhaoClaim616ResidualAllocation.halfBranches_disjoint_minorBranches P)
        (hselectedHalf hj0) (Finset.mem_filter.mp hj).1).elim
  · by_cases hj1 : j ∈ majorResidualBranches P S
    · constructor
      · intro heq
        rw [coordinateBranchEdge, dif_neg hj0, dif_pos hj1] at heq
        exact False.elim (h1b (A.F1edge j) e heq)
      · intro hj
        exact (Finset.disjoint_left.mp
          (ZhaoClaim616ResidualAllocation.halfBranches_disjoint_minorBranches P)
          (mem_majorResidualBranches P S j |>.mp hj1).1
          (Finset.mem_filter.mp hj).1).elim
    · have hjMinor : j ∈ ZhaoClaim616ResidualAllocation.minorBranches P := by
        have hjNotHalf : j ∉ halfBranches P := by
          intro hjHalf
          exact hj1 ((mem_majorResidualBranches P S j).2 ⟨hjHalf, hj0⟩)
        have hjCover : j ∈ halfBranches P ∪
            ZhaoClaim616ResidualAllocation.minorBranches P := by
          rw [ZhaoClaim616ResidualAllocation.halfBranches_union_minorBranches P]
          exact Finset.mem_univ _
        exact (Finset.mem_union.mp hjCover).resolve_left hjNotHalf
      simp only [coordinateBranchEdge, hj0, dite_false, hj1,
        Finset.mem_filter, hjMinor, true_and]
      exact hedgeb.eq_iff

theorem coordinatePoolLoad_edge0_le
    (hedge0 : Function.Injective edge0)
    (h01 : ∀ e0 e1, edge0 e0 ≠ edge1 e1)
    (h0b : ∀ e0 eb, edge0 e0 ≠ edgeb eb)
    (e : K0) (c : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional distinguished distinguishedSide S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
        (sourceInteriorPool hT P optional S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb orient)
        (Sum.inr ⟨edge0 e, c⟩ : RootSlot Edge) ≤
      ∑ j ∈ S.selected.filter (A.F0edge · = e),
        orientedClassSize (branchForest P).branches orient j c := by
  apply coordinatePoolLoad_le_family_side_load hT P optional distinguished
    distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1 edgeb
    orient (edge0 e) _ c
  exact branchEdge_eq_edge0_iff P S capacity0 capacity1 capacityb A edge0
    edge1 edgeb hedge0 h01 h0b e

theorem coordinatePoolLoad_edge1_le
    (hedge1 : Function.Injective edge1)
    (h01 : ∀ e0 e1, edge0 e0 ≠ edge1 e1)
    (h1b : ∀ e1 eb, edge1 e1 ≠ edgeb eb)
    (e : K1) (c : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional distinguished distinguishedSide S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
        (sourceInteriorPool hT P optional S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb orient)
        (Sum.inr ⟨edge1 e, c⟩ : RootSlot Edge) ≤
      ∑ j ∈ (majorResidualBranches P S).filter (A.F1edge · = e),
        orientedClassSize (branchForest P).branches orient j c := by
  apply coordinatePoolLoad_le_family_side_load hT P optional distinguished
    distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1 edgeb
    orient (edge1 e) _ c
  exact branchEdge_eq_edge1_iff P S capacity0 capacity1 capacityb A edge0
    edge1 edgeb hedge1 h01 h1b e

theorem coordinatePoolLoad_edgeb_le
    (havailable : available ⊆ halfBranches P)
    (hedgebInj : Function.Injective edgeb)
    (h0b : ∀ e0 eb, edge0 e0 ≠ edgeb eb)
    (h1b : ∀ e1 eb, edge1 e1 ≠ edgeb eb)
    (e : Kb) (c : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional distinguished distinguishedSide S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
        (sourceInteriorPool hT P optional S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb orient)
        (Sum.inr ⟨edgeb e, c⟩ : RootSlot Edge) ≤
      ∑ j ∈ (ZhaoClaim616ResidualAllocation.minorBranches P).filter
          (A.Fbedge · = e),
        orientedClassSize (branchForest P).branches orient j c := by
  apply coordinatePoolLoad_le_family_side_load hT P optional distinguished
    distinguishedSide S capacity0 capacity1 capacityb A edge0 edge1 edgeb
    orient (edgeb e) _ c
  exact branchEdge_eq_edgeb_iff P S capacity0 capacity1 capacityb A edge0
    edge1 edgeb havailable hedgebInj h0b h1b e

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

/-- A selected exceptional endpoint carries at most its integral packing
capacity. -/
theorem coordinatePoolLoad_edge0_le_capacity
    (hedge0 : Function.Injective edge0)
    (h01 : ∀ e0 e1, edge0 e0 ≠ edge1 e1)
    (h0b : ∀ e0 eb, edge0 e0 ≠ edgeb eb)
    (e : K0) (c : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional distinguished distinguishedSide S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
        (sourceInteriorPool hT P optional S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb orient)
        (Sum.inr ⟨edge0 e, c⟩ : RootSlot Edge) ≤ capacity0 e := by
  calc
    _ ≤ ∑ j ∈ S.selected.filter (A.F0edge · = e),
        orientedClassSize (branchForest P).branches orient j c :=
      coordinatePoolLoad_edge0_le hT P optional distinguished distinguishedSide
        S capacity0 capacity1 capacityb A edge0 edge1 edgeb orient hedge0 h01
        h0b e c
    _ ≤ ∑ j ∈ S.selected.filter (A.F0edge · = e),
        (branchForest P).branches.size j := by
      apply Finset.sum_le_sum
      intro j _
      exact orientedClassSize_le_branchSize P orient j c
    _ ≤ capacity0 e := A.F0_load e

/-- A residual-major endpoint carries at most its integral packing capacity. -/
theorem coordinatePoolLoad_edge1_le_capacity
    (hedge1 : Function.Injective edge1)
    (h01 : ∀ e0 e1, edge0 e0 ≠ edge1 e1)
    (h1b : ∀ e1 eb, edge1 e1 ≠ edgeb eb)
    (e : K1) (c : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional distinguished distinguishedSide S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
        (sourceInteriorPool hT P optional S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb orient)
        (Sum.inr ⟨edge1 e, c⟩ : RootSlot Edge) ≤ capacity1 e := by
  calc
    _ ≤ ∑ j ∈ (majorResidualBranches P S).filter (A.F1edge · = e),
        orientedClassSize (branchForest P).branches orient j c :=
      coordinatePoolLoad_edge1_le hT P optional distinguished distinguishedSide
        S capacity0 capacity1 capacityb A edge0 edge1 edgeb orient hedge1 h01
        h1b e c
    _ ≤ ∑ j ∈ (majorResidualBranches P S).filter (A.F1edge · = e),
        (branchForest P).branches.size j := by
      apply Finset.sum_le_sum
      intro j _
      exact orientedClassSize_le_branchSize P orient j c
    _ ≤ capacity1 e := A.F1_load e

/-- A minor endpoint carries at most its integral packing capacity. -/
theorem coordinatePoolLoad_edgeb_le_capacity
    (havailable : available ⊆ halfBranches P)
    (hedgebInj : Function.Injective edgeb)
    (h0b : ∀ e0 eb, edge0 e0 ≠ edgeb eb)
    (h1b : ∀ e1 eb, edge1 e1 ≠ edgeb eb)
    (e : Kb) (c : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (sourceRootPool hT P optional distinguished distinguishedSide S
          capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
        (sourceInteriorPool hT P optional S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb orient)
        (Sum.inr ⟨edgeb e, c⟩ : RootSlot Edge) ≤ capacityb e := by
  calc
    _ ≤ ∑ j ∈ (ZhaoClaim616ResidualAllocation.minorBranches P).filter
        (A.Fbedge · = e),
        orientedClassSize (branchForest P).branches orient j c :=
      coordinatePoolLoad_edgeb_le hT P optional distinguished distinguishedSide
        S capacity0 capacity1 capacityb A edge0 edge1 edgeb orient havailable
        hedgebInj h0b h1b e c
    _ ≤ ∑ j ∈ (ZhaoClaim616ResidualAllocation.minorBranches P).filter
        (A.Fbedge · = e),
        (branchForest P).branches.size j := by
      apply Finset.sum_le_sum
      intro j _
      exact orientedClassSize_le_branchSize P orient j c
    _ ≤ capacityb e := A.Fb_load e

end

end Erdos547b.ZhaoClaim615HierarchyCoordinatePoolLoad

#print axioms Erdos547b.ZhaoClaim615HierarchyCoordinatePoolLoad.coordinatePoolLoad_edge0_le
#print axioms Erdos547b.ZhaoClaim615HierarchyCoordinatePoolLoad.coordinatePoolLoad_edge1_le
#print axioms Erdos547b.ZhaoClaim615HierarchyCoordinatePoolLoad.coordinatePoolLoad_edgeb_le
#print axioms Erdos547b.ZhaoClaim615HierarchyCoordinatePoolLoad.coordinatePoolLoad_edge0_le_capacity
#print axioms Erdos547b.ZhaoClaim615HierarchyCoordinatePoolLoad.coordinatePoolLoad_edge1_le_capacity
#print axioms Erdos547b.ZhaoClaim615HierarchyCoordinatePoolLoad.coordinatePoolLoad_edgeb_le_capacity
