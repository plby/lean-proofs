/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalMatching
import ErdosProblems.Erdos547b.Claim615HierarchyCoordinatePoolLoad
import ErdosProblems.Erdos547b.Lemma58SelectedOrientationReindex

/-!
# Physical-fiber orientations and coordinate loads for Claim 6.15

Orientations produced independently on the three concrete matching families
are pasted through the canonical physical index.  The literal hierarchy load
of either endpoint is then at most the corresponding Lemma-5.4 side load on
that exact physical fiber.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim615HierarchyCoordinatePoolLoad
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58ChosenMatchingAssembly
open Erdos547b.ZhaoLemma58SelectedOrientationReindex
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable {Pcluster : ClusterAssignment Bv I}
variable {Gdegree : SimpleGraph Bv} [DecidableRel Gdegree.Adj]
variable {threshold quota : ℕ} {R : SimpleGraph I} [DecidableRel R.Adj]
variable {miss : ℕ}
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
variable (sourceDensity : EvenPadding I → EvenPadding I → ℝ)

variable {L : Finset (EvenPadding I)} {eta N targetB cap : ℝ}
variable {which : ExceptionalCase} {count cardBound : ℕ}
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta which count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
variable {available : Finset
  (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
variable (S : SelectedF0 P available target slack)
variable {cap0 : K0 Q sourceDensity E0 → ℕ}
variable {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
variable {capb : Kb Q sourceDensity Mb → ℕ}
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
    cap0 cap1 capb)

private abbrev physicalAssign :=
  assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
    (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)

@[simp] theorem indexedPhysicalEdge_exceptionalIndex
    (e : K0 Q sourceDensity E0) :
    indexedPhysicalEdge Q sourceDensity E0 Mb
        (exceptionalIndex Q sourceDensity E0 Mb e) =
      edge0 Q sourceDensity E0 e := by
  simp [indexedPhysicalEdge, exceptionalIndex, physicalEdge]

@[simp] theorem indexedPhysicalEdge_remainingIndex
    (e : K1 Q sourceDensity E0 Mb) :
    indexedPhysicalEdge Q sourceDensity E0 Mb
        (remainingIndex Q sourceDensity E0 Mb e) =
      edge1 Q sourceDensity E0 Mb e := by
  simp [indexedPhysicalEdge, remainingIndex, physicalEdge]

@[simp] theorem indexedPhysicalEdge_reservedIndex
    (e : Kb Q sourceDensity Mb) :
    indexedPhysicalEdge Q sourceDensity E0 Mb
        (reservedIndex Q sourceDensity E0 Mb e) =
      edgeb Q sourceDensity Mb e := by
  simp [indexedPhysicalEdge, reservedIndex, physicalEdge]

@[simp] theorem indexedRootSide_exceptionalIndex
    (e : K0 Q sourceDensity E0) :
    indexedRootSide Q sourceDensity E0 Mb
        (exceptionalIndex Q sourceDensity E0 Mb e) =
      rootSide0 Q sourceDensity E0 e := by
  simp [indexedRootSide, exceptionalIndex, physicalRootSide]

@[simp] theorem indexedRootSide_remainingIndex
    (e : K1 Q sourceDensity E0 Mb) :
    indexedRootSide Q sourceDensity E0 Mb
        (remainingIndex Q sourceDensity E0 Mb e) =
      rootSide1 Q sourceDensity E0 Mb e := by
  simp [indexedRootSide, remainingIndex, physicalRootSide]

@[simp] theorem indexedRootSide_reservedIndex
    (e : Kb Q sourceDensity Mb) :
    indexedRootSide Q sourceDensity E0 Mb
        (reservedIndex Q sourceDensity E0 Mb e) =
      rootSideb Q sourceDensity Mb e := by
  simp [indexedRootSide, reservedIndex, physicalRootSide]

/-- The distinguished reduced vertex supplying roots on a physical family:
`A` for the exceptional and remaining families, and `B` for the reserved
family. -/
def physicalRootVertex (e : PhysicalIndex Q sourceDensity E0 Mb) :
    EvenPadding I :=
  match (Fintype.equivFin
      (PhysicalEdge Q sourceDensity E0 Mb)).symm e with
  | Sum.inl _ => Sum.inl Q.A
  | Sum.inr (Sum.inl _) => Sum.inl Q.A
  | Sum.inr (Sum.inr _) => Sum.inl Q.B

@[simp] theorem physicalRootVertex_exceptionalIndex
    (e : K0 Q sourceDensity E0) :
    physicalRootVertex Q sourceDensity E0 Mb
        (exceptionalIndex Q sourceDensity E0 Mb e) = Sum.inl Q.A := by
  simp [physicalRootVertex, exceptionalIndex]

@[simp] theorem physicalRootVertex_remainingIndex
    (e : K1 Q sourceDensity E0 Mb) :
    physicalRootVertex Q sourceDensity E0 Mb
        (remainingIndex Q sourceDensity E0 Mb e) = Sum.inl Q.A := by
  simp [physicalRootVertex, remainingIndex]

@[simp] theorem physicalRootVertex_reservedIndex
    (e : Kb Q sourceDensity Mb) :
    physicalRootVertex Q sourceDensity E0 Mb
        (reservedIndex Q sourceDensity E0 Mb e) = Sum.inl Q.B := by
  simp [physicalRootVertex, reservedIndex]

/-- Paste one locally chosen orientation on every physical matching fiber. -/
def physicalFiberOrient
    (localOrient : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
      Fin (matchingFiber
        (physicalAssign Q sourceDensity E0 Mb P S A) e).card → Fin 2 ≃ Fin 2) :
    ZhaoClaim615CoordinateSourceAllocation.BranchIndex P → Fin 2 ≃ Fin 2 :=
  assembledOrient (physicalAssign Q sourceDensity E0 Mb P S A)
    (fun e ↦ extendSelectedOrient
      (matchingFiber (physicalAssign Q sourceDensity E0 Mb P S A) e)
      (localOrient e))

theorem physicalFiberOrient_apply
    (localOrient : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
      Fin (matchingFiber
        (physicalAssign Q sourceDensity E0 Mb P S A) e).card → Fin 2 ≃ Fin 2)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) :
    physicalFiberOrient Q sourceDensity E0 Mb P S A localOrient j =
      localOrient (physicalAssign Q sourceDensity E0 Mb P S A j)
        (assignmentIndex (physicalAssign Q sourceDensity E0 Mb P S A) j) := by
  exact assembledOrient_apply_eq_localOrient_assignmentIndex
    (physicalAssign Q sourceDensity E0 Mb P S A) localOrient j

/-- One source-row adjacency statement on every local physical fiber implies
the exceptional-family root statement for the pasted orientation. -/
theorem physicalFiberOrient_selected_root_adj
    (localOrient : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
      Fin (matchingFiber
        (physicalAssign Q sourceDensity E0 Mb P S A) e).card → Fin 2 ≃ Fin 2)
    (hlocal : ∀ e i,
      (padGraph R).Adj (physicalRootVertex Q sourceDensity E0 Mb e)
        (matchingEdgeEndpoint (indexedPhysicalEdge Q sourceDensity E0 Mb e).1
          (localOrient e i 0)))
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ S.selected) :
    (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge0 Q sourceDensity E0 (A.F0edge j)).1
        (physicalFiberOrient Q sourceDensity E0 Mb P S A localOrient j 0)) := by
  have hidx : physicalAssign Q sourceDensity E0 Mb P S A j =
      exceptionalIndex Q sourceDensity E0 Mb (A.F0edge j) :=
    (assignedPhysicalIndex_eq_exceptional_iff
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) j (A.F0edge j)).2 ⟨hj, rfl⟩
  rw [physicalFiberOrient_apply]
  have hroot := hlocal (physicalAssign Q sourceDensity E0 Mb P S A j)
    (assignmentIndex (physicalAssign Q sourceDensity E0 Mb P S A) j)
  simpa only [physicalRootVertex_exceptionalIndex,
    indexedPhysicalEdge_exceptionalIndex, hidx] using hroot

/-- The same local statement implies the remaining-family root statement. -/
theorem physicalFiberOrient_residual_root_adj
    (localOrient : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
      Fin (matchingFiber
        (physicalAssign Q sourceDensity E0 Mb P S A) e).card → Fin 2 ≃ Fin 2)
    (hlocal : ∀ e i,
      (padGraph R).Adj (physicalRootVertex Q sourceDensity E0 Mb e)
        (matchingEdgeEndpoint (indexedPhysicalEdge Q sourceDensity E0 Mb e).1
          (localOrient e i 0)))
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ majorResidualBranches P S) :
    (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint
        (edge1 Q sourceDensity E0 Mb (A.F1edge j)).1
        (physicalFiberOrient Q sourceDensity E0 Mb P S A localOrient j 0)) := by
  have hidx : physicalAssign Q sourceDensity E0 Mb P S A j =
      remainingIndex Q sourceDensity E0 Mb (A.F1edge j) :=
    (assignedPhysicalIndex_eq_remaining_iff
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) j (A.F1edge j)).2 ⟨hj, rfl⟩
  rw [physicalFiberOrient_apply]
  have hroot := hlocal (physicalAssign Q sourceDensity E0 Mb P S A j)
    (assignmentIndex (physicalAssign Q sourceDensity E0 Mb P S A) j)
  simpa only [physicalRootVertex_remainingIndex,
    indexedPhysicalEdge_remainingIndex, hidx] using hroot

/-- The same local statement implies the reserved-family root statement. -/
theorem physicalFiberOrient_minor_root_adj
    (havailable : available ⊆ halfBranches P)
    (localOrient : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
      Fin (matchingFiber
        (physicalAssign Q sourceDensity E0 Mb P S A) e).card → Fin 2 ≃ Fin 2)
    (hlocal : ∀ e i,
      (padGraph R).Adj (physicalRootVertex Q sourceDensity E0 Mb e)
        (matchingEdgeEndpoint (indexedPhysicalEdge Q sourceDensity E0 Mb e).1
          (localOrient e i 0)))
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (hj : j ∈ minorBranches P) :
    (padGraph R).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (edgeb Q sourceDensity Mb (A.Fbedge j)).1
        (physicalFiberOrient Q sourceDensity E0 Mb P S A localOrient j 0)) := by
  have hidx : physicalAssign Q sourceDensity E0 Mb P S A j =
      reservedIndex Q sourceDensity E0 Mb (A.Fbedge j) :=
    (assignedPhysicalIndex_eq_reserved_iff
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) havailable j (A.Fbedge j)).2 ⟨hj, rfl⟩
  rw [physicalFiberOrient_apply]
  have hroot := hlocal (physicalAssign Q sourceDensity E0 Mb P S A j)
    (assignmentIndex (physicalAssign Q sourceDensity E0 Mb P S A) j)
  simpa only [physicalRootVertex_reservedIndex,
    indexedPhysicalEdge_reservedIndex, hidx] using hroot

/-- The source edge attached to a branch is exactly the physical edge at its
canonical assignment index. -/
theorem coordinateBranchEdge_eq_indexedPhysicalAssigned
    (havailable : available ⊆ halfBranches P)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) :
    coordinateBranchEdge P S
        cap0 cap1 capb A
        (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
        (edgeb Q sourceDensity Mb) j =
      indexedPhysicalEdge Q sourceDensity E0 Mb
        (physicalAssign Q sourceDensity E0 Mb P S A j) := by
  by_cases hj0 : j ∈ S.selected
  · rw [coordinateBranchEdge, dif_pos hj0]
    exact (indexedPhysicalEdge_assigned_selected
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) j hj0).symm
  · by_cases hj1 : j ∈ majorResidualBranches P S
    · rw [coordinateBranchEdge, dif_neg hj0, dif_pos hj1]
      exact (indexedPhysicalEdge_assigned_residual
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j hj1).symm
    · have hjHalf : j ∉ halfBranches P := by
        intro hj
        exact hj1 ((mem_majorResidualBranches P S j).2 ⟨hj, hj0⟩)
      have hjMinor : j ∈ minorBranches P := by
        have hu : j ∈ halfBranches P ∪ minorBranches P := by
          rw [halfBranches_union_minorBranches]
          exact Finset.mem_univ _
        exact (Finset.mem_union.mp hu).resolve_left hjHalf
      rw [coordinateBranchEdge, dif_neg hj0, dif_neg hj1]
      exact (indexedPhysicalEdge_assigned_minor
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) havailable j hjMinor).symm

/-- Exact endpoint load comparison with the side load of the reindexed
physical fiber. -/
theorem coordinatePoolLoad_physical_le_sideLoad
    (optional distinguished : Finset V) (distinguishedSide : V → Fin 2)
    (havailable : available ⊆ halfBranches P)
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (localOrient : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
      Fin (matchingFiber
        (physicalAssign Q sourceDensity E0 Mb P S A) e).card → Fin 2 ≃ Fin 2)
    (e : PhysicalIndex Q sourceDensity E0 Mb) (c : Fin 2) :
    coordinatePoolLoad (AllocationHierarchy hT P optional)
        (coordinateHierarchyRootSlot hT P optional distinguished
          distinguishedSide S
          cap0 cap1 capb A
          (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
          (edgeb Q sourceDensity Mb)
          (physicalFiberOrient Q sourceDensity E0 Mb P S A localOrient))
        (coordinateHierarchyInteriorSlot hT P optional S
          cap0 cap1 capb A
          (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
          (edgeb Q sourceDensity Mb)
          (physicalFiberOrient Q sourceDensity E0 Mb P S A localOrient))
        (Sum.inr ⟨indexedPhysicalEdge Q sourceDensity E0 Mb e, c⟩ :
          RootSlot (MatchingEdge Q.claim67.M)) ≤
      sideLoad
        (selectedForest (branchForest P).branches
          (matchingFiber (physicalAssign Q sourceDensity E0 Mb P S A) e))
        (localOrient e) c := by
  let assign := physicalAssign Q sourceDensity E0 Mb P S A
  let orient := physicalFiberOrient Q sourceDensity E0 Mb P S A localOrient
  calc
    _ ≤ ∑ j ∈ matchingFiber assign e,
        orientedClassSize (branchForest P).branches orient j c := by
      apply coordinatePoolLoad_le_family_side_load hT P optional distinguished
        distinguishedSide S
        cap0 cap1 capb A
        (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
        (edgeb Q sourceDensity Mb) orient
        (indexedPhysicalEdge Q sourceDensity E0 Mb e)
        (matchingFiber assign e) c
      intro j
      rw [mem_matchingFiber]
      rw [coordinateBranchEdge_eq_indexedPhysicalAssigned Q sourceDensity E0
        Mb P S A havailable j]
      exact (indexedPhysicalEdge_injective Q sourceDensity E0 Mb
        hdisjoint).eq_iff
    _ = _ := (sideLoad_matchingFiber_assembledOrient
      (branchForest P).branches assign localOrient e c).symm

/-- Any real-valued margin proved for the local Lemma-5.4 side load also
holds for the literal hierarchy occupancy at the corresponding endpoint. -/
theorem coordinatePoolLoad_physical_margin
    (optional distinguished : Finset V) (distinguishedSide : V → Fin 2)
    (havailable : available ⊆ halfBranches P)
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (localOrient : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
      Fin (matchingFiber
        (physicalAssign Q sourceDensity E0 Mb P S A) e).card → Fin 2 ≃ Fin 2)
    (e : PhysicalIndex Q sourceDensity E0 Mb) (c : Fin 2)
    (removal rhs : ℝ)
    (hmargin :
      (sideLoad
          (selectedForest (branchForest P).branches
            (matchingFiber (physicalAssign Q sourceDensity E0 Mb P S A) e))
          (localOrient e) c : ℝ) + small + 1 + removal + 1 ≤ rhs) :
    (coordinatePoolLoad (AllocationHierarchy hT P optional)
          (coordinateHierarchyRootSlot hT P optional distinguished
            distinguishedSide S
            cap0 cap1 capb A
            (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
            (edgeb Q sourceDensity Mb)
            (physicalFiberOrient Q sourceDensity E0 Mb P S A localOrient))
          (coordinateHierarchyInteriorSlot hT P optional S
            cap0 cap1 capb A
            (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
            (edgeb Q sourceDensity Mb)
            (physicalFiberOrient Q sourceDensity E0 Mb P S A localOrient))
          (Sum.inr ⟨indexedPhysicalEdge Q sourceDensity E0 Mb e, c⟩ :
            RootSlot (MatchingEdge Q.claim67.M)) : ℝ) +
        small + 1 + removal + 1 ≤ rhs := by
  have hload := coordinatePoolLoad_physical_le_sideLoad
    Q sourceDensity E0 Mb hT P S A optional distinguished distinguishedSide
      havailable hdisjoint localOrient e c
  have hloadR :
      (coordinatePoolLoad (AllocationHierarchy hT P optional)
          (coordinateHierarchyRootSlot hT P optional distinguished
            distinguishedSide S
            cap0 cap1 capb A
            (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
            (edgeb Q sourceDensity Mb)
            (physicalFiberOrient Q sourceDensity E0 Mb P S A localOrient))
          (coordinateHierarchyInteriorSlot hT P optional S
            cap0 cap1 capb A
            (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
            (edgeb Q sourceDensity Mb)
            (physicalFiberOrient Q sourceDensity E0 Mb P S A localOrient))
          (Sum.inr ⟨indexedPhysicalEdge Q sourceDensity E0 Mb e, c⟩ :
            RootSlot (MatchingEdge Q.claim67.M)) : ℝ) ≤
        sideLoad
          (selectedForest (branchForest P).branches
            (matchingFiber (physicalAssign Q sourceDensity E0 Mb P S A) e))
          (localOrient e) c := by
    exact_mod_cast hload
  linarith

end Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads

#print axioms Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads.coordinateBranchEdge_eq_indexedPhysicalAssigned
#print axioms Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads.coordinatePoolLoad_physical_le_sideLoad
#print axioms Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads.coordinatePoolLoad_physical_margin
