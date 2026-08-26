/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicRootTargets

/-!
# Root targets from fixed/adaptive branch-side plans

Threshold fibers have a source-determined orientation, whereas Appendix
fibers choose their orientation after the current live root pools are known.
Before roots are selected we can therefore list one side for a fixed branch
and both sides for an adaptive branch.  This module constructs that exact
finite target family and proves the membership interface used after local
realization.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicRootTargets

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment Bv I)
variable (Gdegree : SimpleGraph Bv) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ)
variable (R : SimpleGraph I) [DecidableRel R.Adj]
variable (miss : ℕ)
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

variable (P : ZhaoForestPartition T globalRoot small)
variable {available : Finset
  (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
variable {target slack : ℕ}
variable (S : SelectedF0 P available target slack)
variable {cap0 : K0 Q sourceDensity E0 → ℕ}
variable {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
variable {capb : Kb Q sourceDensity Mb → ℕ}
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
    cap0 cap1 capb)

/-- Allowed endpoint sides are recorded separately for branch roots and for
literal coordinates which may serve as cut parents.  This distinction is
essential: a side needed by a child attachment need not be adjacent to the
root which owns the whole branch. -/
structure RootTargetPlan where
  branchRootSides :
    ZhaoClaim615CoordinateSourceAllocation.BranchIndex P → Finset (Fin 2)
  coordinateSides :
    (Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
      Fin ((branchForest P).branches.size j)) → Finset (Fin 2)

/-- Physical targets permitted for one literal branch coordinate. -/
def plannedCoordinateTargets
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (allowed : Finset (Fin 2)) :
    Finset (RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb) :=
  allowed.image fun c ↦
    Sum.inr (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) j, c)

/-- Planned root targets of all branches owned by one component. -/
def plannedOwnedBranchTargets
    (plan : RootTargetPlan P) (q : Fin P.numParts) :
    Finset (RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb) :=
  ((Finset.univ : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)).filter
      fun j ↦ (branchForest P).owner j = q).biUnion fun j ↦
    plannedCoordinateTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A j (plan.branchRootSides j)

/-- Planned physical target(s) of the literal non-root cut parent. -/
def plannedNonrootCutParentTargets
    (plan : RootTargetPlan P) (q : Fin P.numParts) :
    Finset (RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb) :=
  if hq : q.val ≠ 0 then
    ((Finset.univ : Finset
        (Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
          Fin ((branchForest P).branches.size j))).filter
        fun z ↦ (partitionBranchEquivNonroots P z).1 = P.parent q hq).biUnion
      (fun z ↦ plannedCoordinateTargets Pcluster Gdegree threshold quota R
        miss Q sourceDensity E0 Mb P S A z.1 (plan.coordinateSides z))
  else ∅

/-- Complete pre-orientation target list for one distinguished root. -/
def richPlannedRootTargets
    (plan : RootTargetPlan P) (q : Fin P.numParts) :
    Finset (RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb) :=
  insert (Sum.inl (otherSide (componentReservoirSide P q)))
    (plannedOwnedBranchTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan q ∪
    plannedNonrootCutParentTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan q)

theorem plannedCoordinateTarget_mem
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (allowed : Finset (Fin 2))
    (c : Fin 2) (hc : c ∈ allowed) :
    (Sum.inr (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) j, c) :
      RichRootTarget Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb) ∈
      plannedCoordinateTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A j allowed := by
  exact Finset.mem_image.mpr ⟨c, hc, rfl⟩

theorem plannedBranchRootTarget_mem
    (plan : RootTargetPlan P)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (c : Fin 2) (hc : c ∈ plan.branchRootSides j) :
    (Sum.inr (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) j, c) :
      RichRootTarget Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb) ∈
      richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A plan ((branchForest P).owner j) := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, ?_⟩
  exact plannedCoordinateTarget_mem Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A j (plan.branchRootSides j) c hc

theorem plannedCoordinateTarget_mem_of_nonrootCutParent
    (plan : RootTargetPlan P)
    (q : Fin P.numParts) (hq : q.val ≠ 0)
    (hparentNonroot : P.parent q hq ∉ partitionRoots P)
    (c : Fin 2)
    (hc : c ∈ plan.coordinateSides
      (literalBranchCoordinate P (P.parent q hq) hparentNonroot)) :
    (Sum.inr (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)
        (literalBranchCoordinate P (P.parent q hq) hparentNonroot).1, c) :
      RichRootTarget Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb) ∈
      richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A plan q := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  rw [plannedNonrootCutParentTargets, dif_pos hq]
  apply Finset.mem_biUnion.mpr
  refine ⟨literalBranchCoordinate P (P.parent q hq) hparentNonroot,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · exact partitionBranchEquivNonroots_literalBranchCoordinate P
      (P.parent q hq) hparentNonroot
  · exact plannedCoordinateTarget_mem Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A
        (literalBranchCoordinate P (P.parent q hq) hparentNonroot).1
        (plan.coordinateSides
          (literalBranchCoordinate P (P.parent q hq) hparentNonroot)) c hc

/-- A concrete orientation is covered by a pre-cleaned plan once its actual
branch-root sides and its literal cut-parent sides are allowed.  No condition
is imposed on unrelated interior coordinates. -/
theorem richRootTargets_subset_planned
    (plan : RootTargetPlan P)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (hrootSide : ∀ j,
      orient j
          ((branchForest P).branches.isTree j |>.coloringTwoOfVert
            ((branchForest P).branches.root j)
            ((branchForest P).branches.root j)) ∈ plan.branchRootSides j)
    (hcutSide : ∀ q (hq : q.val ≠ 0)
      (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
        Fin ((branchForest P).branches.size j)),
      (partitionBranchEquivNonroots P z).1 = P.parent q hq →
      orient z.1
          ((branchForest P).branches.isTree z.1 |>.coloringTwoOfVert
            ((branchForest P).branches.root z.1) z.2) ∈
        plan.coordinateSides z)
    (q : Fin P.numParts) :
    richRootTargets Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb P S A orient q ⊆
      richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A plan q := by
  intro t ht
  rw [richRootTargets, Finset.mem_insert] at ht
  rcases ht with rfl | ht
  · simp [richPlannedRootTargets]
  · rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
      have howner := (Finset.mem_filter.mp hj).2
      rw [← howner]
      let c : Fin 2 :=
        orient j
          ((branchForest P).branches.isTree j |>.coloringTwoOfVert
            ((branchForest P).branches.root j)
            ((branchForest P).branches.root j))
      have hc : c ∈ plan.branchRootSides j := hrootSide j
      simpa only [branchRootTarget, coordinateTarget, c] using
        plannedBranchRootTarget_mem Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A plan j c hc
    · rw [nonrootCutParentTargets] at ht
      by_cases hq : q.val ≠ 0
      · rw [dif_pos hq] at ht
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
        have hzParent := (Finset.mem_filter.mp hz).2
        let c : Fin 2 :=
          orient z.1
            ((branchForest P).branches.isTree z.1 |>.coloringTwoOfVert
              ((branchForest P).branches.root z.1) z.2)
        have hc : c ∈ plan.coordinateSides z := hcutSide q hq z hzParent
        apply Finset.mem_insert_of_mem
        apply Finset.mem_union_right
        rw [plannedNonrootCutParentTargets, dif_pos hq]
        apply Finset.mem_biUnion.mpr
        refine ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzParent⟩, ?_⟩
        simpa only [coordinateTarget, c] using
          plannedCoordinateTarget_mem Pcluster Gdegree threshold quota R miss
            Q sourceDensity E0 Mb P S A z.1 (plan.coordinateSides z) c hc
      · rw [dif_neg hq] at ht
        simp at ht

end Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan

#print axioms Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan.plannedBranchRootTarget_mem
#print axioms Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan.plannedCoordinateTarget_mem_of_nonrootCutParent
#print axioms Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan.richRootTargets_subset_planned
