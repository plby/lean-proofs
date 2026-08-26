/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicRootApplication
import ErdosProblems.Erdos547b.Lemma54CanonicalThresholdOrientation

/-!
# Exact oriented root targets for dynamic Zhao Claim 6.15

For a fixed source orientation, a component root needs typicality only toward
three kinds of actual targets:

* the opposite distinguished reservoir for a root-to-root cut edge;
* the oriented root endpoint of every branch it owns; and
* the oriented endpoint containing its own non-root cut parent.

The target type forgets source-coordinate duplicates and remembers only the
physical matching edge and endpoint side.  Thus the regularity loss is
charged per genuine host target, not per source vertex.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichDynamicRootTargets

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ParityHalf
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
open Erdos547b.ZhaoClaim615RichDynamicRootLayout

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

/-- A distinguished-root side, or one physical matching endpoint. -/
abbrev RichRootTarget := Sum (Fin 2)
  (PhysicalIndex Q sourceDensity E0 Mb × Fin 2)

/-- Physical target occupied by one oriented source coordinate. -/
def coordinateTarget
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
      Fin ((branchForest P).branches.size j)) :
    RichRootTarget Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb :=
  Sum.inr
    (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) z.1,
    orient z.1
      ((branchForest P).branches.isTree z.1 |>.coloringTwoOfVert
        ((branchForest P).branches.root z.1) z.2))

/-- Physical target of one branch root. -/
def branchRootTarget
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) :
    RichRootTarget Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb :=
  coordinateTarget Pcluster Gdegree threshold quota R miss Q sourceDensity
    E0 Mb P S A orient ⟨j, (branchForest P).branches.root j⟩

/-- Actual oriented matching targets of branches owned by `q`. -/
def ownedBranchTargets
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (q : Fin P.numParts) :
    Finset (RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb) :=
  ((Finset.univ : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)).filter
      fun j ↦ (branchForest P).owner j = q).image
    (branchRootTarget Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S A orient)

/-- Actual oriented endpoint containing the non-root cut parent of `q`,
expressed by scanning the canonical branch-coordinate equivalence. -/
def nonrootCutParentTargets
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (q : Fin P.numParts) :
    Finset (RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb) :=
  if hq : q.val ≠ 0 then
    ((Finset.univ : Finset
        (Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
          Fin ((branchForest P).branches.size j))).filter
        fun z ↦ (partitionBranchEquivNonroots P z).1 = P.parent q hq).image
      (coordinateTarget Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A orient)
  else ∅

/-- Complete exact target list for one distinguished root. -/
def richRootTargets
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (q : Fin P.numParts) :
    Finset (RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb) :=
  insert (Sum.inl (otherSide (componentReservoirSide P q)))
    (ownedBranchTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A orient q ∪
    nonrootCutParentTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A orient q)

/-- Whole host set represented by an exact root target. -/
def richTargetWhole :
    RichRootTarget Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb → Finset Bv
  | Sum.inl side =>
      rootWholeSide Pcluster Gdegree threshold quota R miss Q side
  | Sum.inr (e, c) =>
      richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        e c

/-- Raw host set represented by an exact root target. -/
def richTargetRaw :
    RichRootTarget Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb → Finset Bv
  | Sum.inl side =>
      rootRawSide Pcluster Gdegree threshold quota R miss Q side
  | Sum.inr (e, c) =>
      richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        e c

theorem oppositeRootTarget_mem
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (q : Fin P.numParts) :
    Sum.inl (otherSide (componentReservoirSide P q)) ∈
      richRootTargets Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb P S A orient q := by
  simp [richRootTargets]

theorem branchRootTarget_mem
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) :
    branchRootTarget Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb P S A orient j ∈
      richRootTargets Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb P S A orient ((branchForest P).owner j) := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩

theorem coordinateTarget_mem_of_nonrootCutParent
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (q : Fin P.numParts) (hq : q.val ≠ 0)
    (hparentNonroot : P.parent q hq ∉ partitionRoots P) :
    coordinateTarget Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb P S A orient
        (literalBranchCoordinate P (P.parent q hq) hparentNonroot) ∈
      richRootTargets Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb P S A orient q := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  rw [nonrootCutParentTargets, dif_pos hq]
  apply Finset.mem_image.mpr
  refine ⟨literalBranchCoordinate P (P.parent q hq) hparentNonroot, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    partitionBranchEquivNonroots_literalBranchCoordinate P
      (P.parent q hq) hparentNonroot⟩

theorem otherSide_eq_of_ne (s t : Fin 2) (hst : s ≠ t) :
    otherSide s = t := by
  fin_cases s <;> fin_cases t <;> simp_all [otherSide]

/-- For a root-to-root cut edge, the parent's opposite distinguished target
is definitionally the child's raw root reservoir. -/
theorem richTargetRaw_opposite_eq_child
    (hT : T.IsTree) (j : Fin P.numParts) (hj : j.val ≠ 0)
    (hroot : P.parent j hj = P.roots (P.parentPart j hj)) :
    richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        (Sum.inl (otherSide
          (componentReservoirSide P (P.parentPart j hj)))) =
      rootRaw Pcluster Gdegree threshold quota R miss Q P j := by
  have hsides := componentReservoirSide_ne_of_cutRoot
    (P := P) hT j hj hroot
  rw [richTargetRaw, rootRaw]
  exact congrArg (rootRawSide Pcluster Gdegree threshold quota R miss Q)
    (otherSide_eq_of_ne _ _ hsides)

end Erdos547b.ZhaoClaim615RichDynamicRootTargets

#print axioms Erdos547b.ZhaoClaim615RichDynamicRootTargets.coordinateTarget_mem_of_nonrootCutParent
#print axioms Erdos547b.ZhaoClaim615RichDynamicRootTargets.richTargetRaw_opposite_eq_child
