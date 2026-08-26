/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichGlobalRootOrientationPlan
import ErdosProblems.Erdos547b.Lemma58PlannedThresholdRootGood

/-!
# Planned root cleaning from physical side sets

Threshold fibers need only the endpoint sides which can actually be selected
by their canonical cutoff orientation.  Appendix fibers, on the other hand,
must retain both sides because their orientation is chosen from the current
residual capacities.  This file records that distinction without choosing an
embedding or a continuation.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichGlobalRootSidePlan

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616CoordinateCutAttachmentParity
open Erdos547b.ZhaoClaim616HierarchyCoordinateSide
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichPhysicalFiberPlan
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads
open Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan
open Erdos547b.ZhaoClaim615RichPhysicalRootOrientation
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichDynamicRootTargets
open Erdos547b.ZhaoClaim615RichDynamicRootCleaning
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim616CoordinateSourceParity
open Erdos547b.ZhaoLemma59FullOnline
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58CanonicalThresholdStep
open Erdos547b.ZhaoLemma58PlannedOwnerLocalStep
open Erdos547b.ZhaoLemma58PlannedThresholdRootGood
open Erdos547b.ZhaoLemma58RootCandidateCleaning

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

/-- A finite set of root-admissible sides on every physical matching edge.
The certificate is purely a reduced-graph statement. -/
structure PhysicalRootSidePlan : Type (max u v w) where
  sides : PhysicalIndex Q sourceDensity E0 Mb → Finset (Fin 2)
  root_good : ∀ e c, c ∈ sides e →
    physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e c

/-- The maximal admissible-side plan: retain exactly the sides adjacent to
the physical source row. -/
noncomputable def physicalRootGoodSidePlan :
    PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb := by
  classical
  exact {
    sides := fun e ↦ (Finset.univ : Finset (Fin 2)).filter
      (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e)
    root_good := by
      intro e c hc
      exact (Finset.mem_filter.mp hc).2 }

@[simp] theorem mem_physicalRootGoodSidePlan
    (e : PhysicalIndex Q sourceDensity E0 Mb) (c : Fin 2) :
    c ∈ (physicalRootGoodSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb).sides e ↔
      physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e c := by
  classical
  simp only [physicalRootGoodSidePlan, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- Pull a physical admissible-side family back to literal branches and
literal coordinates. -/
def isCutParentCoordinate
    (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
      Fin ((branchForest P).branches.size j)) : Prop :=
  ∃ q : Fin P.numParts, ∃ hq : q.val ≠ 0,
    (partitionBranchEquivNonroots P z).1 = P.parent q hq

noncomputable def richRootSideTargetPlan
    (D : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb) : RootTargetPlan P := by
  classical
  exact {
    branchRootSides := fun j ↦ D.sides
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j)
    coordinateSides := fun z ↦
      if isCutParentCoordinate P z then
        D.sides
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A) z.1)
      else Finset.univ }

/-- Every permitted branch-root side gives the required reduced pair. -/
theorem physicalRootSidePlan_branch_pair_adj
    (havailable : available ⊆ halfBranches P)
    (D : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) (c : Fin 2)
    (hc : c ∈ (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A D).branchRootSides j) :
    (padGraph R).Adj
      (richRootCluster Pcluster Gdegree threshold quota R miss Q P
        ((branchForest P).owner j))
      (richTargetCluster Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb
        (Sum.inr (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A) j, c))) := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  have hgood := D.root_good (assign j) c (by
    simpa only [richRootSideTargetPlan] using hc)
  have hsource := physicalRootVertex_richAssign_eq_richRootCluster_owner
    Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A
      havailable j
  rw [← hsource]
  simpa only [richTargetCluster, physicalRootGood, assign] using hgood

/-- The reconnect parity rule identifies the same physical source row for a
literal non-root cut parent. -/
theorem physicalRootSidePlan_cut_pair_adj
    (hT : T.IsTree) (havailable : available ⊆ halfBranches P)
    (D : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (q : Fin P.numParts) (hq : q.val ≠ 0)
    (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
      Fin ((branchForest P).branches.size j))
    (hz : (partitionBranchEquivNonroots P z).1 = P.parent q hq)
    (c : Fin 2)
    (hc : c ∈ (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A D).coordinateSides z) :
    (padGraph R).Adj
      (richRootCluster Pcluster Gdegree threshold quota R miss Q P q)
      (richTargetCluster Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb
        (Sum.inr (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A) z.1, c))) := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  have hnonroot : P.parent q hq ∉ partitionRoots P := by
    rw [← hz]
    exact (Finset.mem_sdiff.mp (partitionBranchEquivNonroots P z).2).2
  have hpart : P.parentPart q hq = (branchForest P).owner z.1 := by
    have hp := partitionBranchEquivNonroots_component P z
    rw [hz, componentIndex_parent P q hq] at hp
    exact hp
  have hreservoir : componentReservoirSide P q =
      componentReservoirSide P ((branchForest P).owner z.1) := by
    rcases P.reconnect_rule q hq with hroot | hparity
    · exfalso
      apply hnonroot
      rw [hroot]
      exact Finset.mem_image.mpr
        ⟨P.parentPart q hq, Finset.mem_univ _, rfl⟩
    · rw [hpart] at hparity
      unfold componentReservoirSide
      rw [hparity]
  have hsource : physicalRootVertex Q sourceDensity E0 Mb (assign z.1) =
      richRootCluster Pcluster Gdegree threshold quota R miss Q P q := by
    calc
      _ = richRootCluster Pcluster Gdegree threshold quota R miss Q P
          ((branchForest P).owner z.1) :=
        physicalRootVertex_richAssign_eq_richRootCluster_owner Pcluster
          Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A
            havailable z.1
      _ = _ := by
        unfold richRootCluster
        rw [hreservoir]
  have hcut : isCutParentCoordinate P z := ⟨q, hq, hz⟩
  have hgood := D.root_good (assign z.1) c (by
    simpa only [richRootSideTargetPlan, if_pos hcut] using hc)
  rw [← hsource]
  simpa only [richTargetCluster, physicalRootGood, assign] using hgood

/-- Any orientation whose branch-root sides are admissible automatically
respects the coordinate plan.  Only literal cut-parent coordinates are
restricted, and their canonical local colour is zero. -/
theorem orientation_coordinate_mem_rootSidePlan
    (hT : T.IsTree)
    (D : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (hroot : ∀ j, orient j 0 ∈ D.sides
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j))
    (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
      Fin ((branchForest P).branches.size j)) :
    orient z.1
        ((branchForest P).branches.isTree z.1 |>.coloringTwoOfVert
          ((branchForest P).branches.root z.1) z.2) ∈
      (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A D).coordinateSides z := by
  classical
  by_cases hcut : isCutParentCoordinate P z
  · have hcut' := hcut
    obtain ⟨q, hq, hz⟩ := hcut
    have hclass : literalSourceClass P (P.parent q hq) = Sum.inr z.1 := by
      rw [← hz]
      exact literalSourceClass_partitionBranchEquivNonroots P z
    have hzero := cutParent_canonicalBranchSide_zero hT P q hq z.1 hclass
    have hlocal :
        ((branchForest P).branches.isTree z.1).coloringTwoOfVert
            ((branchForest P).branches.root z.1) z.2 = 0 := by
      rw [← canonicalBranchSide_partitionBranchCoordinate hT P z.1 z.2,
        hz]
      exact hzero
    simpa only [richRootSideTargetPlan, if_pos hcut', hlocal] using hroot z.1
  · simp only [richRootSideTargetPlan, if_neg hcut, Finset.mem_univ]

/-- Pull an admissible owner-batch root orientation back to the literal rich
branch-root plan. -/
theorem onlineOwnerBatch_root_mem_rootSidePlan
    (D : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (n : ℕ) (hn : n < P.numParts)
    (orient : Fin (onlineOwnerBatch (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e n hn).card → Fin 2 ≃ Fin 2)
    (hroot : ∀ i, orient i 0 ∈ D.sides e)
    (i : Fin (onlineOwnerBatch (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e n hn).card) :
    branchRootSide (onlineOwnerBatchForest (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn) orient i ∈
      onlineOwnerBatchRootAllowed (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A D).branchRootSides i := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  have he := onlineOwnerBatchBranch_assign (branchForest P) assign e n hn i
  simpa only [branchRootSide,
    onlineOwnerBatchRootAllowed, richRootSideTargetPlan, he, assign] using
      hroot i

/-- The same owner-batch orientation respects the coordinate plan.  An
unrestricted coordinate is immediate; a cut-parent coordinate has canonical
local colour zero and hence uses the branch-root side. -/
theorem onlineOwnerBatch_coordinate_mem_rootSidePlan
    (hT : T.IsTree)
    (D : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (n : ℕ) (hn : n < P.numParts)
    (orient : Fin (onlineOwnerBatch (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e n hn).card → Fin 2 ≃ Fin 2)
    (hroot : ∀ i, orient i 0 ∈ D.sides e)
    (i : Fin (onlineOwnerBatch (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e n hn).card)
    (a : Fin ((onlineOwnerBatchForest (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e n hn).size i)) :
    orient i
        ((onlineOwnerBatchForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e n hn).isTree i
          |>.coloringTwoOfVert
            ((onlineOwnerBatchForest (branchForest P)
              (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
                (threshold := threshold) (quota := quota) (R := R)
                (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
                (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) e n hn).root i) a) ∈
      onlineOwnerBatchCoordinateAllowed (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A D).coordinateSides ⟨i, a⟩ := by
  classical
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let z : Σ j, Fin ((branchForest P).branches.size j) :=
    ⟨onlineOwnerBatchBranch (branchForest P) assign e n hn i,
      onlineOwnerBatchVertex (branchForest P) assign e n hn i a⟩
  change orient i _ ∈
    (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A D).coordinateSides z
  by_cases hcut : isCutParentCoordinate P z
  · have hcut' := hcut
    obtain ⟨q, hq, hz⟩ := hcut
    have hclass : literalSourceClass P (P.parent q hq) = Sum.inr z.1 := by
      rw [← hz]
      exact literalSourceClass_partitionBranchEquivNonroots P z
    have hzero := cutParent_canonicalBranchSide_zero hT P q hq z.1 hclass
    have hglobalColor :
        ((branchForest P).branches.isTree z.1).coloringTwoOfVert
            ((branchForest P).branches.root z.1) z.2 = 0 := by
      rw [← canonicalBranchSide_partitionBranchCoordinate hT P z.1 z.2,
        hz]
      exact hzero
    have hlocalColor :
        ((onlineOwnerBatchForest (branchForest P) assign e n hn).isTree i
          |>.coloringTwoOfVert
            ((onlineOwnerBatchForest (branchForest P) assign e n hn).root i)
            a) = 0 := by
      change ((branchForest P).branches.isTree z.1).coloringTwoOfVert
        ((branchForest P).branches.root z.1) z.2 = 0
      exact hglobalColor
    have he := onlineOwnerBatchBranch_assign (branchForest P) assign e n hn i
    have hez : assign z.1 = e := by
      change assign (onlineOwnerBatchBranch (branchForest P) assign e n hn i) = e
      exact he
    change orient i _ ∈ if isCutParentCoordinate P z then
      D.sides (assign z.1) else Finset.univ
    rw [if_pos hcut', hlocalColor, hez]
    exact hroot i
  · simp only [richRootSideTargetPlan, if_neg hcut, Finset.mem_univ]

/-- Attach the pulled-back rich side plan to a canonical threshold step on
one literal online owner batch.  The only extra datum is root-side
admissibility on the physical edge; coordinate admissibility then follows
from the cut-parent parity theorem. -/
def plannedThresholdOwnerLocalStepData_of_rootSidePlan
    (hT : T.IsTree)
    (Dside : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (n : ℕ) (hn : n < P.numParts)
    (externalParent : Fin (onlineOwnerBatch (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e n hn).card → Bv)
    (whole live : Fin 2 → Finset Bv) (rho density : ℝ)
    (D : ActualThresholdStepData
      (onlineOwnerBatchForest (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn)
      G externalParent whole live rho density)
    (hroot : ∀ i,
      canonicalStepOrientation
        (onlineOwnerBatchForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e n hn)
        G externalParent whole live rho density D i 0 ∈ Dside.sides e) :
    PlannedOwnerLocalStepData
      (onlineOwnerBatchForest (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn)
      G externalParent whole live rho density
      (onlineOwnerBatchRootAllowed (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A Dside).branchRootSides)
      (onlineOwnerBatchCoordinateAllowed (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A Dside).coordinateSides) :=
  .threshold D
    (onlineOwnerBatch_root_mem_rootSidePlan Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A Dside e n hn _ hroot)
    (onlineOwnerBatch_coordinate_mem_rootSidePlan Pcluster Gdegree threshold
      quota R miss Q sourceDensity E0 Mb P S A hT Dside e n hn _ hroot)

/-- Attach the pulled-back rich side plan to an Appendix step when both
physical sides remain admissible. -/
def plannedAppendixOwnerLocalStepData_of_rootSidePlan
    (hT : T.IsTree)
    (Dside : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (n : ℕ) (hn : n < P.numParts)
    (externalParent : Fin (onlineOwnerBatch (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e n hn).card → Bv)
    (whole live : Fin 2 → Finset Bv) (rho density : ℝ)
    (D : AppendixStepData
      (onlineOwnerBatchForest (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn)
      G externalParent whole live rho density)
    (hall : ∀ c, c ∈ Dside.sides e) :
    PlannedOwnerLocalStepData
      (onlineOwnerBatchForest (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn)
      G externalParent whole live rho density
      (onlineOwnerBatchRootAllowed (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A Dside).branchRootSides)
      (onlineOwnerBatchCoordinateAllowed (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A Dside).coordinateSides) :=
  .appendix D
    (fun i c ↦ by
      let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
      have he := onlineOwnerBatchBranch_assign (branchForest P) assign e n hn i
      change c ∈ Dside.sides
        (assign (onlineOwnerBatchBranch (branchForest P) assign e n hn i))
      rw [he]
      exact hall c)
    (fun i a c ↦ by
      classical
      let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
      let z : Σ j, Fin ((branchForest P).branches.size j) :=
        ⟨onlineOwnerBatchBranch (branchForest P) assign e n hn i,
          onlineOwnerBatchVertex (branchForest P) assign e n hn i a⟩
      change c ∈ (richRootSideTargetPlan Pcluster Gdegree threshold quota R
        miss Q sourceDensity E0 Mb P S A Dside).coordinateSides z
      by_cases hcut : isCutParentCoordinate P z
      · have he := onlineOwnerBatchBranch_assign (branchForest P) assign e n hn i
        have hez : assign z.1 = e := by
          change assign (onlineOwnerBatchBranch (branchForest P) assign e n hn i) = e
          exact he
        change c ∈ if isCutParentCoordinate P z then Dside.sides (assign z.1)
          else Finset.univ
        rw [if_pos hcut, hez]
        exact hall c
      · simp only [richRootSideTargetPlan, if_neg hcut, Finset.mem_univ])

/-- Reindexed Appendix variant of
`plannedAppendixOwnerLocalStepData_of_rootSidePlan`. -/
def plannedReindexedAppendixOwnerLocalStepData_of_rootSidePlan
    (hT : T.IsTree)
    (Dside : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (n : ℕ) (hn : n < P.numParts)
    (externalParent : Fin (onlineOwnerBatch (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e n hn).card → Bv)
    (whole live : Fin 2 → Finset Bv) (rho density : ℝ)
    (D : ReindexedAppendixStepData
      (onlineOwnerBatchForest (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn)
      G externalParent whole live rho density)
    (hall : ∀ c, c ∈ Dside.sides e) :
    PlannedOwnerLocalStepData
      (onlineOwnerBatchForest (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn)
      G externalParent whole live rho density
      (onlineOwnerBatchRootAllowed (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A Dside).branchRootSides)
      (onlineOwnerBatchCoordinateAllowed (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A Dside).coordinateSides) :=
  .reindexedAppendix D
    (fun i c ↦ by
      let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
      have he := onlineOwnerBatchBranch_assign (branchForest P) assign e n hn i
      change c ∈ Dside.sides
        (assign (onlineOwnerBatchBranch (branchForest P) assign e n hn i))
      rw [he]
      exact hall c)
    (fun i a c ↦ by
      classical
      let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
      let z : Σ j, Fin ((branchForest P).branches.size j) :=
        ⟨onlineOwnerBatchBranch (branchForest P) assign e n hn i,
          onlineOwnerBatchVertex (branchForest P) assign e n hn i a⟩
      change c ∈ (richRootSideTargetPlan Pcluster Gdegree threshold quota R
        miss Q sourceDensity E0 Mb P S A Dside).coordinateSides z
      by_cases hcut : isCutParentCoordinate P z
      · have he := onlineOwnerBatchBranch_assign (branchForest P) assign e n hn i
        have hez : assign z.1 = e := by
          change assign
            (onlineOwnerBatchBranch (branchForest P) assign e n hn i) = e
          exact he
        change c ∈ if isCutParentCoordinate P z then Dside.sides (assign z.1)
          else Finset.univ
        rw [if_pos hcut, hez]
        exact hall c
      · simp only [richRootSideTargetPlan, if_neg hcut, Finset.mem_univ])

/-- One branch in an owner batch makes every side admitted by its abstract
root-target plan a literal target of the current owner's cleaned candidate. -/
theorem plannedRootCandidate_onlineOwnerBatch_branch_degree
    (plan : RootTargetPlan P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H plan)
    (n : ℕ) (hn : n < P.numParts) (z : Bv)
    (hz : z ∈ rootCandidate G rootRho
      (rootWhole Pcluster Gdegree threshold quota R miss Q P)
      (rootRaw Pcluster Gdegree threshold quota R miss Q P)
      (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A plan)
      (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb)
      (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity E0
        Mb) ⟨n, hn⟩)
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (i : Fin #(onlineOwnerBatch (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e n hn))
    (c : Fin 2)
    (hc : c ∈ plan.branchRootSides
      (onlineOwnerBatchBranch (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn i)) :
    (rootDensity - rootRho) *
        #(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) ≤
      #((richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb e c).filter (G.Adj z)) := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let j := onlineOwnerBatchBranch (branchForest P) assign e n hn i
  have hjOwner : (branchForest P).owner j = ⟨n, hn⟩ :=
    onlineOwnerBatchBranch_owner (branchForest P) assign e n hn i
  have hjAssign : assign j = e :=
    onlineOwnerBatchBranch_assign (branchForest P) assign e n hn i
  have ht := plannedBranchRootTarget_mem Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P S A plan j c (by simpa only [assign, j] using hc)
  have hd := F.target_degree Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A G rootRho rootDensity H plan
      ((branchForest P).owner j) z (by simpa only [hjOwner] using hz)
      (Sum.inr (e, c)) (by simpa only [assign, j, hjAssign] using ht)
  simpa only [richTargetRaw] using hd

/-- A nonempty owner batch makes each admissible physical root side an
explicit target of that owner's cleaned root candidate.  Consequently every
chosen owner root has the regularity lower-degree bound into the literal rich
endpoint on that side. -/
theorem plannedRootCandidate_onlineOwnerBatch_degree
    (Dside : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A Dside))
    (n : ℕ) (hn : n < P.numParts) (z : Bv)
    (hz : z ∈ rootCandidate G rootRho
      (rootWhole Pcluster Gdegree threshold quota R miss Q P)
      (rootRaw Pcluster Gdegree threshold quota R miss Q P)
      (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A
          (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A Dside))
      (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb)
      (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity E0
        Mb) ⟨n, hn⟩)
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (hbatch : 0 < #(onlineOwnerBatch (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e n hn))
    (c : Fin 2) (hc : c ∈ Dside.sides e) :
    (rootDensity - rootRho) *
        #(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) ≤
      #((richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb e c).filter (G.Adj z)) := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let i : Fin #(onlineOwnerBatch (branchForest P) assign e n hn) := ⟨0, hbatch⟩
  let j := onlineOwnerBatchBranch (branchForest P) assign e n hn i
  have hjOwner : (branchForest P).owner j = ⟨n, hn⟩ :=
    onlineOwnerBatchBranch_owner (branchForest P) assign e n hn i
  have hjAssign : assign j = e :=
    onlineOwnerBatchBranch_assign (branchForest P) assign e n hn i
  have hcPlan : c ∈
      (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A Dside).branchRootSides j := by
    change c ∈ Dside.sides (assign j)
    rw [hjAssign]
    exact hc
  exact plannedRootCandidate_onlineOwnerBatch_branch_degree Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S A
      (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A Dside) G rootRho rootDensity H F n hn z hz e
      i c (by simpa only [assign, j] using hcPlan)

/-- Construct planned root cleaning from a physical admissible-side family
and the remaining scalar cleaning inequalities. -/
theorem richPlannedRootCleaningFactsOfRootSidePlan
    (hT : T.IsTree) (havailable : available ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (hrootLarge : ∀ side,
      rootRho * #(rootWholeSide Pcluster Gdegree threshold quota R miss Q side) ≤
        quota)
    (hendpointLarge : ∀ e c,
      rootRho * #(richWhole Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb e c) ≤
        #(richEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb e c))
    (hbudget : ∀ q,
      P.numParts + richPlannedRootLoss Pcluster Gdegree threshold quota R miss
        Q sourceDensity E0 Mb P S A rootRho
          (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A D) q ≤ quota)
    (hlink : ∀ j (hj : j.val ≠ 0)
      (_hroot : P.parent j hj = P.roots (P.parentPart j hj)),
      (P.numParts : ℝ) +
          richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A rootRho
              (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb P S A D) j ≤
        (rootDensity - rootRho) * quota) :
    RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A D) := by
  apply RichPlannedRootCleaningFacts.of_source Pcluster Gdegree threshold quota
    R miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
      (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A D)
  · exact physicalRootSidePlan_branch_pair_adj Pcluster Gdegree threshold
      quota R miss Q sourceDensity E0 Mb P S A havailable D
  · exact physicalRootSidePlan_cut_pair_adj Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb P S A hT havailable D
  · exact hrootLarge
  · exact hendpointLarge
  · exact hbudget
  · exact hlink

end Erdos547b.ZhaoClaim615RichGlobalRootSidePlan

#print axioms Erdos547b.ZhaoClaim615RichGlobalRootSidePlan.physicalRootSidePlan_branch_pair_adj
#print axioms Erdos547b.ZhaoClaim615RichGlobalRootSidePlan.physicalRootSidePlan_cut_pair_adj
#print axioms Erdos547b.ZhaoClaim615RichGlobalRootSidePlan.richPlannedRootCleaningFactsOfRootSidePlan
#print axioms Erdos547b.ZhaoClaim615RichGlobalRootSidePlan.plannedReindexedAppendixOwnerLocalStepData_of_rootSidePlan
#print axioms Erdos547b.ZhaoClaim615RichGlobalRootSidePlan.plannedRootCandidate_onlineOwnerBatch_degree
#print axioms Erdos547b.ZhaoClaim615RichGlobalRootSidePlan.plannedRootCandidate_onlineOwnerBatch_branch_degree
