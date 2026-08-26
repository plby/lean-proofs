/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichGlobalFixedHostFacts
import ErdosProblems.Erdos547b.Claim615RichPhysicalFiberPlan
import ErdosProblems.Erdos547b.Claim615RichPhysicalFiberScalarApplication
import ErdosProblems.Erdos547b.Claim616CoordinateCutAttachmentParity
import ErdosProblems.Erdos547b.Claim616HierarchyCoordinateSide

/-!
# Physical-fiber orientations in the synchronized Claim 6.15 backend

The physical plan chooses an orientation on each canonical matching fiber and
pastes those choices to the global branch family.  This file records that the
synchronized online backend restricts the pasted orientation back to the
literal local choice, including exact equality of the complete-fiber loads.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan

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
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads
open Erdos547b.ZhaoClaim615RichPhysicalFiberApplication
open Erdos547b.ZhaoClaim615RichGlobalFixedHostFacts
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichGlobalFixedPlan
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools
open Erdos547b.ZhaoClaim615RichPhysicalFiberPlan
open Erdos547b.ZhaoClaim615RichPhysicalFiberScalarApplication
open Erdos547b.ZhaoClaim615RichDynamicRootCleaning
open Erdos547b.ZhaoClaim616CoordinateSourceParity
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59FullOnline
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics

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

/-- Pulling the globally pasted physical orientation back to one matching
fiber recovers that fiber's literal local orientation. -/
theorem globalFixedFiberOrientation_physicalFiberOrient
    (localOrient : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
      Fin (matchingFiber
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e).card → Fin 2 ≃ Fin 2)
    (e : PhysicalIndex Q sourceDensity E0 Mb) :
    globalFixedFiberOrientation (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (physicalFiberOrient Q sourceDensity E0 Mb P S A localOrient) e =
      localOrient e := by
  simpa only [physicalFiberOrient] using
    globalFixedFiberOrientation_assembledOrient (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) localOrient e

/-- Thus the complete-fiber load used by the synchronized recursion is the
same load proved by the local physical-fiber certificate. -/
theorem sideLoad_globalFixed_physicalFiberOrient
    (localOrient : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
      Fin (matchingFiber
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e).card → Fin 2 ≃ Fin 2)
    (e : PhysicalIndex Q sourceDensity E0 Mb) (c : Fin 2) :
    sideLoad
        (onlineFiberForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e)
        (globalFixedFiberOrientation (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A))
          (physicalFiberOrient Q sourceDensity E0 Mb P S A localOrient) e) c =
      sideLoad
        (onlineFiberForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e)
        (localOrient e) c := by
  rw [globalFixedFiberOrientation_physicalFiberOrient Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb P S A localOrient e]

/-- The distinguished reduced vertex attached to a physical family is
literally the root cluster of every branch assigned to that family. -/
theorem physicalRootVertex_richAssign_eq_richRootCluster_owner
    (havailable : available ⊆ halfBranches P)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) :
    physicalRootVertex Q sourceDensity E0 Mb
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A) j) =
      richRootCluster Pcluster Gdegree threshold quota R miss Q P
        ((branchForest P).owner j) := by
  have hclass : j ∈ S.selected ∨ j ∈ majorResidualBranches P S ∨
      j ∈ minorBranches P := by
    by_cases hjHalf : j ∈ halfBranches P
    · by_cases hj : j ∈ S.selected
      · exact Or.inl hj
      · exact Or.inr (Or.inl
          ((mem_majorResidualBranches P S j).2 ⟨hjHalf, hj⟩))
    · right
      right
      have hj : j ∈ halfBranches P ∪ minorBranches P := by
        rw [halfBranches_union_minorBranches]
        exact Finset.mem_univ _
      exact (Finset.mem_union.mp hj).resolve_left hjHalf
  rcases hclass with hj | hj | hj
  · have he : richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j =
        exceptionalIndex Q sourceDensity E0 Mb (A.F0edge j) :=
      (assignedPhysicalIndex_eq_exceptional_iff
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j (A.F0edge j)).2 ⟨hj, rfl⟩
    rw [he, physicalRootVertex_exceptionalIndex, richRootCluster,
      componentReservoirSide_owner_eq_zero_of_mem_halfBranches P j
        (havailable (S.selected_available hj))]
    rfl
  · have he : richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j =
        remainingIndex Q sourceDensity E0 Mb (A.F1edge j) :=
      (assignedPhysicalIndex_eq_remaining_iff
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j (A.F1edge j)).2 ⟨hj, rfl⟩
    rw [he, physicalRootVertex_remainingIndex, richRootCluster,
      componentReservoirSide_owner_eq_zero_of_mem_halfBranches P j
        ((mem_majorResidualBranches P S j).mp hj).1]
    rfl
  · have he : richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) j =
        reservedIndex Q sourceDensity E0 Mb (A.Fbedge j) :=
      (assignedPhysicalIndex_eq_reserved_iff
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) havailable j (A.Fbedge j)).2 ⟨hj, rfl⟩
    rw [he, physicalRootVertex_reservedIndex, richRootCluster,
      componentReservoirSide_owner_eq_one_of_mem_minorBranches P j hj]
    rfl

/-- Consequently the root-side field of a physical plan supplies the exact
planned target adjacency for every branch root. -/
theorem physicalFiberPlan_fixed_branch_pair_adj
    (havailable : available ⊆ halfBranches P)
    (rootRho rootDensity removalBudget : ℝ)
    (plan : PhysicalFiberPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S cap0 cap1 capb A rootRho rootDensity
        removalBudget)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) (c : Fin 2)
    (hc : c ∈ (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A
        (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient)).branchRootSides j) :
    (padGraph R).Adj
      (richRootCluster Pcluster Gdegree threshold quota R miss Q P
        ((branchForest P).owner j))
      (richTargetCluster Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb
        (Sum.inr (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A) j, c))) := by
  have hc' : c =
      physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient j 0 := by
    simpa only [richFixedRootTargetPlan, globalFixedRootAllowed,
      globalFixedCoordinateSide, Finset.mem_singleton,
      coloringTwoOfVert_root] using hc
  subst c
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let i := assignmentIndex assign j
  have hroot := plan.root_adj (assign j) i
  have hsource := physicalRootVertex_richAssign_eq_richRootCluster_owner
    Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A
      havailable j
  rw [← hsource]
  simpa only [richTargetCluster, physicalFiberOrient_apply, assign, i] using
    hroot

/-- The reconnect rule puts a non-root cut parent on local side zero of its
canonical branch.  Hence the same physical-plan root fact also supplies the
child component's planned cut-parent target adjacency. -/
theorem physicalFiberPlan_fixed_cut_pair_adj
    (hT : T.IsTree) (havailable : available ⊆ halfBranches P)
    (rootRho rootDensity removalBudget : ℝ)
    (plan : PhysicalFiberPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S cap0 cap1 capb A rootRho rootDensity
        removalBudget)
    (q : Fin P.numParts) (hq : q.val ≠ 0)
    (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
      Fin ((branchForest P).branches.size j))
    (hz : (partitionBranchEquivNonroots P z).1 = P.parent q hq)
    (c : Fin 2)
    (hc : c ∈ globalFixedCoordinateAllowed (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient) z) :
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
  let orient := physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient
  have hclass : literalSourceClass P (P.parent q hq) = Sum.inr z.1 := by
    rw [← hz]
    exact literalSourceClass_partitionBranchEquivNonroots P z
  have hlocalCanonical :=
    cutParent_canonicalBranchSide_zero hT P q hq z.1 hclass
  have hlocal :
      ((branchForest P).branches.isTree z.1).coloringTwoOfVert
          ((branchForest P).branches.root z.1) z.2 = 0 := by
    rw [← canonicalBranchSide_partitionBranchCoordinate hT P z.1 z.2,
      hz]
    exact hlocalCanonical
  have hc' : c = orient z.1 0 := by
    simpa only [globalFixedCoordinateAllowed, Finset.mem_singleton,
      globalFixedCoordinateSide, hlocal] using hc
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
  have hroot := plan.root_adj (assign z.1) (assignmentIndex assign z.1)
  rw [← hsource, hc']
  simpa only [richTargetCluster, physicalFiberOrient_apply, assign, orient] using
    hroot

/-- Removing the two distinguished reserves leaves a regularity-large
physical endpoint whenever the standard whole-cluster reserve inequality
holds. -/
theorem richEndpoint_large_of_matching_reserve
    (rootRho : ℝ) (e : PhysicalIndex Q sourceDensity E0 Mb) (c : Fin 2)
    (hreserve : rootRho *
          #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c) + (2 * quota : ℕ) ≤
        #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c)) :
    rootRho * #(richWhole Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb e c) ≤
      #(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb e c) := by
  have hcard := slotWhole_card_le_slotRaw_card_add Pcluster Gdegree threshold
    quota R miss Q (indexedPhysicalEdge Q sourceDensity E0 Mb e) c
  have hcardR :
      (#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0
          Mb e c) : ℝ) ≤
        (#(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) : ℝ) + (2 * quota : ℕ) := by
    exact_mod_cast (show
      #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
          e c) ≤
        #(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) + 2 * quota by
      simpa only [richWhole, whole, richEndpoint, endpoint, slotWhole, slotRaw]
        using hcard)
  exact_mod_cast (by linarith : rootRho *
      (#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        e c) : ℝ) ≤
      (#(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb e c) : ℝ))

/-- A physical plan and the reconnect parity rule supply every planned
root-target adjacency, both at branch roots and at non-root cut parents.
Only scalar cleaning bounds remain. -/
theorem richPlannedRootCleaningFactsOfPhysicalFiberPlan
    (hT : T.IsTree) (havailable : available ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity removalBudget : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (plan : PhysicalFiberPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S cap0 cap1 capb A rootRho rootDensity
        removalBudget)
    (hrootLarge : ∀ side,
      rootRho *
          #(rootWholeSide Pcluster Gdegree threshold quota R miss Q side) ≤
        quota)
    (hendpointLarge : ∀ e c,
      rootRho * #(richWhole Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb e c) ≤
        #(richEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb e c))
    (hbudget : ∀ q,
      P.numParts + richPlannedRootLoss Pcluster Gdegree threshold quota R miss
        Q sourceDensity E0 Mb P S A rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A
              (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient))
          q ≤ quota)
    (hlink : ∀ j (hj : j.val ≠ 0)
      (_hroot : P.parent j hj = P.roots (P.parentPart j hj)),
      (P.numParts : ℝ) +
          richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A rootRho
              (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb P S A
                  (physicalFiberOrient Q sourceDensity E0 Mb P S A
                    plan.orient)) j ≤
        (rootDensity - rootRho) * quota) :
    RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A
            (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient)) := by
  apply RichPlannedRootCleaningFacts.of_source Pcluster Gdegree threshold quota
    R miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
      (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A
          (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient))
  · intro j c hc
    exact physicalFiberPlan_fixed_branch_pair_adj Pcluster Gdegree threshold
      quota R miss Q sourceDensity E0 Mb P S A havailable rootRho rootDensity
      removalBudget plan j c hc
  · intro q hq z hz c hc
    exact physicalFiberPlan_fixed_cut_pair_adj Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb P S A hT havailable rootRho rootDensity
        removalBudget plan q hq z hz c hc
  · exact hrootLarge
  · exact hendpointLarge
  · exact hbudget
  · exact hlink

/-- The common scalar facts already used by the coordinate physical-fiber
application discharge both kinds of regularity-largeness in the planned
cleaning certificate. -/
theorem richPlannedRootCleaningFactsOfPhysicalFiberGlobalFacts
    (hT : T.IsTree) (havailable : available ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity removalBudget : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (plan : PhysicalFiberPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S cap0 cap1 capb A rootRho rootDensity
        removalBudget)
    (m : ℕ)
    (D : PhysicalFiberGlobalFacts Pcluster Gdegree threshold quota R miss Q P
      hT rootRho rootDensity removalBudget m)
    (hbudget : ∀ q,
      P.numParts + richPlannedRootLoss Pcluster Gdegree threshold quota R miss
        Q sourceDensity E0 Mb P S A rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A
              (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient))
          q ≤ quota)
    (hlink : ∀ j (hj : j.val ≠ 0)
      (_hroot : P.parent j hj = P.roots (P.parentPart j hj)),
      (P.numParts : ℝ) +
          richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A rootRho
              (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb P S A
                  (physicalFiberOrient Q sourceDensity E0 Mb P S A
                    plan.orient)) j ≤
        (rootDensity - rootRho) * quota) :
    RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A
            (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient)) := by
  apply richPlannedRootCleaningFactsOfPhysicalFiberPlan Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S A hT havailable G rootRho
      rootDensity removalBudget H plan
  · intro side
    fin_cases side
    · change rootRho * #(clusterVertices Pcluster Q.A) ≤ quota
      exact D.A_reserve
    · change rootRho * #(clusterVertices Pcluster Q.B) ≤ quota
      exact D.B_reserve
  · intro e c
    apply richEndpoint_large_of_matching_reserve Pcluster Gdegree threshold
      quota R miss Q sourceDensity E0 Mb rootRho e c
    simpa only [richWhole, whole, slotWhole] using
      D.matching_reserve (indexedPhysicalEdge Q sourceDensity E0 Mb e) c
  · exact hbudget
  · exact hlink

/-- The checked local physical-fiber margin is exactly the eligibility
margin needed by the synchronized recursion once its permanent-cleaning
overhead fits inside the plan's common removal allowance.  The other fields
are the genuinely additional global-root and residual-capacity inequalities;
no embedding or online-state premise is exposed. -/
noncomputable def richFixedFullFiberEdgeFactsOfPhysicalPlan
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity removalBudget : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (plan : PhysicalFiberPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S cap0 cap1 capb A rootRho rootDensity
        removalBudget)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A
            (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient)))
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (hfactor : 0 ≤ rootDensity - rootRho)
    (hrootBudget : ∀ q,
      thresholdReserve rootRho
          #(rootWhole Pcluster Gdegree threshold quota R miss Q P q) +
        richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A rootRho
            (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb P S A
                (physicalFiberOrient Q sourceDensity E0 Mb P S A
                  plan.orient)) q ≤ quota)
    (hparentThreshold : ∀ c q (hq : q.val ≠ 0)
      (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq)),
      let coord := cutParentBranchCoordinate P q hq hnotroot
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) coord.1 = e →
      c ∈ globalFixedCoordinateAllowed (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient) coord →
        (P.numParts : ℝ) ≤ (rootDensity - rootRho) *
          #(richFixedCandidate Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A G rootRho
              (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient) q))
    (htotal : ∀ c,
      (2 * quota + P.numParts *
          thresholdReserve rootRho
            #(richWhole Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb e c)) +
          sideLoad (onlineFiberForest (branchForest P)
            (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R) (miss := miss)
              (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
              (P := P) (S := S) (A := A)) e)
            (globalFixedFiberOrientation (branchForest P)
              (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
                (threshold := threshold) (quota := quota) (R := R)
                (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
                (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A))
              (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient) e)
            c +
          thresholdReserve rootRho
            #(richWhole Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb e c) ≤
        #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0
          Mb e c))
    (hplanOverhead : ∀ c,
      (((2 * quota + P.numParts *
            thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb e c)) +
          (1 + thresholdReserve rootRho
            #(richWhole Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb e c)) : ℕ) : ℝ) ≤
        (small : ℝ) + 1 + removalBudget + 1)
    (hcomponent : ∀ c,
      let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
      (small : ℝ) + rootRho *
          (#(richWhole Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb e c) : ℝ) + 1 ≤
        (rootDensity - rootRho) *
          ((#(richWhole Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb e c) : ℝ) -
            (2 * quota + P.numParts *
              thresholdReserve rootRho
                #(richWhole Pcluster Gdegree threshold quota R miss Q
                  sourceDensity E0 Mb e c) : ℕ) -
            sideLoad (onlineFiberForest (branchForest P) assign e)
              (globalFixedFiberOrientation (branchForest P) assign
                (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient)
                e) c)) :
    RichFixedFullFiberEdgeFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
        (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient) F e := by
  refine {
    factor_nonneg := hfactor
    root_candidate_budget := hrootBudget
    parent_threshold := hparentThreshold
    total := htotal
    eligible_margin := ?_
    component_margin := hcomponent
  }
  intro c
  dsimp only
  have hcapacity := plan.capacity e c
  have hload := sideLoad_globalFixed_physicalFiberOrient Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S A plan.orient e c
  rw [hload]
  have hover := hplanOverhead c
  calc
    (((2 * quota + P.numParts *
          thresholdReserve rootRho
            #(richWhole Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb e c)) +
        sideLoad (onlineFiberForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e)
          (plan.orient e) c +
        (1 + thresholdReserve rootRho
          #(richWhole Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb e c)) : ℕ) : ℝ) =
        (sideLoad (onlineFiberForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e) (plan.orient e) c : ℝ) +
          (((2 * quota + P.numParts *
              thresholdReserve rootRho
                #(richWhole Pcluster Gdegree threshold quota R miss Q
                  sourceDensity E0 Mb e c)) +
            (1 + thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb e c)) : ℕ) : ℝ) := by
          norm_num only [Nat.cast_add]
          ring
    _ ≤ (sideLoad (onlineFiberForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e) (plan.orient e) c : ℝ) +
          ((small : ℝ) + 1 + removalBudget + 1) := by
      linarith
    _ ≤ (rootDensity - rootRho) *
        #(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) := by
      simpa only [onlineFiberForest, physicalFiberForest, physicalFiberRhs,
        richAssign, richEndpoint, endpoint, whole, slotRaw, selectedForest,
        Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict,
        add_assoc] using hcapacity

end Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan

#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan.globalFixedFiberOrientation_physicalFiberOrient
#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan.sideLoad_globalFixed_physicalFiberOrient
#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan.physicalRootVertex_richAssign_eq_richRootCluster_owner
#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan.physicalFiberPlan_fixed_branch_pair_adj
#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan.physicalFiberPlan_fixed_cut_pair_adj
#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan.richEndpoint_large_of_matching_reserve
#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan.richPlannedRootCleaningFactsOfPhysicalFiberPlan
#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan.richPlannedRootCleaningFactsOfPhysicalFiberGlobalFacts
#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan.richFixedFullFiberEdgeFactsOfPhysicalPlan
