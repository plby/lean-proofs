/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichGlobalFixedPhysicalPlan
import ErdosProblems.Erdos547b.Claim615RichPhysicalRootOrientation

/-!
# Planned root cleaning from root-only physical orientations

The proofs in this file use only the root-adjacency part of the physical
orientation.  In particular they do not mention the obsolete static fiber
capacity field.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichGlobalRootOrientationPlan

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
open Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan
open Erdos547b.ZhaoClaim615RichPhysicalRootOrientation
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichDynamicRootCleaning
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichGlobalFixedPlan
open Erdos547b.ZhaoClaim616CoordinateSourceParity
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59FullOnline

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

/-- The singleton side plan induced by a root-only physical orientation. -/
def richRootOrientationTargetPlan
    (D : PhysicalRootOrientationPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A) : RootTargetPlan P :=
  richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A
      (physicalFiberOrient Q sourceDensity E0 Mb P S A D.orient)

/-- Root-only orientation data supplies the planned branch-root adjacency. -/
theorem physicalRootOrientation_branch_pair_adj
    (havailable : available ⊆ halfBranches P)
    (D : PhysicalRootOrientationPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) (c : Fin 2)
    (hc : c ∈ (richRootOrientationTargetPlan Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A D).branchRootSides j) :
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
      physicalFiberOrient Q sourceDensity E0 Mb P S A D.orient j 0 := by
    simpa only [richRootOrientationTargetPlan, richFixedRootTargetPlan,
      globalFixedRootAllowed, globalFixedCoordinateSide, Finset.mem_singleton,
      coloringTwoOfVert_root] using hc
  subst c
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let i := assignmentIndex assign j
  have hroot := D.root_adj (assign j) i
  have hsource := physicalRootVertex_richAssign_eq_richRootCluster_owner
    Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A
      havailable j
  rw [← hsource]
  simpa only [richTargetCluster, physicalFiberOrient_apply, assign, i] using
    hroot

/-- The reconnect parity rule supplies the corresponding non-root cut-parent
adjacency from the same root-only orientation. -/
theorem physicalRootOrientation_cut_pair_adj
    (hT : T.IsTree) (havailable : available ⊆ halfBranches P)
    (D : PhysicalRootOrientationPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A)
    (q : Fin P.numParts) (hq : q.val ≠ 0)
    (z : Σ j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P,
      Fin ((branchForest P).branches.size j))
    (hz : (partitionBranchEquivNonroots P z).1 = P.parent q hq)
    (c : Fin 2)
    (hc : c ∈ (richRootOrientationTargetPlan Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A D).coordinateSides z) :
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
  let orient := physicalFiberOrient Q sourceDensity E0 Mb P S A D.orient
  have hclass : literalSourceClass P (P.parent q hq) = Sum.inr z.1 := by
    rw [← hz]
    exact literalSourceClass_partitionBranchEquivNonroots P z
  have hlocalCanonical :=
    cutParent_canonicalBranchSide_zero hT P q hq z.1 hclass
  have hlocal :
      ((branchForest P).branches.isTree z.1).coloringTwoOfVert
          ((branchForest P).branches.root z.1) z.2 = 0 := by
    rw [← canonicalBranchSide_partitionBranchCoordinate hT P z.1 z.2, hz]
    exact hlocalCanonical
  have hc' : c = orient z.1 0 := by
    simpa only [richRootOrientationTargetPlan, richFixedRootTargetPlan,
      globalFixedCoordinateAllowed, Finset.mem_singleton,
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
  have hroot := D.root_adj (assign z.1) (assignmentIndex assign z.1)
  rw [← hsource, hc']
  simpa only [richTargetCluster, physicalFiberOrient_apply, assign, orient] using
    hroot

/-- Construct the complete planned root-cleaning certificate from a
root-only physical orientation and scalar largeness bounds. -/
theorem richPlannedRootCleaningFactsOfRootOrientation
    (hT : T.IsTree) (havailable : available ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalRootOrientationPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A)
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
          (richRootOrientationTargetPlan Pcluster Gdegree threshold quota R
            miss Q sourceDensity E0 Mb P S A D) q ≤ quota)
    (hlink : ∀ j (hj : j.val ≠ 0)
      (_hroot : P.parent j hj = P.roots (P.parentPart j hj)),
      (P.numParts : ℝ) +
          richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A rootRho
              (richRootOrientationTargetPlan Pcluster Gdegree threshold quota R
                miss Q sourceDensity E0 Mb P S A D) j ≤
        (rootDensity - rootRho) * quota) :
    RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richRootOrientationTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A D) := by
  apply RichPlannedRootCleaningFacts.of_source Pcluster Gdegree threshold quota
    R miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
      (richRootOrientationTargetPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A D)
  · exact physicalRootOrientation_branch_pair_adj Pcluster Gdegree threshold
      quota R miss Q sourceDensity E0 Mb P S A havailable D
  · exact physicalRootOrientation_cut_pair_adj Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb P S A hT havailable D
  · exact hrootLarge
  · exact hendpointLarge
  · exact hbudget
  · exact hlink

end Erdos547b.ZhaoClaim615RichGlobalRootOrientationPlan

#print axioms Erdos547b.ZhaoClaim615RichGlobalRootOrientationPlan.physicalRootOrientation_branch_pair_adj
#print axioms Erdos547b.ZhaoClaim615RichGlobalRootOrientationPlan.physicalRootOrientation_cut_pair_adj
#print axioms Erdos547b.ZhaoClaim615RichGlobalRootOrientationPlan.richPlannedRootCleaningFactsOfRootOrientation
