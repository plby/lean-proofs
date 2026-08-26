/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicPlannedRootCleaning
import ErdosProblems.Erdos547b.Claim615RichGlobalOnlineCleaning

/-!
# Planned root cleaning for the synchronized rich online backend

This wrapper discharges the initial-root cardinality, root/root cut-link, and
root-versus-matching-endpoint obligations of the synchronized online backend
from the existing planned target-cleaning certificate.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichGlobalOnlinePlannedApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichDynamicRootTargets
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichGlobalOnlineApplication
open Erdos547b.ZhaoClaim615RichGlobalOnlineCleaning
open Erdos547b.ZhaoLemma58RootCandidateCleaning
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalCutOnline

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

/-- The literal planned root candidate used by the synchronized recursion. -/
abbrev plannedRootCandidate
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho : ℝ) (plan : RootTargetPlan P) :=
  rootCandidate G rho
    (rootWhole Pcluster Gdegree threshold quota R miss Q P)
    (rootRaw Pcluster Gdegree threshold quota R miss Q P)
    (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan)
    (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)

/-- The planned cleaning budget leaves at least one full root-count of
choices for every component root. -/
theorem numParts_le_card_plannedRootCandidate
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (plan : RootTargetPlan P)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H plan)
    (q : Fin P.numParts) :
    P.numParts ≤
      #(plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan q) := by
  apply root_count_le_card_rootCandidate G rootRho
    (rootWhole Pcluster Gdegree threshold quota R miss Q P)
    (rootRaw Pcluster Gdegree threshold quota R miss Q P)
    (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan)
    (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    q P.numParts
    (richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A rootRho plan q)
  · exact F.rootTargetBad_le Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H plan q
  · simpa only [card_rootRaw] using F.root_budget q

/-- Every planned root/root cut link retains a full root-count of choices in
the cleaned child reservoir. -/
theorem numParts_le_neighbors_plannedRootCandidate
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (plan : RootTargetPlan P)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H plan)
    (q : Fin P.numParts) (hq : q.val ≠ 0)
    (hroot : P.parent q hq = P.roots (P.parentPart q hq))
    (x : Bv)
    (hx : x ∈ plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho plan (P.parentPart q hq)) :
    P.numParts ≤
      #((plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho plan q).filter (G.Adj x)) := by
  obtain ⟨t, ht, htarget, hdegree⟩ :=
    F.rootLink Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
      P S A hT G rootRho rootDensity H plan q hq hroot
  exact rootCount_le_neighbors_rootCandidate G rootRho
    (rootWhole Pcluster Gdegree threshold quota R miss Q P)
    (rootRaw Pcluster Gdegree threshold quota R miss Q P)
    (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan)
    (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (P.parentPart q hq) q x t ht hx htarget P.numParts
    (richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A rootRho plan q)
    (F.rootTargetBad_le Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H plan q)
    hdegree

/-- Planned target cleaning followed by the globally synchronized online
owner recursion.  In particular, roots are chosen only when their actual cut
parent has already been embedded. -/
theorem exists_treeCopy_of_richPlannedGlobalOnline
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (plan : RootTargetPlan P)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H plan)
    (initialRootImage : Fin P.numParts → Bv)
    (edgeRho edgeDensity : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (hsuccessor : ∀ n hn
      (state : CutOnlineOwnerPrefixState P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richOnlineEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G
          (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A G rootRho plan))
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho plan) n)
      z,
      z ∈ onlineRootEligible P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richOnlineEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G
          (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A G rootRho plan))
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho plan) n hn state →
      (∀ q, q.val < n → z ≠ state.state.rootImage q) →
      RichCleanOnlineOwnerSuccessorData Pcluster Gdegree threshold quota R
        miss Q sourceDensity E0 Mb P S A G
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho plan)
        edgeRho edgeDensity n hn state.state z) :
    Nonempty (T.Copy G) := by
  let candidate := plannedRootCandidate Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P S A G rootRho plan
  have hfirst : P.numParts ≤ #(candidate ⟨0, P.numParts_pos⟩) := by
    apply root_count_le_card_rootCandidate G rootRho
      (rootWhole Pcluster Gdegree threshold quota R miss Q P)
      (rootRaw Pcluster Gdegree threshold quota R miss Q P)
      (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A plan)
      (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb)
      (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb)
      ⟨0, P.numParts_pos⟩ P.numParts
      (richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A rootRho plan ⟨0, P.numParts_pos⟩)
    · exact F.rootTargetBad_le Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho rootDensity H plan _
    · simpa only [card_rootRaw] using F.root_budget ⟨0, P.numParts_pos⟩
  have hrootLink : ∀ q (hq : q.val ≠ 0)
      (hroot : P.parent q hq = P.roots (P.parentPart q hq))
      x, x ∈ candidate (P.parentPart q hq) →
      P.numParts ≤ #((candidate q).filter (G.Adj x)) := by
    intro q hq hroot x hx
    obtain ⟨t, ht, htarget, hdegree⟩ :=
      F.rootLink Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        P S A hT G rootRho rootDensity H plan q hq hroot
    exact rootCount_le_neighbors_rootCandidate G rootRho
      (rootWhole Pcluster Gdegree threshold quota R miss Q P)
      (rootRaw Pcluster Gdegree threshold quota R miss Q P)
      (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A plan)
      (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb)
      (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb)
      (P.parentPart q hq) q x t ht hx htarget P.numParts
      (richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A rootRho plan q)
      (F.rootTargetBad_le Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho rootDensity H plan q)
      hdegree
  apply exists_treeCopy_of_richOnlineParentCleaning Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S A G hdisjoint candidate
    initialRootImage hfirst hrootLink edgeRho edgeDensity hsuccessor
  intro q z hz e c
  have hraw := rootCandidate_subset_raw G rootRho
    (rootWhole Pcluster Gdegree threshold quota R miss Q P)
    (rootRaw Pcluster Gdegree threshold quota R miss Q P)
    (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan)
    (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb) q hz
  exact Finset.disjoint_left.mp
    (rootRawSide_disjoint_endpoint
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (componentReservoirSide P q) e c) hraw

end Erdos547b.ZhaoClaim615RichGlobalOnlinePlannedApplication

#print axioms Erdos547b.ZhaoClaim615RichGlobalOnlinePlannedApplication.exists_treeCopy_of_richPlannedGlobalOnline
