/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicPlannedRootCleaning
import ErdosProblems.Erdos547b.Claim615RichDynamicApplication

/-!
# Rich dynamic application after planned root cleaning

The planned target list is chosen before the matching-edge orientations.
It therefore supports both the fixed threshold orientations of Parts 1/2
and the adaptive Appendix orientation of Part 3.  This wrapper first chooses
the distinguished roots from that list and then invokes the concrete
cut-aware edge-local backend.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichDynamicPlannedApplication

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
open Erdos547b.ZhaoLemma58RootCandidateCleaning
open Erdos547b.ZhaoLemma58RootSkeleton
open Erdos547b.ZhaoLemma58FullCutTree

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

/-- Planned root cleaning followed by the concrete cut-aware local backend.
The edge-local data are constructed only after the injective root map is
known, so their residual bad sets may refer to the actual root images. -/
theorem exists_treeCopy_of_richPlannedRootCleaningFacts
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (plan : RootTargetPlan P)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H plan)
    (edgeRho edgeDensity : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (hdata : ∀ rootImage : Fin P.numParts → Bv,
      (∀ q, rootImage q ∈ rootCandidate G rootRho
        (rootWhole Pcluster Gdegree threshold quota R miss Q P)
        (rootRaw Pcluster Gdegree threshold quota R miss Q P)
        (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A plan)
        (richTargetWhole Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb)
        (richTargetRaw Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb) q) →
      CutEdgeData P G G rootImage
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0
          Mb)
        (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb)
        edgeRho edgeDensity) :
    Nonempty (T.Copy G) := by
  obtain ⟨roots⟩ := F.exists_plannedRootSkeletonEmbedding Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S A hT G rootRho
    rootDensity H plan
  apply exists_treeCopy_of_richCutEdgeData Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P S A G hdisjoint roots.rootImage edgeRho
    edgeDensity (hdata roots.rootImage roots.mem_candidate) roots.injective
  · intro q e c
    have hraw := rootCandidate_subset_raw G rootRho
      (rootWhole Pcluster Gdegree threshold quota R miss Q P)
      (rootRaw Pcluster Gdegree threshold quota R miss Q P)
      (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A plan)
      (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb)
      (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb) q (roots.mem_candidate q)
    exact Finset.disjoint_left.mp
      (rootRawSide_disjoint_endpoint
        (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (componentReservoirSide P q) e c) hraw
  · exact roots.cut_root_adj

end Erdos547b.ZhaoClaim615RichDynamicPlannedApplication

#print axioms Erdos547b.ZhaoClaim615RichDynamicPlannedApplication.exists_treeCopy_of_richPlannedRootCleaningFacts
