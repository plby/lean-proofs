/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicApplication
import ErdosProblems.Erdos547b.Lemma58GlobalCutAssembly

/-!
# Globally synchronized rich Claim-6.15 application

This is the cut-aware dynamic endpoint with the source-faithful order of
operations.  Component `n` is embedded on every physical matching edge
before root `n+1` is selected from the neighborhood of its actual embedded
cut parent.  Consequently no union of sparse-pair non-neighbour sets is
deleted from the matching endpoints.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichGlobalOnlineApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
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
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58GlobalCutAssembly

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

/-- The exact source-data callback at one globally synchronized owner stage.
It contains only threshold/Appendix data; its realization is performed by
the checked `OwnerLocalStepData.realize` theorem inside the successor. -/
abbrev RichOnlineOwnerSuccessorData
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (rootCandidate : Fin P.numParts → Finset Bv)
    (n : ℕ) (hn : n < P.numParts)
    (state : OnlineOwnerPrefixState (branchForest P) G
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
      rootCandidate n)
    (z : Bv) :=
  OnlineOwnerSuccessorData (branchForest P) G
    (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A))
    (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
    (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
    rho density rootCandidate n hn state z

/-- Complete rich physical matching application of the synchronized online
constructor.  Roots are selected dynamically from actual cut-parent
neighborhoods, and every physical edge batch is realized internally from
`OwnerLocalStepData`. -/
theorem exists_treeCopy_of_richOnlineOwnerData
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (rootCandidate : Fin P.numParts → Finset Bv)
    (initialRootImage : Fin P.numParts → Bv)
    (rho density : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (heligible : ∀ n hn
      (state : CutOnlineOwnerPrefixState P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb) rootCandidate n),
      P.numParts ≤ #(onlineRootEligible P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb) rootCandidate n hn state))
    (hsuccessor : ∀ n hn
      (state : CutOnlineOwnerPrefixState P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb) rootCandidate n)
      z,
      z ∈ onlineRootEligible P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb) rootCandidate n hn state →
      (∀ q, q.val < n → z ≠ state.state.rootImage q) →
      RichOnlineOwnerSuccessorData Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rho density rootCandidate n hn
        state.state z)
    (hrootOutside : ∀ q z, z ∈ rootCandidate q → ∀ e c,
      z ∉ richEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb e c) :
    Nonempty (T.Copy G) := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let whole := richWhole Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb
  let endpoint := richEndpoint Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb
  obtain ⟨state⟩ := exists_cutOnlineOwnerPrefixState P G assign whole endpoint
    (endpoint_subset_whole
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb))
    (whole_disjoint
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) hdisjoint)
    rho density rootCandidate initialRootImage heligible hsuccessor
  refine ⟨treeCopyOfCutOnlineState P G assign endpoint rootCandidate state
    (endpointSupport_disjoint
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) hdisjoint) ?_⟩
  intro q e c
  exact hrootOutside q (state.state.rootImage q)
    (state.state.root_mem q q.isLt) e c

end Erdos547b.ZhaoClaim615RichGlobalOnlineApplication

#print axioms Erdos547b.ZhaoClaim615RichGlobalOnlineApplication.exists_treeCopy_of_richOnlineOwnerData
