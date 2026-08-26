/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichGlobalOnlineApplication
import ErdosProblems.Erdos547b.Lemma58OnlineParentCleaning

/-!
# Target-relative parent cleaning in the rich physical matching

This wrapper fixes every physical endpoint to the permanent rich endpoint
minus the small set of vertices having too few neighbours in a future child
root reservoir.  The dynamic eligible-root bound is then derived internally.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichGlobalOnlineCleaning

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
open Erdos547b.ZhaoClaim615RichGlobalOnlineApplication
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58GlobalCutAssembly
open Erdos547b.ZhaoLemma58OnlineParentCleaning

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

/-- Rich physical endpoints after target-relative future-parent cleaning. -/
abbrev richOnlineEndpoint
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset Bv) :=
  onlineCleanEndpoint P G rootCandidate
    (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A))
    (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)

/-- Exact source-data callback against the target-relative cleaned rich
endpoints. -/
abbrev RichCleanOnlineOwnerSuccessorData
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootCandidate : Fin P.numParts → Finset Bv)
    (rho density : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (n : ℕ) (hn : n < P.numParts)
    (state : OnlineOwnerPrefixState (branchForest P) G
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richOnlineEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootCandidate)
      rootCandidate n)
    (z : Bv) :=
  OnlineOwnerSuccessorData (branchForest P) G
    (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A))
    (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
    (richOnlineEndpoint Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootCandidate)
    rho density rootCandidate n hn state z

/-- Full synchronized online application with the eligible-root cardinal
derived from the actual parent-cleaned endpoint. -/
theorem exists_treeCopy_of_richOnlineParentCleaning
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (rootCandidate : Fin P.numParts → Finset Bv)
    (initialRootImage : Fin P.numParts → Bv)
    (hfirst : P.numParts ≤
      #(rootCandidate ⟨0, P.numParts_pos⟩))
    (hrootLink : ∀ q (hq : q.val ≠ 0)
      (hroot : P.parent q hq = P.roots (P.parentPart q hq))
      x, x ∈ rootCandidate (P.parentPart q hq) →
      P.numParts ≤ #((rootCandidate q).filter (G.Adj x)))
    (rho density : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (hsuccessor : ∀ n hn
      (state : CutOnlineOwnerPrefixState P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richOnlineEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootCandidate)
        rootCandidate n)
      z,
      z ∈ onlineRootEligible P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richOnlineEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootCandidate)
        rootCandidate n hn state →
      (∀ q, q.val < n → z ≠ state.state.rootImage q) →
      RichCleanOnlineOwnerSuccessorData Pcluster Gdegree threshold quota R
        miss Q sourceDensity E0 Mb P S A G rootCandidate rho density n hn
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
  let clean := richOnlineEndpoint Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A G rootCandidate
  have hcleanWhole : ∀ e c, clean e c ⊆ whole e c := by
    intro e c
    exact (onlineCleanEndpoint_subset P G rootCandidate assign endpoint e c).trans
      (endpoint_subset_whole
        (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
        (quota := quota) (R := R) (miss := miss) (Q := Q)
        (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e c)
  have hcleanSupport : ∀ e e', e ≠ e' →
      Disjoint (clean e 0 ∪ clean e 1) (clean e' 0 ∪ clean e' 1) := by
    intro e e' he
    apply (endpointSupport_disjoint
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      hdisjoint e e' he).mono
    · exact Finset.union_subset_union
        (onlineCleanEndpoint_subset P G rootCandidate assign endpoint e 0)
        (onlineCleanEndpoint_subset P G rootCandidate assign endpoint e 1)
    · exact Finset.union_subset_union
        (onlineCleanEndpoint_subset P G rootCandidate assign endpoint e' 0)
        (onlineCleanEndpoint_subset P G rootCandidate assign endpoint e' 1)
  obtain ⟨state⟩ := exists_cutOnlineOwnerPrefixState P G assign whole clean
    hcleanWhole
    (whole_disjoint
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) hdisjoint)
    rho density rootCandidate initialRootImage
    (fun n hn state ↦ card_onlineRootEligible_cleanEndpoint P G rootCandidate
      assign endpoint hfirst hrootLink n hn state)
    hsuccessor
  refine ⟨treeCopyOfCutOnlineState P G assign clean rootCandidate state
    hcleanSupport ?_⟩
  intro q e c
  have hraw := hrootOutside q (state.state.rootImage q)
    (state.state.root_mem q q.isLt) e c
  exact fun hm ↦ hraw
    (onlineCleanEndpoint_subset P G rootCandidate assign endpoint e c hm)

end Erdos547b.ZhaoClaim615RichGlobalOnlineCleaning

#print axioms Erdos547b.ZhaoClaim615RichGlobalOnlineCleaning.exists_treeCopy_of_richOnlineParentCleaning
