/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchicalAllocation
import ErdosProblems.Erdos547b.Claim616

/-!
# Current rich source allocation for the coordinate Claim 6.16 backend

This is the allocation-only part of the rich construction, with no dependency
on the obsolete coarse HostPools modules.  `M_1` and `M_b` bins are literal
subtypes of original Claim-6.7 matching edges.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateAllocation

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchicalAllocation

universe u v

abbrev RemainingMinEdge
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA)
    (C : Finset K) :=
  {e : MatchingEdge C67.M //
    e ∈ Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C}

abbrev ReservedEdge
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA) :=
  {e : MatchingEdge C67.M // e ∈ D.mbEdges}

variable {TreeVertex : Type u} [Fintype TreeVertex] [DecidableEq TreeVertex]
variable {T : SimpleGraph TreeVertex} [DecidableRel T.Adj]
variable {globalRoot : TreeVertex} {small target slack : ℕ}

variable {Bv : Type v} {K : Type*}
variable [Fintype Bv] [DecidableEq Bv] [Fintype K] [DecidableEq K]
variable (G Gdegree : SimpleGraph Bv)
variable [DecidableRel G.Adj] [DecidableRel Gdegree.Adj]
variable (cluster : K → Finset Bv) (epsilon reducedDensity : ℚ)
variable [DecidableRel
  (regularityReducedGraph G cluster epsilon reducedDensity).Adj]
variable {L Oset : Finset K}
variable {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate
  (regularityReducedGraph G cluster epsilon reducedDensity) L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L Oset miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)
variable (Aroot Broot : K) (C : Finset K) (W : Finset K) (rhoK : ℕ)
variable (Pcluster : ClusterAssignment Bv K) (threshold quota : ℕ)
variable
  (H : IndexedHostSystem G cluster epsilon reducedDensity Aroot Broot C
    D.Mout W rhoK Pcluster threshold quota Gdegree)

include H

theorem exists_richSourceSegmentAllocation
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset TreeVertex)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb rootSlack : ℕ)
    (hrhoK : 0 < rhoK)
    (hMout : 0 < D.Mout.edgeSet.toFinite.toFinset.card)
    (hMone : 0 <
      (Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C).card)
    (hMb : 0 < D.mbEdges.card)
    (hrootSmall : ∀ j ∈ S.selected,
      F0segmentRootWeight hT P optional S j ≤ rootSlack)
    (hlevel0 : (∑ j ∈ S.selected,
        F0segmentRootWeight hT P optional S j) + C.card * rootSlack ≤
      C.card * clusterCap)
    (hbudget0 : (∑ j ∈ S.selected,
        ((branchForest P).branches.size j - 1)) ≤
      (4 * rhoK) * base0)
    (hbudget1 : OrderedBranchForest.edgeDemand (F1 P S) +
      (Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C).card *
          small ≤
        (Erdos547b.ZhaoClaim616.MatchingDecomposition.MoneEdges D C).card *
          base1)
    (hbudgetb : OrderedBranchForest.edgeDemand (Fb P) +
      D.mbEdges.card * small ≤ D.mbEdges.card * baseb) :
    Nonempty (SourceSegmentAllocation hT P optional S
      (fun _ : Fin C.card ↦ clusterCap)
      (fun i : Fin C.card ↦ indexedAllowedEdges
        (regularityReducedGraph G cluster epsilon reducedDensity)
        D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W i)
      (fun _ : RemainingMinEdge D C ↦ base1)
      (fun _ : ReservedEdge D ↦ baseb) base0) := by
  classical
  letI : Nonempty (Fin C.card) := by
    rw [H.cluster_card]
    exact ⟨⟨0, hrhoK⟩⟩
  letI : Nonempty (Fin D.Mout.edgeSet.toFinite.toFinset.card) :=
    ⟨⟨0, hMout⟩⟩
  letI : Nonempty (RemainingMinEdge D C) := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hMone
    exact ⟨⟨e, he⟩⟩
  letI : Nonempty (ReservedEdge D) := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hMb
    exact ⟨⟨e, he⟩⟩
  apply exists_sourceSegmentAllocation hT P optional S
    (fun _ : Fin C.card ↦ clusterCap)
    (fun i : Fin C.card ↦ indexedAllowedEdges
      (regularityReducedGraph G cluster epsilon reducedDensity)
      D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W i)
    (fun _ : RemainingMinEdge D C ↦ base1)
    (fun _ : ReservedEdge D ↦ baseb)
    (4 * rhoK) base0 rootSlack (by omega) hrootSmall
  · simpa using hlevel0
  · intro i
    exact H.allowed_card i
  · exact hbudget0
  · simpa [Fintype.card_coe] using hbudget1
  · simpa [Fintype.card_coe] using hbudgetb

end Erdos547b.ZhaoClaim616RichCoordinateAllocation

#print axioms Erdos547b.ZhaoClaim616RichCoordinateAllocation.exists_richSourceSegmentAllocation
