/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichCoordinateOrientedPairFacts
import ErdosProblems.Erdos547b.Claim615RichCoordinateOrientedCapacityFacts
import ErdosProblems.Erdos547b.Claim615RichCoordinateCapacityNumerics
import ErdosProblems.Erdos547b.Claim615CoordinateRootLoad

/-!
# Branchwise-oriented coordinate containment for Zhao Claim 6.15

This endpoint keeps the two matching endpoints separate.  It accepts the
literal branch orientation and the four literal coordinate-pool capacity
inequalities, exactly as supplied by Lemma 5.8's threshold/Appendix cases.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichCoordinateOrientedContainment

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616CoordinateCanonicalOptional
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools
open Erdos547b.ZhaoClaim615RichCoordinateApplication
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichCoordinateOrientedPairFacts
open Erdos547b.ZhaoClaim615RichCoordinateCapacityNumerics
open Erdos547b.ZhaoClaim615RichCoordinateOrientedCapacityFacts
open Erdos547b.ZhaoClaim615CoordinateRootLoad
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest

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

/-- Concrete containment with an arbitrary branchwise orientation and exact
endpoint loads.  No copy, embedding, continuation, or cut-forest datum is an
input. -/
theorem isContained_of_orientedCoordinateSourceAllocation
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (hsmall : 1 ≤ small)
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    {K0 K1 Kb : Type*}
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (edge0 : K0 → MatchingEdge Q.claim67.M)
    (edge1 : K1 → MatchingEdge Q.claim67.M)
    (edgeb : Kb → MatchingEdge Q.claim67.M)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density removalBudget : ℝ)
    (Hpair : ReducedPairRealization Pcluster R G rho density)
    (havailable : available ⊆ halfBranches P)
    (hroot0 : ∀ j, j ∈ S.selected → (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge0 (A.F0edge j)).1 (orient j 0)))
    (hroot1 : ∀ j, j ∈ majorResidualBranches P S →
      (padGraph R).Adj (Sum.inl Q.A)
        (matchingEdgeEndpoint (edge1 (A.F1edge j)).1 (orient j 0)))
    (hrootb : ∀ j, j ∈ minorBranches P → (padGraph R).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (edgeb (A.Fbedge j)).1 (orient j 0)))
    (hA : rho * #(clusterVertices Pcluster Q.A) ≤ quota)
    (hB : rho * #(clusterVertices Pcluster Q.B) ≤ quota)
    (hmatching : ∀ e : MatchingEdge Q.claim67.M, ∀ side : Fin 2,
      rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨e, side⟩)) + (2 * quota : ℕ) ≤
        #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨e, side⟩)))
    (hremoval : ∀ i a,
      coordinateRemovalBudget
        (AllocationHierarchy hT P (canonicalOptional P)) rho
        (coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
          (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
          edge0 edge1 edgeb orient)
        (slotWhole Pcluster Gdegree threshold quota R miss Q)
        (fun i a ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
          (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
            capacity0 capacity1 capacityb A edge0 edge1 edgeb orient i a)) i a ≤
        removalBudget)
    (hreserveCapacity : ∀ side,
      (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
            (coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
              (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
              edge0 edge1 edgeb orient)
            (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
            (Sum.inl side : RootSlot (MatchingEdge Q.claim67.M)) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inl side)))
    (h0Capacity : ∀ e c,
      (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
            (coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
              (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
              edge0 edge1 edgeb orient)
            (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
            (Sum.inr ⟨edge0 e, c⟩ : RootSlot (MatchingEdge Q.claim67.M)) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨edge0 e, c⟩)))
    (h1Capacity : ∀ e c,
      (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
            (coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
              (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
              edge0 edge1 edgeb orient)
            (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
            (Sum.inr ⟨edge1 e, c⟩ : RootSlot (MatchingEdge Q.claim67.M)) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨edge1 e, c⟩)))
    (hbCapacity : ∀ e c,
      (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
            (coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
              (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A
              edge0 edge1 edgeb orient)
            (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
              capacity0 capacity1 capacityb A edge0 edge1 edgeb orient)
            (Sum.inr ⟨edgeb e, c⟩ : RootSlot (MatchingEdge Q.claim67.M)) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨edgeb e, c⟩)))
    (hbadBudget :
      (#(Finset.univ.filter fun i ↦
          (AllocationHierarchy hT P (canonicalOptional P)).parent i =
            Sum.inl 0) : ℝ) *
        (rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))) <
        #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))) :
    T.IsContained G := by
  have pairFacts := orientedCoordinatePairFacts Pcluster Gdegree threshold quota
    R miss Q hT P S capacity0 capacity1 capacityb A edge0 edge1 edgeb orient G
    rho density Hpair havailable hroot0 hroot1 hrootb
  have hrawLarge : ∀ slot : RootSlot (MatchingEdge Q.claim67.M),
      rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q slot) ≤
        #(slotRaw Pcluster Gdegree threshold quota R miss Q slot) :=
    richSlotRaw_large Pcluster Gdegree threshold quota R miss Q rho hA hB
      hmatching
  have hsegmentSmall : ∀ i,
      (AllocationHierarchy hT P (canonicalOptional P)).segments.size i ≤ small :=
    by
      intro i
      cases hclass : segmentSourceClass hT P (canonicalOptional P) i with
      | inl q =>
          have hiRoot : i ∈ rootSegments hT P (canonicalOptional P) :=
            (mem_rootSegments_iff hT P (canonicalOptional P) i).2 ⟨q, hclass⟩
          rw [rootSegment_size_eq_one hT P (canonicalOptional P) i hiRoot]
          exact hsmall
      | inr j =>
          exact (segment_size_le_sourceBranch hT P (canonicalOptional P) i j
            hclass).trans (canonical_branch_size_le_small P j)
  have capacityFacts := richCoordinateCapacityFacts_of_endpointLoads Pcluster
    Gdegree threshold quota R miss Q hT P (canonicalOptional P) ∅
    (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A edge0 edge1
    edgeb orient rho density removalBudget hsegmentSmall hrawLarge hremoval
    hreserveCapacity h0Capacity h1Capacity hbCapacity hbadBudget
  exact isContained_of_richCoordinateHostFacts Pcluster Gdegree threshold quota R
    miss Q hT P (canonicalOptional P) ∅ (sourceVertexReservoirSide P) S
    capacity0 capacity1 capacityb A edge0 edge1 edgeb orient G rho density
    removalBudget pairFacts capacityFacts

end Erdos547b.ZhaoClaim615RichCoordinateOrientedContainment

#print axioms Erdos547b.ZhaoClaim615RichCoordinateOrientedContainment.isContained_of_orientedCoordinateSourceAllocation
