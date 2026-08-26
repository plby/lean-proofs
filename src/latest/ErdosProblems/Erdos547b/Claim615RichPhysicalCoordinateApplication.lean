/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichCoordinateOrientedContainment
import ErdosProblems.Erdos547b.Claim615RichPhysicalEdgeFamilies

/-!
# Concrete physical-family coordinate application for Claim 6.15

The three abstract source families, edge maps, orientations, and root-facing
adjacency rows are specialized here to the exceptional, positive remaining,
and reserved physical matching families.  The remaining hypotheses are the
literal endpoint capacity and cleaning inequalities.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalCoordinateApplication

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
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichCoordinateOrientedContainment
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest

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

/-- Canonical source packing into the three concrete physical families. -/
noncomputable def canonicalPhysicalSourceAllocation
    (P : ZhaoForestPartition T globalRoot small)
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    (hcount : 0 < count) (htargetB : 0 < targetB)
    (hnonnegA : ∀ e ∈ allMatchingEdges Q.claim67.M,
      0 ≤ N * (sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 0) +
        sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 1)))
    (hremainingA : 0 < sourceDegree Q.claim67.M L sourceDensity N
      (Sum.inl Q.A) (allMatchingEdges Q.claim67.M \
        (E0.selected ∪ Mb.selected))) :
    PhysicalSourceAllocation Q sourceDensity P S E0 Mb :=
  Classical.choice (exists_sourceAllocation_average_physical
    (Q := Q) (sourceDensity := sourceDensity) (P := P) (S := S)
    (E0 := E0) (Mb := Mb) hcount htargetB hnonnegA hremainingA)

/-- The oriented coordinate backend specialized to the three literal rich
matching families and their canonical source-facing endpoint choices. -/
theorem isContained_of_physicalEdgesOrientedSourceAllocation
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (hsmall : 1 ≤ small)
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density removalBudget : ℝ)
    (Hpair : ReducedPairRealization Pcluster R G rho density)
    (havailable : available ⊆ halfBranches P)
    (hroot0 : ∀ j, j ∈ S.selected → (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint
        (edge0 Q sourceDensity E0 (A.F0edge j)).1 (orient j 0)))
    (hroot1 : ∀ j, j ∈ majorResidualBranches P S →
      (padGraph R).Adj (Sum.inl Q.A)
        (matchingEdgeEndpoint
          (edge1 Q sourceDensity E0 Mb (A.F1edge j)).1 (orient j 0)))
    (hrootb : ∀ j, j ∈ minorBranches P →
      (padGraph R).Adj (Sum.inl Q.B)
        (matchingEdgeEndpoint
          (edgeb Q sourceDensity Mb (A.Fbedge j)).1 (orient j 0)))
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
          (sourceVertexReservoirSide P) S
          cap0 cap1 capb A
          (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
          (edgeb Q sourceDensity Mb)
          orient)
        (slotWhole Pcluster Gdegree threshold quota R miss Q)
        (fun i a ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
          (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
            cap0 cap1 capb A
            (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
            (edgeb Q sourceDensity Mb)
            orient i a)) i a ≤
        removalBudget)
    (hreserveCapacity : ∀ side,
      (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
            (coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
              (sourceVertexReservoirSide P) S
              cap0 cap1 capb A
              (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
              (edgeb Q sourceDensity Mb)
              orient)
            (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
              cap0 cap1 capb A
              (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
              (edgeb Q sourceDensity Mb)
              orient)
            (Sum.inl side : RootSlot (MatchingEdge Q.claim67.M)) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inl side)))
    (h0Capacity : ∀ e c,
      (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
            (coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
              (sourceVertexReservoirSide P) S
              cap0 cap1 capb A
              (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
              (edgeb Q sourceDensity Mb)
              orient)
            (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
              cap0 cap1 capb A
              (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
              (edgeb Q sourceDensity Mb)
              orient)
            (Sum.inr ⟨edge0 Q sourceDensity E0 e, c⟩ :
              RootSlot (MatchingEdge Q.claim67.M)) + small + 1 : ℝ) +
          removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨edge0 Q sourceDensity E0 e, c⟩)))
    (h1Capacity : ∀ e c,
      (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
            (coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
              (sourceVertexReservoirSide P) S
              cap0 cap1 capb A
              (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
              (edgeb Q sourceDensity Mb)
              orient)
            (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
              cap0 cap1 capb A
              (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
              (edgeb Q sourceDensity Mb)
              orient)
            (Sum.inr ⟨edge1 Q sourceDensity E0 Mb e, c⟩ :
              RootSlot (MatchingEdge Q.claim67.M)) + small + 1 : ℝ) +
          removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨edge1 Q sourceDensity E0 Mb e, c⟩)))
    (hbCapacity : ∀ e c,
      (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
            (coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
              (sourceVertexReservoirSide P) S
              cap0 cap1 capb A
              (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
              (edgeb Q sourceDensity Mb)
              orient)
            (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
              cap0 cap1 capb A
              (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
              (edgeb Q sourceDensity Mb)
              orient)
            (Sum.inr ⟨edgeb Q sourceDensity Mb e, c⟩ :
              RootSlot (MatchingEdge Q.claim67.M)) + small + 1 : ℝ) +
          removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨edgeb Q sourceDensity Mb e, c⟩)))
    (hbadBudget :
      (#(Finset.univ.filter fun i ↦
          (AllocationHierarchy hT P (canonicalOptional P)).parent i =
            Sum.inl 0) : ℝ) *
        (rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))) <
        #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))) :
    T.IsContained G := by
  apply isContained_of_orientedCoordinateSourceAllocation Pcluster Gdegree
    threshold quota R miss Q hT P hsmall S
    cap0 cap1 capb A
    (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
    (edgeb Q sourceDensity Mb)
    orient G rho density removalBudget
    Hpair havailable
  · exact hroot0
  · exact hroot1
  · exact hrootb
  · exact hA
  · exact hB
  · exact hmatching
  · exact hremoval
  · exact hreserveCapacity
  · exact h0Capacity
  · exact h1Capacity
  · exact hbCapacity
  · exact hbadBudget

end Erdos547b.ZhaoClaim615RichPhysicalCoordinateApplication

#print axioms Erdos547b.ZhaoClaim615RichPhysicalCoordinateApplication.isContained_of_physicalEdgesOrientedSourceAllocation
#print axioms Erdos547b.ZhaoClaim615RichPhysicalCoordinateApplication.canonicalPhysicalSourceAllocation
