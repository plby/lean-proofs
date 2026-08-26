/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalCoordinateApplication
import ErdosProblems.Erdos547b.Claim615RichPhysicalOrientationLoads

/-!
# Fiber-oriented physical coordinate application for Claim 6.15

This module replaces the three duplicated coordinate-pool capacity premises
by one source-faithful Lemma-5.4 side-load premise on every canonical physical
matching fiber.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalFiberApplication

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
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichPhysicalCoordinateApplication
open Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58MatchingAssembly
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

/-- Source and scalar data chosen independently on every physical matching
fiber.  It contains an orientation and the two properties actually consumed
by the coordinate hierarchy; it contains no embedding or containment. -/
structure PhysicalFiberPlan
    (P : ZhaoForestPartition T globalRoot small)
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    (cap0 : K0 Q sourceDensity E0 → ℕ)
    (cap1 : K1 Q sourceDensity E0 Mb → ℕ)
    (capb : Kb Q sourceDensity Mb → ℕ)
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb)
    (rho density removalBudget : ℝ) where
  orient : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
    Fin (matchingFiber
      (assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) e).card →
      Fin 2 ≃ Fin 2
  root_adj : ∀ e i,
    (padGraph R).Adj (physicalRootVertex Q sourceDensity E0 Mb e)
      (matchingEdgeEndpoint (indexedPhysicalEdge Q sourceDensity E0 Mb e).1
        (orient e i 0))
  capacity : ∀ e c,
    (sideLoad
        (selectedForest (branchForest P).branches
          (matchingFiber
            (assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
              (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) e))
        (orient e) c : ℝ) + small + 1 + removalBudget + 1 ≤
      (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
        (Sum.inr ⟨indexedPhysicalEdge Q sourceDensity E0 Mb e, c⟩))

/-- The concrete coordinate application with one capacity display per
physical matching fiber rather than three family-specific hierarchy loads. -/
theorem isContained_of_physicalFiberSideLoads
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
    (havailable : available ⊆ halfBranches P)
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density removalBudget : ℝ)
    (plan : PhysicalFiberPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S cap0 cap1 capb A rho density removalBudget)
    (Hpair : ReducedPairRealization Pcluster R G rho density)
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
          (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient))
        (slotWhole Pcluster Gdegree threshold quota R miss Q)
        (fun i a ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
          (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
            cap0 cap1 capb A
            (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
            (edgeb Q sourceDensity Mb)
            (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient)
            i a)) i a ≤ removalBudget)
    (hreserveCapacity : ∀ side,
      (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
            (coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
              (sourceVertexReservoirSide P) S
              cap0 cap1 capb A
              (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
              (edgeb Q sourceDensity Mb)
              (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient))
            (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
              cap0 cap1 capb A
              (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
              (edgeb Q sourceDensity Mb)
              (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient))
            (Sum.inl side : RootSlot (MatchingEdge Q.claim67.M)) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inl side)))
    (hbadBudget :
      (#(Finset.univ.filter fun i ↦
          (AllocationHierarchy hT P (canonicalOptional P)).parent i =
            Sum.inl 0) : ℝ) *
        (rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))) <
        #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))) :
    T.IsContained G := by
  apply isContained_of_physicalEdgesOrientedSourceAllocation Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb hT P hsmall S A
    (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient)
    G rho density removalBudget Hpair havailable
  · exact physicalFiberOrient_selected_root_adj Q sourceDensity E0 Mb P S A
      plan.orient plan.root_adj
  · exact physicalFiberOrient_residual_root_adj Q sourceDensity E0 Mb P S A
      plan.orient plan.root_adj
  · exact physicalFiberOrient_minor_root_adj Q sourceDensity E0 Mb P S A
      havailable plan.orient plan.root_adj
  · exact hA
  · exact hB
  · exact hmatching
  · exact hremoval
  · exact hreserveCapacity
  · intro e c
    have h := coordinatePoolLoad_physical_margin Q sourceDensity E0 Mb hT P
      S A (canonicalOptional P) ∅ (sourceVertexReservoirSide P) havailable
      hdisjoint plan.orient (exceptionalIndex Q sourceDensity E0 Mb e) c
      removalBudget
      ((density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
        (Sum.inr ⟨edge0 Q sourceDensity E0 e, c⟩)))
    simpa only [indexedPhysicalEdge_exceptionalIndex] using
      h (by simpa only [indexedPhysicalEdge_exceptionalIndex] using
        plan.capacity (exceptionalIndex Q sourceDensity E0 Mb e) c)
  · intro e c
    have h := coordinatePoolLoad_physical_margin Q sourceDensity E0 Mb hT P
      S A (canonicalOptional P) ∅ (sourceVertexReservoirSide P) havailable
      hdisjoint plan.orient (remainingIndex Q sourceDensity E0 Mb e) c
      removalBudget
      ((density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
        (Sum.inr ⟨edge1 Q sourceDensity E0 Mb e, c⟩)))
    simpa only [indexedPhysicalEdge_remainingIndex] using
      h (by simpa only [indexedPhysicalEdge_remainingIndex] using
        plan.capacity (remainingIndex Q sourceDensity E0 Mb e) c)
  · intro e c
    have h := coordinatePoolLoad_physical_margin Q sourceDensity E0 Mb hT P
      S A (canonicalOptional P) ∅ (sourceVertexReservoirSide P) havailable
      hdisjoint plan.orient (reservedIndex Q sourceDensity E0 Mb e) c
      removalBudget
      ((density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
        (Sum.inr ⟨edgeb Q sourceDensity Mb e, c⟩)))
    simpa only [indexedPhysicalEdge_reservedIndex] using
      h (by simpa only [indexedPhysicalEdge_reservedIndex] using
        plan.capacity (reservedIndex Q sourceDensity E0 Mb e) c)
  · exact hbadBudget

end Erdos547b.ZhaoClaim615RichPhysicalFiberApplication

#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberApplication.isContained_of_physicalFiberSideLoads
