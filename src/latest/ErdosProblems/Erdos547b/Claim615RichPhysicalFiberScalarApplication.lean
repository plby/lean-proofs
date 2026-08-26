/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalFiberApplication
import ErdosProblems.Erdos547b.Claim615CoordinateRootLoad
import ErdosProblems.Erdos547b.HierarchicalCoordinateRemovalBudgetBoundsGeneral

/-!
# Scalar cleaning wrapper for a physical-fiber plan

This module is independent of which exceptional family supplied the local
fiber certificates.  A common slot cardinality and one scalar deletion
budget imply the literal coordinate-removal inequalities, while the load in
either distinguished reservoir is bounded by the number of hierarchy
segments.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalFiberScalarApplication

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
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads
open Erdos547b.ZhaoClaim615RichPhysicalFiberApplication
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.RegularPair
open Erdos547b.ZhaoClaim615CoordinateRootLoad
open Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBoundsGeneral
open Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest
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

/-- Allocation-independent scalar facts shared by all physical-fiber
orientation cases. -/
structure PhysicalFiberGlobalFacts
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (rho density removalBudget : ℝ) (m : ℕ) : Prop where
  rho_nonneg : 0 ≤ rho
  whole_card : ∀ slot : RootSlot (MatchingEdge Q.claim67.M),
    #(slotWhole Pcluster Gdegree threshold quota R miss Q slot) = m
  removal :
    ((Fintype.card (SegmentIndex hT P (canonicalOptional P)) + small : ℕ) : ℝ) *
        (rho * m) ≤ removalBudget
  A_reserve : rho * #(clusterVertices Pcluster Q.A) ≤ quota
  B_reserve : rho * #(clusterVertices Pcluster Q.B) ≤ quota
  matching_reserve : ∀ e : MatchingEdge Q.claim67.M, ∀ side : Fin 2,
    rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q
        (Sum.inr ⟨e, side⟩)) + (2 * quota : ℕ) ≤
      #(slotWhole Pcluster Gdegree threshold quota R miss Q
        (Sum.inr ⟨e, side⟩))
  distinguished_margin : ∀ side,
    (Fintype.card (SegmentIndex hT P (canonicalOptional P)) + small + 1 : ℝ) +
        removalBudget + 1 ≤
      (density - rho) *
        #(slotRaw Pcluster Gdegree threshold quota R miss Q (Sum.inl side))
  direct_root_budget :
    (#(Finset.univ.filter fun i ↦
        (AllocationHierarchy hT P (canonicalOptional P)).parent i =
          Sum.inl 0) : ℝ) *
      (rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q
        (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))) <
      #(slotRaw Pcluster Gdegree threshold quota R miss Q
        (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))

/-- A physical-fiber plan plus common scalar cleaning facts gives the full
coordinate-hierarchy containment. -/
theorem isContained_of_physicalFiberPlanScalarFacts
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
    (m : ℕ)
    (H : PhysicalFiberGlobalFacts Pcluster Gdegree threshold quota R miss Q P
      hT rho density removalBudget m) :
    T.IsContained G := by
  classical
  let orient := physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient
  let rootSlot := coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
    (sourceVertexReservoirSide P) S cap0 cap1 capb A
    (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
    (edgeb Q sourceDensity Mb) orient
  let interiorSlot := coordinateHierarchyInteriorSlot hT P
    (canonicalOptional P) S cap0 cap1 capb A
    (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
    (edgeb Q sourceDensity Mb) orient
  let whole := slotWhole Pcluster Gdegree threshold quota R miss Q
  let interiorWhole : (i : SegmentIndex hT P (canonicalOptional P)) →
      Fin ((AllocationHierarchy hT P (canonicalOptional P)).segments.size i) →
        Finset Bv := fun i a ↦ whole (interiorSlot i a)
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
  have hcandidate : ∀ i a,
      #(rawCandidate (AllocationHierarchy hT P (canonicalOptional P)) rootSlot
        whole interiorWhole i a) ≤ m := by
    intro i a
    simp only [rawCandidate]
    split
    · exact (H.whole_card _).le
    · exact (H.whole_card _).le
  have hremoval : ∀ i a,
      coordinateRemovalBudget (AllocationHierarchy hT P (canonicalOptional P))
        rho rootSlot whole interiorWhole i a ≤ removalBudget :=
    coordinateRemovalBudget_le
      (AllocationHierarchy hT P (canonicalOptional P)) rho removalBudget
      rootSlot whole interiorWhole small m H.rho_nonneg hsegmentSmall hcandidate
      (by simpa only [SegmentIndex, Fintype.card_fin] using H.removal)
  have hreserveLoad : ∀ side,
      coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
          rootSlot interiorSlot (Sum.inl side : RootSlot (MatchingEdge Q.claim67.M)) ≤
        Fintype.card (SegmentIndex hT P (canonicalOptional P)) := by
    intro side
    exact coordinatePoolLoad_reserve_le_card_segments hT P
      (canonicalOptional P) ∅ (sourceVertexReservoirSide P) S cap0 cap1 capb A
      (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
      (edgeb Q sourceDensity Mb) orient side
  have hreserveCapacity : ∀ side,
      (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
            rootSlot interiorSlot (Sum.inl side : RootSlot (MatchingEdge Q.claim67.M)) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) *
          #(slotRaw Pcluster Gdegree threshold quota R miss Q (Sum.inl side)) := by
    intro side
    have hloadR :
        (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
          rootSlot interiorSlot (Sum.inl side : RootSlot (MatchingEdge Q.claim67.M)) : ℝ) ≤
          Fintype.card (SegmentIndex hT P (canonicalOptional P)) := by
      exact_mod_cast hreserveLoad side
    linarith [H.distinguished_margin side]
  apply isContained_of_physicalFiberSideLoads Pcluster Gdegree threshold quota
    R miss Q sourceDensity E0 Mb hT P hsmall S A havailable hdisjoint G rho
    density removalBudget plan Hpair H.A_reserve H.B_reserve H.matching_reserve
  · simpa only [rootSlot, interiorSlot, whole, interiorWhole, orient] using
      hremoval
  · simpa only [rootSlot, interiorSlot, orient] using hreserveCapacity
  · exact H.direct_root_budget

end Erdos547b.ZhaoClaim615RichPhysicalFiberScalarApplication

#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberScalarApplication.isContained_of_physicalFiberPlanScalarFacts
