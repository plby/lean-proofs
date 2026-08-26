/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichCoordinateContainment
import ErdosProblems.Erdos547b.HierarchicalCoordinateRemovalBudgetBoundsGeneral

/-!
# Source-packing specialization of coordinate Claim 6.15

The public theorem in this file constructs the three finite branch packings
internally.  Its source inputs are aggregate integral capacity inequalities;
the cleaning loss is derived from a common whole-slot size and one scalar
budget.  No allocation, copy, embedding, or continuation is assumed.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichCoordinateSourceApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616CoordinateCanonicalOptional
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615CoordinateOrientation
open Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichCoordinateContainment
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBoundsGeneral
open Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest

universe u v w

/-- The honest discrete hypotheses for the three finite source packings. -/
structure SourcePackingBudgets
    (Pmass0 Pmass1 Pmassb card0 card1 cardb small : ℕ)
    {K0 K1 Kb : Type*} [Fintype K0] [Fintype K1] [Fintype Kb]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ) : Prop where
  card0_eq : Fintype.card K0 = card0
  card1_eq : Fintype.card K1 = card1
  cardb_eq : Fintype.card Kb = cardb
  card0_pos : 0 < card0
  card1_pos : 0 < card1
  cardb_pos : 0 < cardb
  family0 : Pmass0 + card0 * small ≤ ∑ e : K0, capacity0 e
  family1 : Pmass1 + card1 * small ≤ ∑ e : K1, capacity1 e
  familyb : Pmassb + cardb * small ≤ ∑ e : Kb, capacityb e

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

/-- Construct the literal source allocation and invoke the concrete
coordinate containment theorem. -/
theorem isContained_of_richCoordinatePackingBudgets
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
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ)
    (capacityb : Kb → ℕ)
    (edge0 : K0 → MatchingEdge Q.claim67.M)
    (edge1 : K1 → MatchingEdge Q.claim67.M)
    (edgeb : Kb → MatchingEdge Q.claim67.M)
    (rootSide0 : K0 → Fin 2) (rootSide1 : K1 → Fin 2)
    (rootSideb : Kb → Fin 2)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density removalBudget : ℝ)
    (Hpair : ReducedPairRealization Pcluster R G rho density)
    (havailable : available ⊆ halfBranches P)
    (hroot0 : ∀ e : K0, (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge0 e).1 (rootSide0 e)))
    (hroot1 : ∀ e : K1, (padGraph R).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge1 e).1 (rootSide1 e)))
    (hrootb : ∀ e : Kb, (padGraph R).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint (edgeb e).1 (rootSideb e)))
    (hedge0 : Function.Injective edge0)
    (hedge1 : Function.Injective edge1)
    (hedgeb : Function.Injective edgeb)
    (h01 : ∀ e0 e1, edge0 e0 ≠ edge1 e1)
    (h0b : ∀ e0 eb, edge0 e0 ≠ edgeb eb)
    (h1b : ∀ e1 eb, edge1 e1 ≠ edgeb eb)
    (card0 card1 cardb : ℕ)
    (packing : SourcePackingBudgets (branchMass P S.selected)
      (branchMass P (majorResidualBranches P S))
      (branchMass P (minorBranches P)) card0 card1 cardb small capacity0
      capacity1 capacityb)
    (m : ℕ)
    (hwholeCard : ∀ slot : RootSlot (MatchingEdge Q.claim67.M),
      #(slotWhole Pcluster Gdegree threshold quota R miss Q slot) = m)
    (hrho : 0 ≤ rho)
    (hremovalScalar :
      ((Fintype.card (SegmentIndex hT P (canonicalOptional P)) + small : ℕ) :
          ℝ) * (rho * m) ≤ removalBudget)
    (hA : rho * #(clusterVertices Pcluster Q.A) ≤ quota)
    (hB : rho * #(clusterVertices Pcluster Q.B) ≤ quota)
    (hmatching : ∀ e : MatchingEdge Q.claim67.M, ∀ side : Fin 2,
      rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨e, side⟩)) + (2 * quota : ℕ) ≤
        #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨e, side⟩)))
    (hreserveMargin : ∀ side,
      (Fintype.card (SegmentIndex hT P (canonicalOptional P)) + small + 1 : ℝ) +
          removalBudget + 1 ≤
        (density - rho) *
          #(slotRaw Pcluster Gdegree threshold quota R miss Q (Sum.inl side)))
    (h0Margin : ∀ e c,
      (capacity0 e + small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨edge0 e, c⟩)))
    (h1Margin : ∀ e c,
      (capacity1 e + small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨edge1 e, c⟩)))
    (hbMargin : ∀ e c,
      (capacityb e + small + 1 : ℝ) + removalBudget + 1 ≤
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
  classical
  letI : Nonempty K0 := Fintype.card_pos_iff.mp (packing.card0_eq.symm ▸
    packing.card0_pos)
  letI : Nonempty K1 := Fintype.card_pos_iff.mp (packing.card1_eq.symm ▸
    packing.card1_pos)
  letI : Nonempty Kb := Fintype.card_pos_iff.mp (packing.cardb_eq.symm ▸
    packing.cardb_pos)
  obtain ⟨A⟩ := exists_sourceAllocation P S K0 K1 Kb capacity0 capacity1
    capacityb
    (by simpa [packing.card0_eq] using packing.family0)
    (by simpa [packing.card1_eq] using packing.family1)
    (by simpa [packing.cardb_eq] using packing.familyb)
  let orient := canonicalCoordinateOrientation P S capacity0 capacity1
    capacityb A rootSide0 rootSide1 rootSideb
  let rootSlot := coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
    (sourceVertexReservoirSide P) S capacity0 capacity1 capacityb A edge0 edge1
    edgeb orient
  let interiorSlot := coordinateHierarchyInteriorSlot hT P
    (canonicalOptional P) S capacity0 capacity1 capacityb A edge0 edge1 edgeb
    orient
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
    · exact (hwholeCard _).le
    · exact (hwholeCard _).le
  have hremoval : ∀ i a,
      coordinateRemovalBudget (AllocationHierarchy hT P (canonicalOptional P))
        rho rootSlot whole interiorWhole i a ≤ removalBudget :=
    coordinateRemovalBudget_le
      (AllocationHierarchy hT P (canonicalOptional P)) rho removalBudget
      rootSlot whole interiorWhole small m hrho hsegmentSmall hcandidate
      (by simpa only [SegmentIndex, Fintype.card_fin] using hremovalScalar)
  exact isContained_of_richCoordinateSourceAllocation Pcluster Gdegree threshold
    quota R miss Q hT P hsmall S capacity0 capacity1 capacityb A edge0 edge1
    edgeb rootSide0 rootSide1 rootSideb G rho density removalBudget Hpair
    havailable hroot0 hroot1 hrootb hedge0 hedge1 hedgeb h01 h0b h1b hA hB
    hmatching (by simpa only [rootSlot, interiorSlot, whole, interiorWhole,
      orient] using hremoval) hreserveMargin h0Margin h1Margin hbMargin
    hbadBudget

end Erdos547b.ZhaoClaim615RichCoordinateSourceApplication

#print axioms Erdos547b.ZhaoClaim615RichCoordinateSourceApplication.isContained_of_richCoordinatePackingBudgets
