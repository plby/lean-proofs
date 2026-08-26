/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateCanonicalNumerics
import ErdosProblems.Erdos547b.Claim616CoordinateSourceAllocation
import ErdosProblems.Erdos547b.Claim616CoordinateDirectCount
import ErdosProblems.Erdos547b.Claim616RichCoordinateBudgetFacts
import ErdosProblems.Erdos547b.HierarchicalCoordinateRemovalBudgetBoundsGeneral

/-!
# Source-allocation specialization of rich coordinate containment

This is the first coordinate endpoint whose public boundary contains no
`SourceSegmentAllocation`.  It constructs that allocation from the three
literal finite packing budgets, then derives the coordinate-removal and
direct-root Hall records from coarse scalar bounds.

The packing inequalities remain hypotheses here on purpose.  The current
rich Lemma 6.11 output records real source-degree sums, but does not yet turn
them into the three integral, per-family bin capacities used below.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateSourceApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616HierarchicalAllocation
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoClaim616HierarchicalCoordinateHostLayout
open Erdos547b.ZhaoClaim616CoordinateCanonicalOptional
open Erdos547b.ZhaoClaim616CoordinateDirectCount
open Erdos547b.ZhaoClaim616CoordinateOrientation
open Erdos547b.ZhaoClaim616CoordinateSourceAllocation
open Erdos547b.ZhaoClaim616RichCoordinateAllocation
open Erdos547b.ZhaoClaim616RichCoordinateBudgetFacts
open Erdos547b.ZhaoClaim616RichCoordinateContainment
open Erdos547b.ZhaoClaim616RichCoordinateCanonicalNumerics
open Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBounds
open Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBoundsGeneral
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u v w

/-- The genuinely discrete inputs to the three source packings.  Keeping
these in one small record prevents the final theorem from exposing an
already-constructed allocation while making the still-missing arithmetic
boundary explicit. -/
structure SourcePackingScalars
    (target slack small clusterCount rhoK remainingCount reservedCount
      clusterCap base0 base1 baseb selectedDeep residualDemand minorDemand :
      ℕ) : Prop where
  rhoK_pos : 0 < rhoK
  remaining_pos : 0 < remainingCount
  reserved_pos : 0 < reservedCount
  level0 : (target + slack) * small + clusterCount * small ≤
    clusterCount * clusterCap
  selected : selectedDeep ≤ (4 * rhoK) * base0
  residual : residualDemand + remainingCount * small ≤
    remainingCount * base1
  minor : minorDemand + reservedCount * small ≤ reservedCount * baseb

/-- The two coarse online inequalities left after segment sizes, whole-slot
cardinalities, and direct-root counts have been bounded canonically. -/
structure CanonicalOnlineScalars
    (hierarchyBound small wholeBound quota : ℕ)
    (rho removalBudget : ℝ) : Prop where
  rho_nonneg : 0 ≤ rho
  removal : ((hierarchyBound + small : ℕ) : ℝ) *
      (rho * wholeBound) ≤ removalBudget
  direct : (hierarchyBound : ℝ) * (rho * wholeBound) < quota

variable {V : Type u} {B : Type v} {K : Type w}
variable [Fintype V] [DecidableEq V]
variable [Fintype B] [DecidableEq B] [Fintype K] [DecidableEq K]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}
variable (G Gdegree : SimpleGraph B)
variable [DecidableRel G.Adj] [DecidableRel Gdegree.Adj]
variable (cluster : K → Finset B) (epsilon density : ℚ)
variable [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
variable {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate
  (regularityReducedGraph G cluster epsilon density) L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)
variable (Aroot Broot : K) (C : Finset K) (rhoK : ℕ)
variable (Pcluster : ClusterAssignment B K) (threshold quota : ℕ)
variable
  (H : IndexedHostSystem G cluster epsilon density Aroot Broot C
    (MatchingDecomposition.Mout
      (R := regularityReducedGraph G cluster epsilon density) D)
    (MatchingDecomposition.V2
        (R := regularityReducedGraph G cluster epsilon density) D ∩
      (matchingSupport (MatchingDecomposition.Mout
          (R := regularityReducedGraph G cluster epsilon density) D) \
        matchingSupport (MatchingDecomposition.Mb
          (R := regularityReducedGraph G cluster epsilon density) D)))
    rhoK Pcluster threshold quota Gdegree)

include H

/-- Construct the literal source allocation and feed it to the canonical
numeric coordinate endpoint.  There is no copy, embedding, continuation, or
cut-forest-data premise. -/
theorem isContained_of_richCoordinatePackingScalars
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (hsmall : 1 ≤ small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (clusterCap base0 base1 baseb : ℕ)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (hCV1 : C ⊆ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D)
    (hV1Adj : ∀ x ∈ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Aroot x)
    (hMbAdj : ∀ e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Broot
          (matchingEdgeEndpoint e.1.1 (mbSide e)))
    (m : ℕ) (removalBudget : ℝ)
    (scale : CanonicalClusterScaleFacts cluster Aroot Broot
      (epsilon : ℝ) quota m)
    (margins : CanonicalMarginScalars P.numParts small clusterCap base0 base1
      baseb quota m (epsilon : ℝ) (density : ℝ) removalBudget)
    (packing : SourcePackingScalars target slack small C.card rhoK
      (MatchingDecomposition.MoneEdges
        (R := regularityReducedGraph G cluster epsilon density) D C).card
      (MatchingDecomposition.mbEdges
        (R := regularityReducedGraph G cluster epsilon density) D).card
      clusterCap base0 base1 baseb
      (∑ j ∈ S.selected, ((branchForest P).branches.size j - 1))
      (OrderedBranchForest.edgeDemand (F1 P S))
      (OrderedBranchForest.edgeDemand (Fb P)))
    (online : CanonicalOnlineScalars
      (Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot)) +
        (P.numParts + Fintype.card (BranchIndex P) + P.numParts))
      small m quota (epsilon : ℝ) removalBudget) :
    T.IsContained G := by
  classical
  letI : Nonempty (Fin C.card) := by
    rw [H.cluster_card]
    exact ⟨⟨0, packing.rhoK_pos⟩⟩
  let C0 : Fin C.card := Classical.choice inferInstance
  have hm0 : 0 < 4 * rhoK :=
    Nat.mul_pos (by norm_num) packing.rhoK_pos
  letI : Nonempty
      (Fin (MatchingDecomposition.Mout
        (R := regularityReducedGraph G cluster epsilon density)
        D).edgeSet.toFinite.toFinset.card) := by
    have hallowed := H.allowed_card C0
    have hpos : 0 < #(containmentAllowed0 G cluster epsilon density D C C0) := by
      exact hm0.trans_le hallowed
    obtain ⟨e, _he⟩ := Finset.card_pos.mp hpos
    exact ⟨e⟩
  letI : Nonempty (RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C) := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp packing.remaining_pos
    exact ⟨⟨e, he⟩⟩
  letI : Nonempty (ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D) := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp packing.reserved_pos
    exact ⟨⟨e, he⟩⟩
  obtain ⟨Aalloc⟩ := exists_sourceSegmentAllocation_targetLevel hT P
    (canonicalOptional P) S
    (fun _ : Fin C.card ↦ clusterCap)
    (containmentAllowed0 G cluster epsilon density D C)
    (fun _ : RemainingMinEdge
      (R := regularityReducedGraph G cluster epsilon density) D C ↦ base1)
    (fun _ : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D ↦ baseb)
    (4 * rhoK) base0 hm0
    (by simpa using packing.level0)
    (fun i ↦ H.allowed_card i) packing.selected
    (by simpa [Finset.sum_const] using packing.residual)
    (by simpa [Finset.sum_const] using packing.minor)
  let orient : BranchIndex P → Fin 2 ≃ Fin 2 :=
    canonicalCoordinateOrientation G cluster epsilon density D C hT P
      (canonicalOptional P) S clusterCap base0 base1 baseb Aalloc mbSide
  let rootSlot : SegmentIndex hT P (canonicalOptional P) →
      RootSlot (Fin C.card) (MatchingEdge C67.M) :=
    containmentRootSlot G cluster epsilon density D C hT P S clusterCap base0
      base1 baseb Aalloc orient
  let interiorSlot : (i : SegmentIndex hT P (canonicalOptional P)) →
      Fin ((AllocationHierarchy hT P (canonicalOptional P)).segments.size i) →
        RootSlot (Fin C.card) (MatchingEdge C67.M) :=
    containmentInteriorSlot G cluster epsilon density D C hT P S clusterCap
      base0 base1 baseb Aalloc orient
  let whole : RootSlot (Fin C.card) (MatchingEdge C67.M) → Finset B :=
    containmentWhole G cluster epsilon density Aroot Broot C
  let interiorWhole :
      (i : SegmentIndex hT P (canonicalOptional P)) →
        Fin ((AllocationHierarchy hT P (canonicalOptional P)).segments.size i) →
          Finset B := fun i a ↦ whole (interiorSlot i a)
  have hwholeSlot (slot : RootSlot (Fin C.card) (MatchingEdge C67.M)) :
      #(whole slot) = m := by
    simpa only [whole] using
      card_containmentWhole_eq G cluster epsilon density Aroot Broot C m
        scale.clusterCard slot
  have hcandidate : ∀ i a,
      #(rawCandidate (AllocationHierarchy hT P (canonicalOptional P)) rootSlot
        whole interiorWhole i a) ≤ m := by
    intro i a
    simp only [rawCandidate]
    split
    · exact (hwholeSlot _).le
    · exact (hwholeSlot _).le
  have removal : CoordinateRemovalBounds
      (AllocationHierarchy hT P (canonicalOptional P)) (epsilon : ℝ)
      rootSlot whole interiorWhole removalBudget := by
    have hsegments := card_segments_canonicalOptional_le hT P
    have hcount :
        Fintype.card (SegmentIndex hT P (canonicalOptional P)) + small ≤
          (Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot)) +
            (P.numParts + Fintype.card (BranchIndex P) + P.numParts)) +
              small := Nat.add_le_add_right hsegments small
    have hscaled :
        ((Fintype.card (SegmentIndex hT P (canonicalOptional P)) + small : ℕ) :
            ℝ) * ((epsilon : ℝ) * m) ≤
          ((Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot)) +
              (P.numParts + Fintype.card (BranchIndex P) + P.numParts) +
              small : ℕ) : ℝ) * ((epsilon : ℝ) * m) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcount
      · exact mul_nonneg online.rho_nonneg (Nat.cast_nonneg _)
    refine ⟨ZhaoHierarchicalCoordinateRemovalBudgetBoundsGeneral.coordinateRemovalBudget_le
      (AllocationHierarchy hT P (canonicalOptional P)) (epsilon : ℝ)
      removalBudget rootSlot whole interiorWhole small m online.rho_nonneg
      (canonicalOptional_segment_size_le_small hT P hsmall S) hcandidate ?_⟩
    simpa only [SegmentIndex, Fintype.card_fin] using hscaled.trans online.removal
  let sourceSlot : RootSlot (Fin C.card) (MatchingEdge C67.M) :=
    Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)
  let directBound :=
    Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot)) +
      (P.numParts + Fintype.card (BranchIndex P) + P.numParts)
  have directHall : DirectHallBound
      (AllocationHierarchy hT P (canonicalOptional P)) (epsilon : ℝ)
      (containmentWhole G cluster epsilon density Aroot Broot C sourceSlot)
      quota := by
    apply richDirectHallBound G cluster epsilon density
      (AllocationHierarchy hT P (canonicalOptional P)) Aroot Broot C
      sourceSlot quota m directBound online.rho_nonneg scale.clusterCard
    · simpa only [directBound] using
        card_directSegments_canonicalOptional_le hT P
    · simpa only [directBound] using online.direct
  exact isContained_of_richCoordinateCanonicalNumerics G Gdegree cluster
    epsilon density D Aroot Broot C rhoK Pcluster threshold quota H hT P
    hsmall S clusterCap base0 base1 baseb Aalloc mbSide hCV1 hV1Adj hMbAdj m
    removalBudget scale margins
    (by simpa only [rootSlot, interiorSlot, whole, interiorWhole, orient] using
      removal)
    (by simpa only [sourceSlot, rootSlot, interiorSlot, orient] using directHall)

end Erdos547b.ZhaoClaim616RichCoordinateSourceApplication

#print axioms Erdos547b.ZhaoClaim616RichCoordinateSourceApplication.isContained_of_richCoordinatePackingScalars
