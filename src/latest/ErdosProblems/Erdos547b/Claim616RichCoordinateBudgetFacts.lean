/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616CoordinateScalarBounds

/-!
# Coarse cleaning and Hall budgets for rich coordinate slots

Every whole rich coordinate slot is one regularity cluster.  Consequently a
single common cluster-cardinality identity turns the generic cleaning and
direct-root estimates into the two compact records used by the canonical
Claim 6.16 endpoint.
-/

open scoped BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateBudgetFacts

open Finset Fintype
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout
open Erdos547b.ZhaoClaim616HierarchicalCoordinateHostLayout
open Erdos547b.ZhaoClaim616RichCoordinateContainment
open Erdos547b.ZhaoClaim616RichCoordinateCanonicalNumerics
open Erdos547b.ZhaoClaim616CoordinateScalarBounds
open Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBounds
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest

universe u v

variable {B : Type u} {K : Type v}
variable [Fintype B] [DecidableEq B] [Fintype K] [DecidableEq K]
variable (G : SimpleGraph B) [DecidableRel G.Adj]
variable (cluster : K → Finset B) (epsilon density : ℚ)
variable [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
variable {L : Finset K} {miss : ℕ}
variable {C67 : Claim67Certificate
  (regularityReducedGraph G cluster epsilon density) L miss}

/-- Every literal rich whole slot has the common cluster size. -/
theorem card_containmentWhole_eq
    (Aroot Broot : K) (C : Finset K) (m : ℕ)
    (hclusterCard : ∀ x, #(cluster x) = m)
    (slot : RootSlot (Fin C.card) (MatchingEdge C67.M)) :
    #(containmentWhole G cluster epsilon density Aroot Broot C slot) = m := by
  rcases slot with side | clusterOrEdge
  · fin_cases side
    · simpa [containmentWhole, slotWhole] using hclusterCard Aroot
    · simpa [containmentWhole, slotWhole] using hclusterCard Broot
  · rcases clusterOrEdge with C0 | edgeSide
    · simpa [containmentWhole, slotWhole, indexedCluster] using
        hclusterCard (finsetValue C C0)
    · rcases edgeSide with ⟨e, side⟩
      simpa [containmentWhole, slotWhole] using
        hclusterCard (matchingEdgeEndpoint e.1 side)

/-- Coarse direct-child count and the common cluster size imply the rich
direct-root Hall record. -/
theorem richDirectHallBound
    {s : ℕ}
    (F : HierarchicalSegmentForest 1 s)
    (Aroot Broot : K) (C : Finset K)
    (sourceSlot : RootSlot (Fin C.card) (MatchingEdge C67.M))
    (quota m directCountBound : ℕ)
    (hrho : 0 ≤ (epsilon : ℝ))
    (hclusterCard : ∀ x, #(cluster x) = m)
    (hdirect : #(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) ≤
      directCountBound)
    (hscalar : (directCountBound : ℝ) * ((epsilon : ℝ) * m) < quota) :
    DirectHallBound F (epsilon : ℝ)
      (containmentWhole G cluster epsilon density Aroot Broot C sourceSlot)
      quota := by
  exact directHallBoundOfScalar F (epsilon : ℝ)
    (containmentWhole G cluster epsilon density Aroot Broot C sourceSlot)
    quota directCountBound m hrho hdirect
    (card_containmentWhole_eq G cluster epsilon density Aroot Broot C m
      hclusterCard sourceSlot).le hscalar

end Erdos547b.ZhaoClaim616RichCoordinateBudgetFacts

#print axioms Erdos547b.ZhaoClaim616RichCoordinateBudgetFacts.richDirectHallBound
