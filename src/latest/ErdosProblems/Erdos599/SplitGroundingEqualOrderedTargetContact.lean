/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualOrderedRooting

/-!
# Target-component contact at the ordered split switch

The repaired relation of lower-index routes roots the current route initial
and every grounded backward owner.  Adding the current forward edges lets
the strict-collision theorem stop at a rooted point of the route's own
target component.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating Stationary

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}

private abbrev SplitOrderedContactInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

namespace SplitReservedStationaryEqualSelection

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {P : Popular.XSWarp
    (SplitOrderedContactInput L hL).lambda
    (SplitOrderedContactInput L hL).lambda.target}

/-- Edges available while inserting one strict route in source-index order. -/
def strictRouteReachabilityEdges
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (q : WarpPath S.strictRoutes) : Set (V × V) :=
  canonicalErasedRepairedEdges
      (SplitOrderedContactInput L hL)
      (S.strictRoutesBeforeIndex
        (warpPathIndex (L.splitPopularAuxiliaryIndexed hL)
          S.strictRoutes q)) ∪
    (canonicalErasedRoute
      (SplitOrderedContactInput L hL)
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp S.routes)
      ⟨q.1, S.strictRoutes_subset_equalRoutes q.2⟩).directionEdges .forward

theorem strictRouteReachabilityEdges_subset_adj
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (q : WarpPath S.strictRoutes) :
    S.strictRouteReachabilityEdges q ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  rintro e (he | he)
  · exact S.strictRoutesBeforeIndex_repaired_subset_adj
      (warpPathIndex (L.splitPopularAuxiliaryIndexed hL)
        S.strictRoutes q) he
  · simp only [AltPath.directionEdges, Set.mem_iUnion] at he
    obtain ⟨l, _hl, _hd, hel⟩ := he
    exact l.path.edgeSet_subset_adj hel

/-- At its ordered switch, a strict route reaches a source-rooted point of
its own equal target component. -/
theorem strictRoute_exists_sourceRooted_targetComponentContact_atSwitch
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (q : WarpPath S.strictRoutes)
    (R : L.SplitCanonicalErasedRouteRootPrefix hL S.strictRoutes q)
    (T : L.SplitEqualTargetComponent hL S.routes q.1
      (S.strictRoutes_subset_equalRoutes q.2)) :
    ∃ x ∈ T.component.support, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ S.strictRouteReachabilityEdges q) a x := by
  let E := S.strictRouteReachabilityEdges q
  have hinitial : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a
        (canonicalErasedRoute
          (SplitOrderedContactInput L hL)
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp S.routes)
          ⟨q.1, S.strictRoutes_subset_equalRoutes q.2⟩).initial := by
    obtain ⟨a, ha, hareach⟩ :=
      S.strictRoute_initial_sourceRooted_beforeIndex q R
    refine ⟨a, ha, Relation.ReflTransGen.mono ?_ _ _ hareach⟩
    intro u v huv
    exact Or.inl huv
  have hforward :
      (canonicalErasedRoute
        (SplitOrderedContactInput L hL)
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp S.routes)
        ⟨q.1, S.strictRoutes_subset_equalRoutes q.2⟩).directionEdges
          .forward ⊆ E := by
    intro e he
    exact Or.inr he
  have hgrounded : ∀ (b : Link Gamma.graph),
      b ∈ (canonicalErasedRoute
        (SplitOrderedContactInput L hL)
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp S.routes)
        ⟨q.1, S.strictRoutes_subset_equalRoutes q.2⟩).links →
      b.direction = .backward →
      ∀ (parent : Gamma.DPath), parent ∈ L.limitWarp →
      parent.initial ∈ Gamma.source → b.path.IsSubpathOf parent →
        ∃ a ∈ Gamma.source,
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
            a b.path.start := by
    intro b hb hbdir parent hparent hparentSource hsub
    obtain ⟨a, ha, hareach⟩ :=
      S.strictBackwardOwner_start_sourceRooted_beforeIndex q b
        hb hbdir parent (by
          simpa only [KappaLadder.splitPopularAuxiliaryInput] using hparent)
        hparentSource hsub
    refine ⟨a, ha, Relation.ReflTransGen.mono ?_ _ _ hareach⟩
    intro u v huv
    exact Or.inl huv
  exact L.splitStrictCollisionFree_equalSubwarp_exists_sourceRooted_targetComponentContact
    hL S.routes q (S.strictRoutes_targetPure q.1 q.2) T
    hinitial hforward hgrounded

end SplitReservedStationaryEqualSelection
end DWeb.KappaLadder
end Erdos599
