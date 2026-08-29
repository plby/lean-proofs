/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalRouteRoot
import ErdosProblems.Erdos599.GroundingEqualCollisionBoundaryOwners
import ErdosProblems.Erdos599.SimultaneousAssignment
import ErdosProblems.Erdos599.CountableAssignment

/-!
# A well-founded collision forest for a maximal equal family

For an arbitrary decoded equal-route family, assign to each route `q` the
least source-index route whose *actual canonical erased route* meets the
grounded parent from which `q` starts.  The owner always exists because `q`
itself meets that parent at its canonical initial vertex.  Before the owner
is inserted, the entire finite source prefix of `q` survives.

Unlike the stationary ordered-avoidance selector, a maximal closure may
have a genuinely earlier owner.  That branch is retained explicitly: it is
the well-founded absorption edge from `q` to a smaller-index route.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder
namespace GroundingEqualMaximalCollisionForest

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
variable {W : Popular.XSWarp
  (L.popularAuxiliaryInput hL.legal).lambda
  (L.popularAuxiliaryInput hL.legal).lambda.target}

/-- The initial segment of an arbitrary equal-route family below one source
index. -/
def routesBeforeIndex
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (W : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (a : Stationary.Below kappa) :
    Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target where
  paths := {p | ∃ hp : p ∈ W.paths,
    warpPathIndex (L.popularAuxiliaryIndexed hL) W ⟨p, hp⟩ < a}
  disjoint := by
    rintro p ⟨hp, _⟩ q ⟨hq, _⟩ hpq
    exact W.disjoint hp hq hpq
  starts_in_source := by
    rintro p ⟨hp, _⟩
    exact W.starts_in_source hp
  ends_in_target := by
    rintro p ⟨hp, _⟩
    exact W.ends_in_target hp

theorem routesBeforeIndex_paths_subset
    (a : Stationary.Below kappa) :
    (routesBeforeIndex L hL W a).paths ⊆ W.paths := by
  rintro p ⟨hp, _⟩
  exact hp

/-- The least actual-route contact with one grounded source parent. -/
structure FirstActualRootParentCollision
    (q : WarpPath W)
    (R : L.CanonicalErasedRouteRootPrefix hL W q) where
  owner : WarpPath W
  owner_contact :
    ((canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal) W owner).vertexSet ∩
      R.parent.support).Nonempty
  owner_index_le_route :
    warpPathIndex (L.popularAuxiliaryIndexed hL) W owner ≤
      warpPathIndex (L.popularAuxiliaryIndexed hL) W q
  earlier_disjoint : ∀ r : WarpPath W,
    warpPathIndex (L.popularAuxiliaryIndexed hL) W r <
      warpPathIndex (L.popularAuxiliaryIndexed hL) W owner →
    Disjoint
      (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal) W r).vertexSet
      R.parent.support

/-- Every route has a least actual collision owner for its grounded source
parent. -/
theorem exists_firstActualRootParentCollision
    (q : WarpPath W)
    (R : L.CanonicalErasedRouteRootPrefix hL W q) :
    Nonempty (FirstActualRootParentCollision q R) := by
  let J := L.popularAuxiliaryInput hL.legal
  let C : Set (WarpPath W) :=
    {r | ((canonicalErasedRoute J W r).vertexSet ∩
      R.parent.support).Nonempty}
  have hqC : q ∈ C := by
    let x := (canonicalErasedRoute J W q).initial
    refine ⟨x, (canonicalErasedRoute J W q).initial_mem_vertexSet, ?_⟩
    have hfinish : R.path.finish = x := by
      simpa only [x, J] using R.finish_eq
    rw [← hfinish]
    exact R.support_subset R.path.finish_mem_support
  let rank : WarpPath W → Stationary.Below kappa :=
    warpPathIndex (L.popularAuxiliaryIndexed hL) W
  obtain ⟨owner, hownerC, hminimal⟩ :=
    (InvImage.wf rank wellFounded_lt).has_min C ⟨q, hqC⟩
  exact ⟨{
    owner := owner
    owner_contact := hownerC
    owner_index_le_route := le_of_not_gt (hminimal q hqC)
    earlier_disjoint := by
      intro r hr
      rw [Set.disjoint_left]
      intro x hxr hxparent
      exact hminimal r ⟨x, hxr, hxparent⟩ hr }⟩

namespace FirstActualRootParentCollision

/-- A least actual collision is usable without treating an arbitrary
backward-run interior as rooted.  It is either the route initial, an actual
forward-link vertex, or a backward link whose ladder owner is exactly the
grounded parent being protected. -/
theorem owner_contact_provenance
    {q : WarpPath W} {R : L.CanonicalErasedRouteRootPrefix hL W q}
    (C : FirstActualRootParentCollision q R) :
    (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal) W C.owner).initial ∈
          R.parent.support ∨
      (∃ x ∈ (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W C.owner).directionVertices
            .forward,
        x ∈ R.parent.support) ∨
      ∃ l : Link Gamma.graph,
        l ∈ (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W C.owner).links ∧
        l.direction = .backward ∧ l.path.IsSubpathOf R.parent := by
  let J := L.popularAuxiliaryInput hL.legal
  obtain ⟨x, hxroute, hxparent⟩ := C.owner_contact
  rcases AltPath.vertexSet_subset_initial_union_links
      (canonicalErasedRoute J W C.owner) hxroute with hxinitial | hxlink
  · left
    simpa only [Set.mem_singleton_iff] using hxinitial.symm ▸ hxparent
  · simp only [Set.mem_iUnion] at hxlink
    obtain ⟨l, hlroute, hxl⟩ := hxlink
    cases hdir : l.direction with
    | forward =>
        right
        left
        exact ⟨x, Set.mem_iUnion.2 ⟨l,
          Set.mem_iUnion.2 ⟨hlroute,
            Set.mem_iUnion.2 ⟨hdir, hxl⟩⟩⟩, hxparent⟩
    | backward =>
        let D := J.decodeFinitePath C.owner.1
          (W.starts_in_source C.owner.2) (W.ends_in_target C.owner.2)
        have hback : BackwardLinksOn J.ladder.paths
            (canonicalErasedRoute J W C.owner) := by
          change BackwardLinksOn J.ladder.paths D.erasedCompression.path
          exact D.erasedCompression_backwardLinksOn
        obtain ⟨parent, hparent, hsub⟩ := hback l hlroute hdir
        have hRparent : R.parent ∈ J.ladder.paths := by
          simpa only [J, KappaLadder.popularAuxiliaryInput] using
            R.parent_inessential.1
        have hparentEq : parent = R.parent := by
          by_contra hne
          exact Set.disjoint_left.1
            (J.ladder.disjoint hparent hRparent hne)
            (hsub.1 hxl) hxparent
        right
        right
        exact ⟨l, hlroute, hdir, hparentEq ▸ hsub⟩

/-- The actual erased-route contact chosen by the collision forest is
visible in the auxiliary collision hull: some old original-web point on the
protected parent has the selected owner route as collision provenance. -/
theorem exists_oldCollisionProvenance_mem_parent
    {q : WarpPath W} {R : L.CanonicalErasedRouteRootPrefix hL W q}
    (C : FirstActualRootParentCollision q R) :
    ∃ x ∈ R.parent.support,
      OldCollisionProvenance
        (L.popularAuxiliaryInput hL.legal) C.owner.1 x := by
  let J := L.popularAuxiliaryInput hL.legal
  obtain ⟨x, hxroute, hxparent⟩ := C.owner_contact
  have hxcarrier : x ∈ J.decodedVertexCarrier C.owner.1 :=
    canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
      J W C.owner hxroute
  rcases J.mem_old_support_or_exposedLadderPath_of_mem_decodedVertexCarrier
      C.owner.1 (W.starts_in_source C.owner.2) hxcarrier with
      hxold | ⟨Y, hYexposed, hxY⟩
  · exact ⟨x, hxparent, Or.inl ⟨hxold, hxcarrier⟩⟩
  · exact ⟨x, hxparent, Or.inr ⟨Y, hYexposed, hxY⟩⟩

/-- Consequently every grounded source parent of a selected maximal route
meets the corrected original-web boundary.  This is the exact bridge from
the collision forest to the full `BB` coverage problem. -/
theorem exists_mem_parent_mem_targetCollisionCut_BB
    {q : WarpPath W} {R : L.CanonicalErasedRouteRootPrefix hL W q}
    (C : FirstActualRootParentCollision q R) :
    ∃ x ∈ R.parent.support,
      x ∈ GroundingCut.BB (L.popularAuxiliaryInput hL.legal)
        (reservedMaximalTargetCollisionCut
          (L.popularAuxiliaryInput hL.legal) W.paths) := by
  obtain ⟨x, hxparent, hxprov⟩ :=
    C.exists_oldCollisionProvenance_mem_parent
  refine ⟨x, hxparent, Or.inl ?_⟩
  exact (mem_CV_reservedMaximalTargetCollisionCut_iff
    (L.popularAuxiliaryInput hL.legal) W.paths x).2
      (Or.inr ⟨C.owner.1, C.owner.2, hxprov⟩)

/-- The chosen boundary witness can be retained as the *actual* erased-route
contact from which it was constructed.  This is the transaction-level form
needed to absorb a later collision node through its earlier owner. -/
theorem exists_mem_ownerRoute_mem_parent_mem_targetCollisionCut_BB
    {q : WarpPath W} {R : L.CanonicalErasedRouteRootPrefix hL W q}
    (C : FirstActualRootParentCollision q R) :
    ∃ x,
      x ∈ (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal) W C.owner).vertexSet ∧
      x ∈ R.parent.support ∧
      x ∈ GroundingCut.BB (L.popularAuxiliaryInput hL.legal)
        (reservedMaximalTargetCollisionCut
          (L.popularAuxiliaryInput hL.legal) W.paths) := by
  let J := L.popularAuxiliaryInput hL.legal
  obtain ⟨x, hxroute, hxparent⟩ := C.owner_contact
  have hxcarrier : x ∈ J.decodedVertexCarrier C.owner.1 :=
    canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
      J W C.owner hxroute
  rcases J.mem_old_support_or_exposedLadderPath_of_mem_decodedVertexCarrier
      C.owner.1 (W.starts_in_source C.owner.2) hxcarrier with
      hxold | ⟨Y, hYexposed, hxY⟩
  · refine ⟨x, hxroute, hxparent, Or.inl ?_⟩
    exact (mem_CV_reservedMaximalTargetCollisionCut_iff
      J W.paths x).2
        (Or.inr ⟨C.owner.1, C.owner.2,
          Or.inl ⟨hxold, hxcarrier⟩⟩)
  · refine ⟨x, hxroute, hxparent, Or.inl ?_⟩
    exact (mem_CV_reservedMaximalTargetCollisionCut_iff
      J W.paths x).2
        (Or.inr ⟨C.owner.1, C.owner.2,
          Or.inr ⟨Y, hYexposed, hxY⟩⟩)

/-- Ordered form of the actual owner contact.  In the backward-link case we
replace an arbitrary interior contact by the link entry, which still lies on
the protected parent and is the point to which the finite alternating-root
lemma transfers reachability. -/
theorem exists_orderedOwnerContact_mem_parent_mem_targetCollisionCut_BB
    {q : WarpPath W} {R : L.CanonicalErasedRouteRootPrefix hL W q}
    (C : FirstActualRootParentCollision q R) :
    ∃ x,
      x ∈ (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal) W C.owner).vertexSet ∧
      x ∈ R.parent.support ∧
      x ∈ GroundingCut.BB (L.popularAuxiliaryInput hL.legal)
        (reservedMaximalTargetCollisionCut
          (L.popularAuxiliaryInput hL.legal) W.paths) ∧
      (x = (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W C.owner).initial ∨
        x ∈ (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W C.owner).directionVertices
            .forward ∨
        ∃ l : Link Gamma.graph,
          l ∈ (canonicalErasedRoute
            (L.popularAuxiliaryInput hL.legal) W C.owner).links ∧
          l.direction = .backward ∧ l.path.IsSubpathOf R.parent ∧
          x = l.entry) := by
  let J := L.popularAuxiliaryInput hL.legal
  let A := canonicalErasedRoute J W C.owner
  have memBB_of_route {x : V} (hxroute : x ∈ A.vertexSet) :
      x ∈ GroundingCut.BB J
        (reservedMaximalTargetCollisionCut J W.paths) := by
    have hxcarrier : x ∈ J.decodedVertexCarrier C.owner.1 :=
      canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
        J W C.owner hxroute
    rcases J.mem_old_support_or_exposedLadderPath_of_mem_decodedVertexCarrier
        C.owner.1 (W.starts_in_source C.owner.2) hxcarrier with
        hxold | ⟨Y, hYexposed, hxY⟩
    · refine Or.inl <| (mem_CV_reservedMaximalTargetCollisionCut_iff
        J W.paths x).2 ?_
      exact Or.inr ⟨C.owner.1, C.owner.2,
        Or.inl ⟨hxold, hxcarrier⟩⟩
    · refine Or.inl <| (mem_CV_reservedMaximalTargetCollisionCut_iff
        J W.paths x).2 ?_
      exact Or.inr ⟨C.owner.1, C.owner.2,
        Or.inr ⟨Y, hYexposed, hxY⟩⟩
  rcases C.owner_contact_provenance with hinitial | hforward | hbackward
  · refine ⟨A.initial, A.initial_mem_vertexSet, hinitial,
      memBB_of_route A.initial_mem_vertexSet, Or.inl rfl⟩
  · obtain ⟨x, hxforward, hxparent⟩ := hforward
    simp only [AltPath.directionVertices, Set.mem_iUnion] at hxforward
    obtain ⟨l, hl, hldir, hxl⟩ := hxforward
    have hxroute : x ∈ A.vertexSet :=
      A.link_support_subset_vertexSet hl hxl
    refine ⟨x, hxroute, hxparent, memBB_of_route hxroute, Or.inr ?_⟩
    exact Or.inl (by
      simp only [AltPath.directionVertices, Set.mem_iUnion]
      exact ⟨l, hl, hldir, hxl⟩)
  · obtain ⟨l, hl, hldir, hsub⟩ := hbackward
    have hxroute : l.entry ∈ A.vertexSet :=
      A.link_support_subset_vertexSet hl l.entry_mem_support
    refine ⟨l.entry, hxroute, hsub.1 l.entry_mem_support,
      memBB_of_route hxroute, Or.inr <| Or.inr ?_⟩
    exact ⟨l, hl, hldir, hsub, rfl⟩

/-- The finite grounded prefix survives until its first actual-route
collision owner. -/
theorem rootPrefix_edgeSet_subset_repaired_beforeOwner
    {q : WarpPath W} {R : L.CanonicalErasedRouteRootPrefix hL W q}
    (C : FirstActualRootParentCollision q R) :
    R.path.edgeSet ⊆ canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal)
      (routesBeforeIndex L hL W
        (warpPathIndex (L.popularAuxiliaryIndexed hL) W C.owner)) := by
  apply R.path_edgeSet_subset_repaired_of_routeVertices_disjoint_parent
  intro r
  obtain ⟨hr, hrIndex⟩ := r.2
  exact C.earlier_disjoint ⟨r.1, hr⟩ hrIndex

/-- In fact the whole grounded source parent, rather than only the stored
finite route prefix, survives until its first actual-route collision owner.
This lets the collision point itself be rooted before the owner is
processed. -/
theorem rootParent_edgeSet_subset_repaired_beforeOwner
    {q : WarpPath W} {R : L.CanonicalErasedRouteRootPrefix hL W q}
    (C : FirstActualRootParentCollision q R) :
    R.parent.edgeSet ⊆ canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal)
      (routesBeforeIndex L hL W
        (warpPathIndex (L.popularAuxiliaryIndexed hL) W C.owner)) := by
  apply R.parent_edgeSet_subset_repaired_of_routeVertices_disjoint
  intro r
  obtain ⟨hr, hrIndex⟩ := r.2
  exact C.earlier_disjoint ⟨r.1, hr⟩ hrIndex

/-- The corrected collision boundary already contains a point of the
grounded source parent, and that same point is source-rooted strictly before
the least route colliding with the parent is processed.  Retaining the
parent-membership witness is useful when collision stops are composed by
well-founded absorption. -/
theorem exists_mem_parent_sourceRooted_targetCollisionCut_BB_beforeOwner
    {q : WarpPath W} {R : L.CanonicalErasedRouteRootPrefix hL W q}
    (C : FirstActualRootParentCollision q R) :
    ∃ x ∈ GroundingCut.BB (L.popularAuxiliaryInput hL.legal)
        (reservedMaximalTargetCollisionCut
          (L.popularAuxiliaryInput hL.legal) W.paths),
      x ∈ R.parent.support ∧
        ∃ a ∈ Gamma.source,
          Relation.ReflTransGen
            (fun u v ↦ (u, v) ∈ canonicalErasedRepairedEdges
              (L.popularAuxiliaryInput hL.legal)
              (routesBeforeIndex L hL W
                (warpPathIndex
                  (L.popularAuxiliaryIndexed hL) W C.owner))) a x := by
  obtain ⟨x, hxParent, hxBB⟩ :=
    C.exists_mem_parent_mem_targetCollisionCut_BB
  obtain ⟨s, hsStart, hsFinish, _hsSupport, hsEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix R.parent hxParent
  refine ⟨x, hxBB, hxParent, s.start, ?_, ?_⟩
  · simpa only [hsStart] using R.parent_initial_mem_source
  · have hreach :=
      GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
        s (hsEdges.trans C.rootParent_edgeSet_subset_repaired_beforeOwner)
          s.finish_mem_support
    simpa only [hsFinish] using hreach

/-- The parent-free projection of the preceding stopping invariant. -/
theorem exists_sourceRooted_targetCollisionCut_BB_beforeOwner
    {q : WarpPath W} {R : L.CanonicalErasedRouteRootPrefix hL W q}
    (C : FirstActualRootParentCollision q R) :
    ∃ x ∈ GroundingCut.BB (L.popularAuxiliaryInput hL.legal)
        (reservedMaximalTargetCollisionCut
          (L.popularAuxiliaryInput hL.legal) W.paths),
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈ canonicalErasedRepairedEdges
            (L.popularAuxiliaryInput hL.legal)
            (routesBeforeIndex L hL W
              (warpPathIndex
                (L.popularAuxiliaryIndexed hL) W C.owner))) a x := by
  obtain ⟨x, hxBB, _hxParent, hroot⟩ :=
    C.exists_mem_parent_sourceRooted_targetCollisionCut_BB_beforeOwner
  exact ⟨x, hxBB, hroot⟩

/-- Independently of whether the least owner is self or earlier, the route
initial is source-rooted strictly before that owner is processed.  The
earlier-owner branch is the well-founded input to the subsequent absorption
transaction. -/
theorem route_initial_sourceRooted_beforeOwner
    {q : WarpPath W} {R : L.CanonicalErasedRouteRootPrefix hL W q}
    (C : FirstActualRootParentCollision q R) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (L.popularAuxiliaryInput hL.legal)
          (routesBeforeIndex L hL W
            (warpPathIndex
              (L.popularAuxiliaryIndexed hL) W C.owner)))
        a (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W q).initial := by
  exact R.reaches_initial C.rootPrefix_edgeSet_subset_repaired_beforeOwner

/-- The route owner is either the route itself, or has genuinely smaller
source index. -/
theorem owner_eq_route_or_index_lt
    {q : WarpPath W} {R : L.CanonicalErasedRouteRootPrefix hL W q}
    (C : FirstActualRootParentCollision q R) :
    C.owner = q ∨
      warpPathIndex (L.popularAuxiliaryIndexed hL) W C.owner <
        warpPathIndex (L.popularAuxiliaryIndexed hL) W q := by
  by_cases heq : C.owner = q
  · exact Or.inl heq
  · right
    exact lt_of_le_of_ne C.owner_index_le_route (by
      intro hindex
      apply heq
      exact warpPath_eq_of_index_eq
        (L.popularAuxiliaryIndexed hL)
        (L.popularAuxiliaryIndexed_sourceIndexed hL) W hindex)

/-- If the owner is self, the canonical initial of `q` is source-rooted in
the repaired relation immediately before `q`. -/
theorem route_initial_sourceRooted_before_self
    {q : WarpPath W} {R : L.CanonicalErasedRouteRootPrefix hL W q}
    (C : FirstActualRootParentCollision q R) (hself : C.owner = q) :
    ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (L.popularAuxiliaryInput hL.legal)
          (routesBeforeIndex L hL W
            (warpPathIndex (L.popularAuxiliaryIndexed hL) W q)))
        a (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W q).initial := by
  simpa only [hself] using C.route_initial_sourceRooted_beforeOwner

end FirstActualRootParentCollision
end GroundingEqualMaximalCollisionForest
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.exists_firstActualRootParentCollision
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision.owner_contact_provenance
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision.exists_oldCollisionProvenance_mem_parent
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision.exists_mem_parent_mem_targetCollisionCut_BB
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision.exists_mem_ownerRoute_mem_parent_mem_targetCollisionCut_BB
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision.exists_orderedOwnerContact_mem_parent_mem_targetCollisionCut_BB
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision.rootPrefix_edgeSet_subset_repaired_beforeOwner
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision.rootParent_edgeSet_subset_repaired_beforeOwner
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision.exists_mem_parent_sourceRooted_targetCollisionCut_BB_beforeOwner
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision.exists_sourceRooted_targetCollisionCut_BB_beforeOwner
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision.route_initial_sourceRooted_beforeOwner
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision.owner_eq_route_or_index_lt
#print axioms Erdos599.DWeb.KappaLadder.GroundingEqualMaximalCollisionForest.FirstActualRootParentCollision.route_initial_sourceRooted_before_self
