/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalOrderedTransaction
import ErdosProblems.Erdos599.GroundingFiniteSourceRoot

/-!
# Last-contact survival in the maximal ordered equal switch

Other active routes are disjoint from every limiting component exposed by a
fixed active route.  The only possible deletions on such a component are
therefore deletions made by the fixed route itself.  On a finite component,
take the suffix beginning at the last vertex of the canonical erased route.
Every edge of that suffix whose tail is strictly after the contact survives
the full simultaneous repaired relation.  Thus only the first outgoing edge
at the last contact can still be diverted by the switch.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection
open GroundingEqualOrderedActiveSelection

variable {kappa : Cardinal.{u}}

private abbrev ActiveWarp
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :=
  maximalOrderedActiveSubwarp hL M

/-- The tail of an edge of a finite path belongs to the support tail unless
it is the path's initial vertex. -/
private theorem finitePath_edge_tail_mem_support_tail_of_ne_start
    (p : FinitePath Gamma.graph) {e : V × V} (he : e ∈ p.edgeSet)
    (hne : e.1 ≠ p.start) :
    e.1 ∈ p.walk.support.tail := by
  have heSupport : e.1 ∈ p.walk.support :=
    (p.edgeSet_subset_support_prod he).1
  apply List.mem_of_ne_of_mem hne
  have hdecomp : p.start :: p.walk.support.tail = p.walk.support := by
    simpa only [p.walk.head_support] using
      (List.cons_head_tail p.walk.support_ne_nil)
  rw [hdecomp]
  exact heSupport

/-- After the last contact with the current erased route, all component
edges except possibly the first outgoing edge survive the final relation.

The statement is deliberately about the literal `lastHit` suffix.  It does
not claim that the first edge survives: a current forward edge may have the
same tail and legitimately divert the switched component there. -/
theorem maximalActive_lastContactSuffix_edge_mem_full_of_tail_ne_start
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M))
    (F : FinitePath Gamma.graph)
    (hFexposed : (Sum.inl F : Gamma.DPath) ∈
      GroundingSimultaneousDecode.exposedLadderPaths
        (EqualInput L hL) p.1)
    (hcontact : F.walk.Meets (canonicalErasedRoute
      (EqualInput L hL) (ActiveWarp hL M) p).vertexSet)
    {e : V × V}
    (heSuffix : e ∈ (F.lastHit
      (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).vertexSet
      hcontact).edgeSet)
    (htail : e.1 ≠ (F.lastHit
      (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).vertexSet
      hcontact).start) :
    e ∈ canonicalErasedRepairedEdges
      (EqualInput L hL) (ActiveWarp hL M) := by
  let C := (canonicalErasedRoute
    (EqualInput L hL) (ActiveWarp hL M) p).vertexSet
  let hmeet : F.walk.Meets C := hcontact
  let S := F.lastHit C hmeet
  change e ∈ S.edgeSet at heSuffix
  change e.1 ≠ S.start at htail
  by_contra heNotFull
  have heF : e ∈ F.edgeSet := F.lastHit_edgeSet_subset C hmeet heSuffix
  let Y : Gamma.DPath := Sum.inl F
  have heY : e ∈ Y.edgeSet := by
    simpa only [Y, Path.edgeSet_finite] using heF
  have hself : ((EqualInput L hL).decodedVertexCarrier p.1 ∩
      Y.support).Nonempty := by
    obtain ⟨x, hxF, hxC⟩ := hcontact
    refine ⟨x, ?_, ?_⟩
    · exact canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
        (EqualInput L hL) (ActiveWarp hL M) p hxC
    · change x ∈ F.support
      exact hxF
  have hkind :=
    maximalActive_exposedParentEdge_currentDeletion_of_not_mem_full
      p Y (by simpa only [Y] using hFexposed) hself heY heNotFull
  have hheadAfter : e.2 ∈ S.walk.support.tail :=
    walk_edge_head_mem_support_tail S.walk heSuffix
  have htailAfter : e.1 ∈ S.walk.support.tail :=
    finitePath_edge_tail_mem_support_tail_of_ne_start S heSuffix htail
  have hheadNotC : e.2 ∉ C :=
    F.lastHit_no_mem_after C hmeet hheadAfter
  have htailNotC : e.1 ∉ C :=
    F.lastHit_no_mem_after C hmeet htailAfter
  rcases hkind with hbackward | ⟨f, hf, htailEq | hheadEq⟩
  · have hEnds := AltPath.directionEdge_endpoints_mem_vertexSet
      (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p)
      hbackward
    exact hheadNotC hEnds.2
  · have hEnds := AltPath.directionEdge_endpoints_mem_vertexSet
      (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p) hf
    exact htailNotC (htailEq.symm ▸ hEnds.1)
  · have hEnds := AltPath.directionEdge_endpoints_mem_vertexSet
      (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p) hf
    exact hheadNotC (hheadEq.symm ▸ hEnds.2)

/-- A rooted last contact has exactly two outcomes in the final relation:
either the finite component terminal is rooted, or the first component edge
is diverted along a current forward edge and that forward head is rooted.

There is no backward or same-head alternative at the last contact, because
the head of the deleted component edge lies strictly after the last route
vertex on the component. -/
theorem maximalActive_lastContact_rooted_terminal_or_forwardHead
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M))
    (F : FinitePath Gamma.graph)
    (hFexposed : (Sum.inl F : Gamma.DPath) ∈
      GroundingSimultaneousDecode.exposedLadderPaths
        (EqualInput L hL) p.1)
    (hcontact : F.walk.Meets (canonicalErasedRoute
      (EqualInput L hL) (ActiveWarp hL M) p).vertexSet)
    (hroot : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (ActiveWarp hL M)) a
        (F.lastHit
          (canonicalErasedRoute
            (EqualInput L hL) (ActiveWarp hL M) p).vertexSet
          hcontact).start) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (EqualInput L hL) (ActiveWarp hL M)) a F.finish) ∨
    (∃ f ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (ActiveWarp hL M)) a f.2) := by
  let C := (canonicalErasedRoute
    (EqualInput L hL) (ActiveWarp hL M) p).vertexSet
  let E := canonicalErasedRepairedEdges
    (EqualInput L hL) (ActiveWarp hL M)
  let S := F.lastHit C hcontact
  obtain ⟨a, ha, haS⟩ := hroot
  by_cases hdeleted : ∃ e ∈ S.edgeSet, e ∉ E
  · obtain ⟨e, heS, heNotE⟩ := hdeleted
    have htailEq : e.1 = S.start := by
      by_contra hne
      exact heNotE
        (maximalActive_lastContactSuffix_edge_mem_full_of_tail_ne_start
          p F hFexposed hcontact heS hne)
    have heF : e ∈ F.edgeSet := F.lastHit_edgeSet_subset C hcontact heS
    let Y : Gamma.DPath := Sum.inl F
    have heY : e ∈ Y.edgeSet := by
      simpa only [Y, Path.edgeSet_finite] using heF
    have hself : ((EqualInput L hL).decodedVertexCarrier p.1 ∩
        Y.support).Nonempty := by
      obtain ⟨x, hxF, hxC⟩ := hcontact
      refine ⟨x, ?_, ?_⟩
      · exact canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
          (EqualInput L hL) (ActiveWarp hL M) p hxC
      · change x ∈ F.support
        exact hxF
    have hkind :=
      maximalActive_exposedParentEdge_currentDeletion_of_not_mem_full
        p Y (by simpa only [Y] using hFexposed) hself heY heNotE
    have hheadAfter : e.2 ∈ S.walk.support.tail :=
      walk_edge_head_mem_support_tail S.walk heS
    have hheadNotC : e.2 ∉ C :=
      F.lastHit_no_mem_after C hcontact hheadAfter
    rcases hkind with hbackward | ⟨f, hf, htail | hhead⟩
    · have hEnds := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p)
        hbackward
      exact False.elim (hheadNotC hEnds.2)
    · right
      refine ⟨f, hf, a, ha, haS.tail ?_⟩
      change (S.start, f.2) ∈ E
      have hstart : S.start = f.1 := htailEq.symm.trans htail
      rw [hstart]
      apply Or.inr
      simp only [canonicalErasedForwardEdges, Set.mem_iUnion]
      exact ⟨p, hf⟩
    · have hEnds := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p) hf
      exact False.elim (hheadNotC (hhead.symm ▸ hEnds.2))
  · left
    refine ⟨a, ha, haS.trans ?_⟩
    have hSEdges : S.edgeSet ⊆ E := by
      intro e he
      by_contra heE
      exact hdeleted ⟨e, he, heE⟩
    have hreach :=
      GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
        S hSEdges S.finish_mem_support
    change Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) S.start S.finish
    exact hreach

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.maximalActive_lastContactSuffix_edge_mem_full_of_tail_ne_start
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_lastContact_rooted_terminal_or_forwardHead
