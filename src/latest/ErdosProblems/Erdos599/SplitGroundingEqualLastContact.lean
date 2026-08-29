/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualActiveIsolation
import ErdosProblems.Erdos599.GroundingFiniteSourceRoot

/-!
# Last-contact survival for the split maximal equal relation

An exposed limiting-ladder component met by one ordered active route is
isolated from every other route.  Consequently, after the last contact with
that route, every later edge of a finite component survives the full repaired
relation.  The first outgoing edge at the contact remains exceptional: it may
be diverted by a forward edge of the same route.

This is the split-legal counterpart of
`maximalActive_lastContactSuffix_edge_mem_full_of_tail_ne_start`.  It does
not assert acyclicity; a last-contact truncation must still handle the first
outgoing diversion explicitly.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection
open GroundingSimultaneousDecode

variable {kappa : Cardinal.{u}}

private abbrev SplitLastContactInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

private abbrev SplitLastContactActiveWarp
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitKappaHindrance)
    {reserved : FinitePath (SplitLastContactInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitLastContactInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {reserved.start})
      (collisionCarrier (SplitLastContactInput L hL) reserved)) :=
  splitMaximalOrderedActiveSubwarp hL M

/-- On an exposed component met by `p`, a missing component edge is deleted
by `p` itself, never by another active route. -/
theorem splitMaximalActive_exposedParentEdge_currentDeletion_of_not_mem_full
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {reserved : FinitePath (SplitLastContactInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitLastContactInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {reserved.start})
      (collisionCarrier (SplitLastContactInput L hL) reserved)}
    (p : WarpPath (SplitLastContactActiveWarp hL M))
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths (SplitLastContactInput L hL) p.1)
    (hself : ((SplitLastContactInput L hL).decodedVertexCarrier p.1 ∩
      Y.support).Nonempty)
    {e : V × V} (heY : e ∈ Y.edgeSet)
    (heNotFull : e ∉ canonicalErasedRepairedEdges
      (SplitLastContactInput L hL) (SplitLastContactActiveWarp hL M)) :
    e ∈ (canonicalErasedRoute
        (SplitLastContactInput L hL)
        (SplitLastContactActiveWarp hL M) p).directionEdges .backward ∨
      ∃ f ∈ (canonicalErasedRoute
        (SplitLastContactInput L hL)
        (SplitLastContactActiveWarp hL M) p).directionEdges .forward,
        e.1 = f.1 ∨ e.2 = f.2 := by
  let I := SplitLastContactInput L hL
  let W := SplitLastContactActiveWarp hL M
  have hYLadder : Y ∈ I.ladder.paths :=
    GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
      (L.splitPopularAuxiliary_proxyPathsFaithful hL) p.1 hY
  have heFamily : e ∈ I.familyEdges := ⟨Y, hYLadder, heY⟩
  by_cases heBackward : e ∈ canonicalErasedBackwardEdges I W
  · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at heBackward
    obtain ⟨r, her⟩ := heBackward
    have hrp : r = p := by
      by_contra hne
      have hdisj :=
        splitMaximalActive_otherRoute_decodedCarrier_disjoint_exposedParent
          p r hne hY hself
      have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute I W r) her
      have hcarrier :=
        canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
          I W r hends.1
      exact Set.disjoint_left.1 hdisj hcarrier
        (Y.edgeSet_subset_support_prod heY).1
    left
    subst r
    exact her
  · have heResidual : e ∈ canonicalErasedResidualEdges I W :=
      ⟨heFamily, heBackward⟩
    have heConflict : e ∈ canonicalErasedForwardConflictEdges I W := by
      by_contra heNotConflict
      exact heNotFull (Or.inl ⟨heResidual, heNotConflict⟩)
    obtain ⟨f, hf, htail | hhead⟩ := heConflict
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
      obtain ⟨r, hfr⟩ := hf
      have hrp : r = p := by
        by_contra hne
        have hdisj :=
          splitMaximalActive_otherRoute_decodedCarrier_disjoint_exposedParent
            p r hne hY hself
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute I W r) hfr
        have hcarrier :=
          canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
            I W r hends.1
        exact Set.disjoint_left.1 hdisj hcarrier
          (htail ▸ (Y.edgeSet_subset_support_prod heY).1)
      right
      subst r
      exact ⟨f, hfr, Or.inl htail⟩
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
      obtain ⟨r, hfr⟩ := hf
      have hrp : r = p := by
        by_contra hne
        have hdisj :=
          splitMaximalActive_otherRoute_decodedCarrier_disjoint_exposedParent
            p r hne hY hself
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute I W r) hfr
        have hcarrier :=
          canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
            I W r hends.2
        exact Set.disjoint_left.1 hdisj hcarrier
          (hhead ▸ (Y.edgeSet_subset_support_prod heY).2)
      right
      subst r
      exact ⟨f, hfr, Or.inr hhead⟩

/-- The tail of an edge of a finite path lies in the strict support tail
unless it is the initial vertex. -/
private theorem split_finitePath_edge_tail_mem_support_tail_of_ne_start
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

/-- Every edge strictly after the last route contact on a finite exposed
component survives the full split repaired relation. -/
theorem splitMaximalActive_lastContactSuffix_edge_mem_full_of_tail_ne_start
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {reserved : FinitePath (SplitLastContactInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitLastContactInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {reserved.start})
      (collisionCarrier (SplitLastContactInput L hL) reserved)}
    (p : WarpPath (SplitLastContactActiveWarp hL M))
    (F : FinitePath Gamma.graph)
    (hFexposed : (Sum.inl F : Gamma.DPath) ∈
      exposedLadderPaths (SplitLastContactInput L hL) p.1)
    (hcontact : F.walk.Meets (canonicalErasedRoute
      (SplitLastContactInput L hL)
      (SplitLastContactActiveWarp hL M) p).vertexSet)
    {e : V × V}
    (heSuffix : e ∈ (F.lastHit
      (canonicalErasedRoute
        (SplitLastContactInput L hL)
        (SplitLastContactActiveWarp hL M) p).vertexSet
      hcontact).edgeSet)
    (htail : e.1 ≠ (F.lastHit
      (canonicalErasedRoute
        (SplitLastContactInput L hL)
        (SplitLastContactActiveWarp hL M) p).vertexSet
      hcontact).start) :
    e ∈ canonicalErasedRepairedEdges
      (SplitLastContactInput L hL) (SplitLastContactActiveWarp hL M) := by
  let C := (canonicalErasedRoute
    (SplitLastContactInput L hL)
    (SplitLastContactActiveWarp hL M) p).vertexSet
  let hmeet : F.walk.Meets C := hcontact
  let S := F.lastHit C hmeet
  change e ∈ S.edgeSet at heSuffix
  change e.1 ≠ S.start at htail
  by_contra heNotFull
  have heF : e ∈ F.edgeSet := F.lastHit_edgeSet_subset C hmeet heSuffix
  let Y : Gamma.DPath := Sum.inl F
  have heY : e ∈ Y.edgeSet := by
    simpa only [Y, Path.edgeSet_finite] using heF
  have hself : ((SplitLastContactInput L hL).decodedVertexCarrier p.1 ∩
      Y.support).Nonempty := by
    obtain ⟨x, hxF, hxC⟩ := hcontact
    refine ⟨x, ?_, ?_⟩
    · exact canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
        (SplitLastContactInput L hL)
        (SplitLastContactActiveWarp hL M) p hxC
    · change x ∈ F.support
      exact hxF
  have hkind :=
    splitMaximalActive_exposedParentEdge_currentDeletion_of_not_mem_full
      p Y (by simpa only [Y] using hFexposed) hself heY heNotFull
  have hheadAfter : e.2 ∈ S.walk.support.tail :=
    walk_edge_head_mem_support_tail S.walk heSuffix
  have htailAfter : e.1 ∈ S.walk.support.tail :=
    split_finitePath_edge_tail_mem_support_tail_of_ne_start S heSuffix htail
  have hheadNotC : e.2 ∉ C :=
    F.lastHit_no_mem_after C hmeet hheadAfter
  have htailNotC : e.1 ∉ C :=
    F.lastHit_no_mem_after C hmeet htailAfter
  rcases hkind with hbackward | ⟨f, hf, htailEq | hheadEq⟩
  · have hends := AltPath.directionEdge_endpoints_mem_vertexSet
      (canonicalErasedRoute
        (SplitLastContactInput L hL)
        (SplitLastContactActiveWarp hL M) p) hbackward
    exact hheadNotC hends.2
  · have hends := AltPath.directionEdge_endpoints_mem_vertexSet
      (canonicalErasedRoute
        (SplitLastContactInput L hL)
        (SplitLastContactActiveWarp hL M) p) hf
    exact htailNotC (htailEq.symm ▸ hends.1)
  · have hends := AltPath.directionEdge_endpoints_mem_vertexSet
      (canonicalErasedRoute
        (SplitLastContactInput L hL)
        (SplitLastContactActiveWarp hL M) p) hf
    exact hheadNotC (hheadEq.symm ▸ hends.2)

/-- A rooted last contact either roots the finite component terminal, or
the exceptional first component edge is diverted along a forward edge of
the same route and the forward head is rooted. -/
theorem splitMaximalActive_lastContact_rooted_terminal_or_forwardHead
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {reserved : FinitePath (SplitLastContactInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitLastContactInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {reserved.start})
      (collisionCarrier (SplitLastContactInput L hL) reserved)}
    (p : WarpPath (SplitLastContactActiveWarp hL M))
    (F : FinitePath Gamma.graph)
    (hFexposed : (Sum.inl F : Gamma.DPath) ∈
      exposedLadderPaths (SplitLastContactInput L hL) p.1)
    (hcontact : F.walk.Meets (canonicalErasedRoute
      (SplitLastContactInput L hL)
      (SplitLastContactActiveWarp hL M) p).vertexSet)
    (hroot : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (SplitLastContactInput L hL) (SplitLastContactActiveWarp hL M)) a
        (F.lastHit
          (canonicalErasedRoute
            (SplitLastContactInput L hL)
            (SplitLastContactActiveWarp hL M) p).vertexSet
          hcontact).start) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
          (SplitLastContactInput L hL) (SplitLastContactActiveWarp hL M))
        a F.finish) ∨
    (∃ f ∈ (canonicalErasedRoute
        (SplitLastContactInput L hL)
        (SplitLastContactActiveWarp hL M) p).directionEdges .forward,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (SplitLastContactInput L hL) (SplitLastContactActiveWarp hL M))
          a f.2) := by
  let C := (canonicalErasedRoute
    (SplitLastContactInput L hL)
    (SplitLastContactActiveWarp hL M) p).vertexSet
  let E := canonicalErasedRepairedEdges
    (SplitLastContactInput L hL) (SplitLastContactActiveWarp hL M)
  let S := F.lastHit C hcontact
  obtain ⟨a, ha, haS⟩ := hroot
  by_cases hdeleted : ∃ e ∈ S.edgeSet, e ∉ E
  · obtain ⟨e, heS, heNotE⟩ := hdeleted
    have htailEq : e.1 = S.start := by
      by_contra hne
      exact heNotE
        (splitMaximalActive_lastContactSuffix_edge_mem_full_of_tail_ne_start
          p F hFexposed hcontact heS hne)
    have heF : e ∈ F.edgeSet := F.lastHit_edgeSet_subset C hcontact heS
    let Y : Gamma.DPath := Sum.inl F
    have heY : e ∈ Y.edgeSet := by
      simpa only [Y, Path.edgeSet_finite] using heF
    have hself : ((SplitLastContactInput L hL).decodedVertexCarrier p.1 ∩
        Y.support).Nonempty := by
      obtain ⟨x, hxF, hxC⟩ := hcontact
      refine ⟨x, ?_, ?_⟩
      · exact canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
          (SplitLastContactInput L hL)
          (SplitLastContactActiveWarp hL M) p hxC
      · change x ∈ F.support
        exact hxF
    have hkind :=
      splitMaximalActive_exposedParentEdge_currentDeletion_of_not_mem_full
        p Y (by simpa only [Y] using hFexposed) hself heY heNotE
    have hheadAfter : e.2 ∈ S.walk.support.tail :=
      walk_edge_head_mem_support_tail S.walk heS
    have hheadNotC : e.2 ∉ C :=
      F.lastHit_no_mem_after C hcontact hheadAfter
    rcases hkind with hbackward | ⟨f, hf, htail | hhead⟩
    · have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute
          (SplitLastContactInput L hL)
          (SplitLastContactActiveWarp hL M) p) hbackward
      exact False.elim (hheadNotC hends.2)
    · right
      refine ⟨f, hf, a, ha, haS.tail ?_⟩
      change (S.start, f.2) ∈ E
      have hstart : S.start = f.1 := htailEq.symm.trans htail
      rw [hstart]
      apply Or.inr
      simp only [canonicalErasedForwardEdges, Set.mem_iUnion]
      exact ⟨p, hf⟩
    · have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute
          (SplitLastContactInput L hL)
          (SplitLastContactActiveWarp hL M) p) hf
      exact False.elim (hheadNotC (hhead.symm ▸ hends.2))
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

#print axioms Erdos599.DWeb.KappaLadder.splitMaximalActive_exposedParentEdge_currentDeletion_of_not_mem_full
#print axioms Erdos599.DWeb.KappaLadder.splitMaximalActive_lastContactSuffix_edge_mem_full_of_tail_ne_start
#print axioms Erdos599.DWeb.KappaLadder.splitMaximalActive_lastContact_rooted_terminal_or_forwardHead
