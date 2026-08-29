/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalChronology

/-!
# Ordered contacts of maximal equal-stage routes

At a compressed backward link there are two different ambient endpoints.
The ambient start of the deleted link is the root of the *following*
switched component and need not yet be grounded.  Its traversal entry is
the useful contact with the owner component: it is either the initial
vertex of the whole alternating route or belongs to the immediately
preceding forward link.

This distinction resolves the local equality case in the ordinal closure.
When a route first meets a hanging component having the same owner rank as
the route, the construction stops at the backward-link entry.  That entry
is already on the rooted side of the route; no false reachability across
the deleted backward link is required.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace Alternating.FiniteTrace

/-- The traversal entry of a backward link is on the rooted side of that
link: it is the whole trace initial, or it lies on the preceding forward
link. -/
theorem backwardLink_entry_eq_initial_or_mem_forwardVertices
    (Q : FiniteTrace Gamma.graph) (l : Link Gamma.graph)
    (hl : l ∈ (AltPath.finite Q).links)
    (hldir : l.direction = .backward) :
    l.entry = Q.initial ∨
      l.entry ∈ (AltPath.finite Q).directionVertices .forward := by
  change l ∈ Q.links at hl
  rcases hl with ⟨i, rfl⟩
  cases hi : i.1 with
  | zero =>
      left
      have hizero : i = (0 : Fin (Q.lastIndex + 1)) := by
        apply Fin.ext
        exact hi
      have hinitial : Q.initial = (Q.link i).entry := by
        rw [hizero]
        rfl
      rw [hinitial]
  | succ n =>
      right
      have hn : n < Q.lastIndex := by omega
      let j : Fin Q.lastIndex := ⟨n, hn⟩
      let pred : Fin (Q.lastIndex + 1) := Fin.castSucc j
      have hipred : i = j.succ := by
        apply Fin.ext
        change i.1 = n + 1
        exact hi
      have hpredDir : (Q.link pred).direction = .forward := by
        have halt := Q.alternates j
        change (Q.link pred).direction ≠
          (Q.link j.succ).direction at halt
        rw [← hipred, hldir] at halt
        cases hp : (Q.link pred).direction with
        | forward => rfl
        | backward => exact False.elim (halt hp)
      have hentry : (Q.link i).entry = (Q.link pred).exit := by
        rw [hipred]
        exact (Q.joins j).symm
      simp only [AltPath.directionVertices, Set.mem_iUnion]
      refine ⟨Q.link pred, ⟨pred, rfl⟩, hpredDir, ?_⟩
      rw [hentry, Link.exit]
      simp [hpredDir]

/-- Strong ordered form of the entry-contact classification.  The entry
of a backward link is reached by forward edges either from the trace
initial or from the ambient start of a *strictly earlier* backward link.
The latter is returned with its genuine reference-warp owner. -/
theorem backwardLink_entry_reached_from_initial_or_priorBackward
    (Q : FiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hback : BackwardLinksOn Y (.finite Q))
    (l : Link Gamma.graph) (hl : l ∈ (AltPath.finite Q).links)
    (hldir : l.direction = .backward) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          (AltPath.finite Q).directionEdges .forward)
        Q.initial l.entry ∨
      ∃ (b : Link Gamma.graph),
        b ∈ (AltPath.finite Q).links ∧
        b.direction = .backward ∧
        (∃ parent ∈ Y, b.path.IsSubpathOf parent) ∧
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            (AltPath.finite Q).directionEdges .forward)
          b.path.start l.entry ∧
        ∃ (bi li : Fin (Q.lastIndex + 1)),
          Q.link bi = b ∧ Q.link li = l ∧ bi.1 < li.1 := by
  change l ∈ Q.links at hl
  rcases hl with ⟨i, rfl⟩
  cases hi : i.1 with
  | zero =>
      left
      have hizero : i = (0 : Fin (Q.lastIndex + 1)) := by
        apply Fin.ext
        exact hi
      have hinitial : Q.initial = (Q.link i).entry := by
        rw [hizero]
        rfl
      rw [hinitial]
  | succ n =>
      have hn : n < Q.lastIndex := by omega
      let predShort : Fin Q.lastIndex := ⟨n, hn⟩
      let pred : Fin (Q.lastIndex + 1) := Fin.castSucc predShort
      have hipred : i = predShort.succ := by
        apply Fin.ext
        change i.1 = n + 1
        exact hi
      have hpredDir : (Q.link pred).direction = .forward := by
        have halt := Q.alternates predShort
        change (Q.link pred).direction ≠
          (Q.link predShort.succ).direction at halt
        rw [← hipred, hldir] at halt
        cases hp : (Q.link pred).direction with
        | forward => rfl
        | backward => exact False.elim (halt hp)
      have hreach := Q.reflTransGen_entry_exit_of_forward pred hpredDir
        (Set.Subset.rfl)
      have hfinish : (Q.link pred).exit = (Q.link i).entry := by
        rw [hipred]
        exact Q.joins predShort
      cases hnval : n with
      | zero =>
          left
          have hpredZero : pred = (0 : Fin (Q.lastIndex + 1)) := by
            apply Fin.ext
            exact hnval
          have hinitial : Q.initial = (Q.link pred).entry := by
            rw [hpredZero]
            rfl
          rw [← hfinish]
          rw [hinitial]
          exact hreach
      | succ m =>
          right
          have hm : m < Q.lastIndex := by omega
          let priorShort : Fin Q.lastIndex := ⟨m, hm⟩
          let prior : Fin (Q.lastIndex + 1) := Fin.castSucc priorShort
          have hpredSucc : pred = priorShort.succ := by
            apply Fin.ext
            change n = m + 1
            exact hnval
          have hpriorDir : (Q.link prior).direction = .backward := by
            have halt := Q.alternates priorShort
            change (Q.link prior).direction ≠
              (Q.link priorShort.succ).direction at halt
            rw [← hpredSucc, hpredDir] at halt
            cases hp : (Q.link prior).direction with
            | forward => exact False.elim (halt hp)
            | backward => rfl
          have hpriorMem : Q.link prior ∈
              (AltPath.finite Q).links := ⟨prior, rfl⟩
          obtain ⟨parent, hparent, hsub⟩ :=
            hback (Q.link prior) hpriorMem hpriorDir
          refine ⟨Q.link prior, hpriorMem, hpriorDir,
            ⟨parent, hparent, hsub⟩, ?_, prior, i, rfl, rfl, ?_⟩
          · have hjoin : (Q.link prior).exit =
                (Q.link pred).entry := by
              rw [hpredSucc]
              exact Q.joins priorShort
            have hstart : (Q.link prior).path.start =
                (Q.link prior).exit := by
              simp [Link.exit, hpriorDir]
            rw [hstart, hjoin, ← hfinish]
            exact hreach
          · change m < i.1
            omega

end Alternating.FiniteTrace

namespace DWeb.KappaLadder

variable {kappa : Cardinal.{u}}

/-- A marker which occurs on a final limiting-ladder component is the
initial vertex of that component.  The singleton marker inserted at its
successor stage grows to the final direct limit; disjointness in the final
warp identifies that continuation with the component containing the
marker. -/
theorem IsLegal.initial_eq_of_marker_mem_limitWarp_support
    {L : Gamma.KappaLadder kappa} (hL : L.IsLegal)
    {a : Ladder.Stage kappa} {y : V} (hy : L.marker a = some y)
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp) (hyp : y ∈ p.support) :
    p.initial = y := by
  have htrivialSuccessor : Gamma.trivialPath y ∈ L.successorWarp a :=
    (hL.freshMarkers.2 a y hy).2
  have htrivialStage : Gamma.trivialPath y ∈
      L.warpAt (L.successorStage hL a) := by
    simpa only [L.warpAt_successorStage hL] using htrivialSuccessor
  have hmeet : ((Gamma.trivialPath y).support ∩ p.support).Nonempty := by
    exact ⟨y, by simp, hyp⟩
  have hext : Gamma.Extends (Gamma.trivialPath y) p :=
    hL.extends_limitWarp_of_stage_intersects htrivialStage hp hmeet
  have hinitial := Gamma.extends_initial hext
  simpa using hinitial.symm

/-- Target markers are ordinary ladder markers, so a target marker lying
on a final limiting component owns that component's initial vertex. -/
theorem IsLegal.initial_eq_of_targetMarker_mem_limitWarp_support
    {L : Gamma.KappaLadder kappa} (hL : L.IsLegal)
    {y : V} (hy : y ∈
      (L.popularAuxiliaryInput hL).targetMarkers)
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp) (hyp : y ∈ p.support) :
    p.initial = y := by
  obtain ⟨a, ha⟩ := hy.1
  exact hL.initial_eq_of_marker_mem_limitWarp_support ha hp hyp

open GroundingEqualActiveSelection

/-- Every canonical erased edge is one of the deterministic decoded route
edges of its auxiliary path. -/
theorem canonicalErasedRoute_edgeSet_subset_decodedRouteEdges
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q) :
    (canonicalErasedRoute J Q p).edgeSet ⊆
      J.decodedRouteEdges p.1 := by
  let T := J.decodeFinitePath p.1
    (Q.starts_in_source p.2) (Q.ends_in_target p.2)
  simpa only [canonicalErasedRoute, T] using
    T.erasedCompression_edgeSet_subset

/-- The vertices genuinely traversed by either colour of the canonical
route lie in the narrow decoded incident carrier.  This rules out the
spurious proxy-interior activity admitted by `decodedVertexCarrier`. -/
theorem canonicalErasedRoute_directionVertices_subset_decodedRouteIncidentCarrier
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q)
    (d : Direction) :
    (canonicalErasedRoute J Q p).directionVertices d ⊆
      J.decodedRouteIncidentCarrier p.1 := by
  intro x hx
  simp only [AltPath.directionVertices, Set.mem_iUnion] at hx
  obtain ⟨l, hl, hldir, hxl⟩ := hx
  obtain ⟨e, hel, hxe⟩ :
      ∃ e ∈ l.path.edgeSet, x = e.1 ∨ x = e.2 := by
    by_cases hxfinish : x = l.path.finish
    · have hxstart : x ≠ l.path.start := by
        intro h
        apply l.nontrivial
        exact h.symm.trans hxfinish
      obtain ⟨y, hy⟩ :=
        _root_.Erdos599.Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          l.path hxl hxstart
      exact ⟨(y, x), hy, Or.inr rfl⟩
    · obtain ⟨y, hy⟩ :=
        _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          l.path hxl hxfinish
      exact ⟨(x, y), hy, Or.inl rfl⟩
  have heDir : e ∈
      (canonicalErasedRoute J Q p).directionEdges d := by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, hel⟩
  have heAll : e ∈ (canonicalErasedRoute J Q p).edgeSet := by
    rw [(canonicalErasedRoute J Q p).edgeSet_eq_directionEdges_union]
    cases d with
    | forward => exact Or.inl heDir
    | backward => exact Or.inr heDir
  exact Or.inl ⟨e,
    canonicalErasedRoute_edgeSet_subset_decodedRouteEdges J Q p heAll,
    hxe⟩

/-- Canonical form of the ordered-contact lemma.  Every compressed
backward-link entry is either the decoded route initial or an exact
retained forward-route vertex.  This statement concerns the entry, not the
ambient start of the deleted link. -/
theorem canonicalErasedRoute_backwardLink_entry_eq_initial_or_mem_forwardVertices
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute J Q p).links)
    (hldir : l.direction = .backward) :
    l.entry = (canonicalErasedRoute J Q p).initial ∨
      l.entry ∈
        (canonicalErasedRoute J Q p).directionVertices .forward := by
  cases hroute : canonicalErasedRoute J Q p with
  | trivial v => simp [hroute, AltPath.links] at hl
  | finite F =>
      simpa only [hroute, AltPath.initial] using
        F.backwardLink_entry_eq_initial_or_mem_forwardVertices l
          (by simpa only [hroute] using hl) hldir
  | infinite R =>
      let T := J.decodeFinitePath p.1
        (Q.starts_in_source p.2) (Q.ends_in_target p.2)
      have hterminal := T.erasedCompression.terminal_eq
      have hpath : T.erasedCompression.path = .infinite R := by
        simpa only [canonicalErasedRoute, T] using hroute
      rw [hpath] at hterminal
      simp at hterminal

/-- Ordered reachability form for a canonical route.  A backward entry is
fed only by the route initial or by a strictly earlier backward anchor;
the current deleted link is never used to justify its own entry. -/
theorem canonicalErasedRoute_backwardLink_entry_reached_from_initial_or_priorBackward
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute J Q p).links)
    (hldir : l.direction = .backward) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          (canonicalErasedRoute J Q p).directionEdges .forward)
        (canonicalErasedRoute J Q p).initial l.entry ∨
      ∃ (b : Link Gamma.graph),
        b ∈ (canonicalErasedRoute J Q p).links ∧
        b.direction = .backward ∧
        (∃ parent ∈ J.ladder.paths, b.path.IsSubpathOf parent) ∧
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            (canonicalErasedRoute J Q p).directionEdges .forward)
          b.path.start l.entry ∧
        ∃ (F : FiniteTrace Gamma.graph)
            (hroute : canonicalErasedRoute J Q p = .finite F)
            (bi li : Fin (F.lastIndex + 1)),
          F.link bi = b ∧ F.link li = l ∧ bi.1 < li.1 := by
  cases hroute : canonicalErasedRoute J Q p with
  | trivial v => simp [hroute, AltPath.links] at hl
  | finite F =>
      have hback : BackwardLinksOn J.ladder.paths (.finite F) := by
        let T := J.decodeFinitePath p.1
          (Q.starts_in_source p.2) (Q.ends_in_target p.2)
        have hfull : BackwardLinksOn J.ladder.paths
            (canonicalErasedRoute J Q p) := by
          simpa only [canonicalErasedRoute, T] using
            T.erasedCompression_backwardLinksOn
        simpa only [hroute] using hfull
      rcases F.backwardLink_entry_reached_from_initial_or_priorBackward
          hback l (by simpa only [hroute] using hl) hldir with
          hroot | ⟨b, hb, hbdir, hbowner, hreach, bi, li,
            hbi, hli, hlt⟩
      · left
        simpa only [hroute, AltPath.initial,
          AltPath.directionEdges] using hroot
      · right
        refine ⟨b, ?_, hbdir, hbowner, ?_, F, rfl, bi, li,
          hbi, hli, hlt⟩
        · simpa only [hroute] using hb
        · simpa only [hroute, AltPath.directionEdges] using hreach
  | infinite R =>
      let T := J.decodeFinitePath p.1
        (Q.starts_in_source p.2) (Q.ends_in_target p.2)
      have hterminal := T.erasedCompression.terminal_eq
      have hpath : T.erasedCompression.path = .infinite R := by
        simpa only [canonicalErasedRoute, T] using hroute
      rw [hpath] at hterminal
      simp at hterminal

/-- Root transfer to a chosen backward-link entry only needs anchors for
strictly earlier backward links.  This is the ordered stopping interface:
the current deleted link, and every later link, are irrelevant. -/
theorem canonicalErasedRoute_backwardLink_entry_rooted_of_priorBackward
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute J Q p).links)
    (hldir : l.direction = .backward)
    {A : Set V} {E : Set (V × V)}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (canonicalErasedRoute J Q p).initial)
    (hforward :
      (canonicalErasedRoute J Q p).directionEdges .forward ⊆ E)
    (hprior : ∀ (b : Link Gamma.graph),
      b ∈ (canonicalErasedRoute J Q p).links →
      b.direction = .backward →
      (∃ parent ∈ J.ladder.paths, b.path.IsSubpathOf parent) →
      ∀ (F : FiniteTrace Gamma.graph)
        (hroute : canonicalErasedRoute J Q p = .finite F)
        (bi li : Fin (F.lastIndex + 1)),
        F.link bi = b → F.link li = l → bi.1 < li.1 →
        ∃ a ∈ A,
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
            a b.path.start) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a l.entry := by
  rcases canonicalErasedRoute_backwardLink_entry_reached_from_initial_or_priorBackward
      J Q p l hl hldir with
      hfromInitial |
        ⟨b, hb, hbdir, hbowner, hfromPrior,
          F, hroute, bi, li, hbi, hli, hlt⟩
  · obtain ⟨a, haA, haInitial⟩ := hinitial
    refine ⟨a, haA, haInitial.trans ?_⟩
    exact Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈
        (canonicalErasedRoute J Q p).directionEdges .forward)
      (p := fun x y ↦ (x, y) ∈ E)
      (fun _ _ h ↦ hforward h) _ _ hfromInitial
  · obtain ⟨a, haA, haPrior⟩ :=
      hprior b hb hbdir hbowner F hroute bi li hbi hli hlt
    refine ⟨a, haA, haPrior.trans ?_⟩
    exact Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈
        (canonicalErasedRoute J Q p).directionEdges .forward)
      (p := fun x y ↦ (x, y) ∈ E)
      (fun _ _ h ↦ hforward h) _ _ hfromPrior

/-- The ordered entry contact of a backward link really lies on its
limiting-ladder owner. -/
theorem canonicalErasedRoute_backwardLink_entry_mem_owner
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q)
    (l : Link Gamma.graph)
    (_hl : l ∈ (canonicalErasedRoute J Q p).links)
    (_hldir : l.direction = .backward)
    (parent : Gamma.DPath) (_hparent : parent ∈ J.ladder.paths)
    (hsub : l.path.IsSubpathOf parent) :
    l.entry ∈ parent.support := by
  exact hsub.1 l.entry_mem_support

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.Alternating.FiniteTrace.backwardLink_entry_eq_initial_or_mem_forwardVertices
#print axioms Erdos599.Alternating.FiniteTrace.backwardLink_entry_reached_from_initial_or_priorBackward
#print axioms Erdos599.DWeb.KappaLadder.IsLegal.initial_eq_of_marker_mem_limitWarp_support
#print axioms Erdos599.DWeb.KappaLadder.canonicalErasedRoute_directionVertices_subset_decodedRouteIncidentCarrier
#print axioms Erdos599.DWeb.KappaLadder.canonicalErasedRoute_backwardLink_entry_eq_initial_or_mem_forwardVertices
#print axioms Erdos599.DWeb.KappaLadder.canonicalErasedRoute_backwardLink_entry_reached_from_initial_or_priorBackward
#print axioms Erdos599.DWeb.KappaLadder.canonicalErasedRoute_backwardLink_entry_rooted_of_priorBackward
