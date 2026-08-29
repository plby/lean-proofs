/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingActiveRequestRootTransfer
import ErdosProblems.Erdos599.AlternatingDichotomy

/-!
# Prefix alternatives for an unrooted active control at a stopping frontier

For a nonempty stopping frontier, the final forward link of an active request
need not reach its control vertex: it may first meet the frontier.  This file
records the exact replacement for the pre-stopped terminal-root lemma.  An
unrooted active control has an unrooted local anchor, or the source-side prefix
of its last forward link reaches an actual member of the stopping frontier.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingErasedDecode

open _root_.Erdos599.DirectedPath Alternating PopularAuxiliary.Input
open GroundingSimultaneousDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

private theorem finiteForwardPrefix_edges_subset_retainedAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V)
    (c : ActiveControlRequestAt U S K T)
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression U S K
      (chosenRequest c.1)).path.links)
    (hldir : l.direction = .forward)
    (q : FinitePath Gamma.graph)
    (hqStart : q.start = l.path.start)
    (hqEdges : q.edgeSet ⊆ l.path.edgeSet)
    (hnoTail : ∀ e ∈ q.edgeSet, e.1 ∉ T) :
    q.edgeSet ⊆ retainedForwardEdgesAt T
      (selectedErasedCompression U S K (chosenRequest c.1)).path := by
  intro e he
  have heTail : e.1 ∈ q.support :=
    (q.edgeSet_subset_support_prod he).1
  obtain ⟨r, hrStart, hrFinish, _hrSupport, hrEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix
      (.inl q : Gamma.DPath) heTail
  have hreach : Relation.ReflTransGen
      (retainedForwardLinkStepAt T l) r.start r.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ r.edgeSet)
      (p := retainedForwardLinkStepAt T l)
    · intro x y hxy
      have hxyQ : (x, y) ∈ q.edgeSet := hrEdges hxy
      exact ⟨hqEdges hxyQ, hnoTail (x, y) hxyQ⟩
    · exact Walk.reflTransGen_edgeSet r.walk
  have hrStart' : r.start = q.start := by
    simpa [Path.initial] using hrStart
  refine ⟨l, hl, hldir, hqEdges he, hnoTail e he, ?_⟩
  simpa only [hrStart', hrFinish, hqStart] using hreach

/-- Literal first-hit prefix produced when a rooted active forward-link entry
meets `T`.  The certificate retains the path, its switched-edge containment,
and the absence of an earlier `T` vertex, rather than only its endpoint. -/
structure ActiveControlAtStoppedPrefix
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T A : Set V)
    (c : ActiveControlRequestAt U S K T) where
  link : Link Gamma.graph
  link_mem : link ∈ (selectedErasedCompression U S K
    (chosenRequest c.1)).path.links
  direction : link.direction = .forward
  vertex : V
  vertex_mem : vertex ∈ T
  path : FinitePath Gamma.graph
  path_start : path.start = link.path.start
  path_finish : path.finish = vertex
  path_support : path.support ⊆ link.path.support
  path_edges : path.edgeSet ⊆ link.path.edgeSet
  path_switched : path.edgeSet ⊆ erasedSelectedSwitchedEdgesAt U S K T
  no_boundary_before : ∀ x ∈ path.walk.support.dropLast, x ∉ T
  rooted : ∃ a ∈ A, Relation.ReflTransGen
    (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T) a vertex

/-- A rooted active forward-link entry which meets `T` has a literal rooted
first-hit prefix in the At-`T` switched relation. -/
theorem exists_activeControlAtStoppedPrefix
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T A : Set V)
    (c : ActiveControlRequestAt U S K T)
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression U S K
      (chosenRequest c.1)).path.links)
    (hldir : l.direction = .forward)
    (hentry : ∃ a ∈ A, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
      a l.path.start)
    (hmeet : l.path.walk.Meets T) :
    Nonempty (ActiveControlAtStoppedPrefix U S K T A c) := by
  let q := l.path.firstHit T hmeet
  have hqStart : q.start = l.path.start := rfl
  have hqFinish : q.finish ∈ T :=
    l.path.firstHit_finish_mem T hmeet
  have hqEdges : q.edgeSet ⊆ l.path.edgeSet :=
    l.path.firstHit_edgeSet_subset T hmeet
  have hnoTail : ∀ e ∈ q.edgeSet, e.1 ∉ T := by
    intro e he
    exact l.path.firstHit_no_mem_before T hmeet
      (_root_.Erdos599.Alternating.Walk.edge_fst_mem_support_dropLast
        q.walk he)
  have hqRetained : q.edgeSet ⊆ retainedForwardEdgesAt T
      (selectedErasedCompression U S K (chosenRequest c.1)).path :=
    finiteForwardPrefix_edges_subset_retainedAt
      U S K T c l hl hldir q hqStart hqEdges hnoTail
  have hqSwitched : q.edgeSet ⊆ erasedSelectedSwitchedEdgesAt U S K T :=
    hqRetained.trans
      (activeRetainedForwardEdgesAt_subset_switched U S K T c)
  have hqReach : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
      q.start q.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ q.edgeSet)
      (p := fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
    · exact fun _ _ h ↦ hqSwitched h
    · exact Walk.reflTransGen_edgeSet q.walk
  obtain ⟨a, ha, haEntry⟩ := hentry
  exact ⟨{
    link := l
    link_mem := hl
    direction := hldir
    vertex := q.finish
    vertex_mem := hqFinish
    path := q
    path_start := hqStart
    path_finish := rfl
    path_support := l.path.firstHit_support_subset T hmeet
    path_edges := hqEdges
    path_switched := hqSwitched
    no_boundary_before := fun x hx ↦
      l.path.firstHit_no_mem_before T hmeet hx
    rooted := ⟨a, ha,
      haEntry.trans (by simpa only [hqStart] using hqReach)⟩ }⟩

private theorem activeForwardNoHit_reaches_finish
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V)
    (c : ActiveControlRequestAt U S K T)
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression U S K
      (chosenRequest c.1)).path.links)
    (hldir : l.direction = .forward)
    (hnotMeet : ¬ l.path.walk.Meets T) :
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
      l.path.start l.path.finish := by
  have hnoTail : ∀ e ∈ l.path.edgeSet, e.1 ∉ T := by
    intro e he heT
    apply hnotMeet
    exact ⟨e.1, (l.path.edgeSet_subset_support_prod he).1, heT⟩
  have hretained : l.path.edgeSet ⊆ retainedForwardEdgesAt T
      (selectedErasedCompression U S K (chosenRequest c.1)).path :=
    finiteForwardPrefix_edges_subset_retainedAt
      U S K T c l hl hldir l.path rfl (fun _ h ↦ h) hnoTail
  have hswitched : l.path.edgeSet ⊆
      erasedSelectedSwitchedEdgesAt U S K T :=
    hretained.trans
      (activeRetainedForwardEdgesAt_subset_switched U S K T c)
  apply Relation.ReflTransGen.mono
    (r := fun x y ↦ (x, y) ∈ l.path.edgeSet)
    (p := fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
  · exact fun _ _ h ↦ hswitched h
  · exact Walk.reflTransGen_edgeSet l.path.walk

/-- Exact local outcomes for an unrooted active control at `T`.  The first
two constructors retain an unrooted local anchor.  The third is the honest
stopping alternative: a source-side prefix is rooted up to an actual member
of `T`, but need not continue to the control beyond that sink. -/
inductive ActiveControlAtUnrootedPrefixOutcome
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T A : Set V)
    (c : ActiveControlRequestAt U S K T) : Prop
  | initial
      (not_rooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
        a (selectedRequestTrace U S K (chosenRequest c.1)).initial)
  | backwardOwner
      (link : Link Gamma.graph)
      (parent : Gamma.DPath)
      (link_mem : link ∈ (selectedErasedCompression U S K
        (chosenRequest c.1)).path.links)
      (direction : link.direction = .backward)
      (parent_mem : parent ∈ L.ladder.paths)
      (subpath : link.path.IsSubpathOf parent)
      (not_rooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
        a link.path.start)
  | stopped
      (data : ActiveControlAtStoppedPrefix U S K T A c)

/-- An unrooted active control either has an unrooted trace/backward anchor,
or its final forward link is stopped at a rooted member of `T`. -/
theorem activeControlAt_unrooted_prefix_outcome
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T A : Set V)
    (c : ActiveControlRequestAt U S K T)
    (hnotRooted : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
      a c.1) :
    ActiveControlAtUnrootedPrefixOutcome U S K T A c := by
  let r := chosenRequest c.1
  let Tr := selectedRequestTrace U S K r
  let C := selectedErasedCompression U S K r
  have hback : BackwardLinksOn L.ladder.paths C.path :=
    selectedErasedCompression_backwardLinksOn U S K r
  cases hpath : C.path with
  | trivial v =>
      refine ActiveControlAtUnrootedPrefixOutcome.initial ?_
      rintro ⟨a, ha, hareach⟩
      apply hnotRooted
      have hi : v = Tr.initial := by
        simpa only [C, hpath, AltPath.initial] using C.initial_eq
      have ht : v = c.1 := by
        have hterminal : (some v : Option V) = some (requestExit r) := by
          simpa only [C, hpath, AltPath.terminal?] using C.terminal_eq
        have hv : v = requestExit r := Option.some.inj hterminal
        simpa only [r, requestExit_chosenRequest] using hv
      have hit : Tr.initial = c.1 := hi.symm.trans ht
      have hareach' : Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
          a Tr.initial := by
        simpa only [Tr, r] using hareach
      exact ⟨a, ha, hit ▸ hareach'⟩
  | infinite Q =>
      have hfalse : (none : Option V) = some (requestExit r) := by
        simpa only [C, hpath, AltPath.terminal?] using C.terminal_eq
      cases hfalse
  | finite Q =>
      have hbackQ : BackwardLinksOn L.ladder.paths (.finite Q) := by
        simpa only [C, hpath] using hback
      have hterminal : Q.terminal = c.1 := by
        have hterminal' : (some Q.terminal : Option V) =
            some (requestExit r) := by
          simpa only [C, hpath, AltPath.terminal?] using C.terminal_eq
        have hq : Q.terminal = requestExit r := Option.some.inj hterminal'
        simpa only [r, requestExit_chosenRequest] using hq
      cases hlastDir : Q.lastLink.direction with
      | backward =>
          have hmem : Q.lastLink ∈ (AltPath.finite Q).links :=
            Q.lastLink_mem_links
          obtain ⟨parent, hparent, hsub⟩ :=
            hbackQ Q.lastLink hmem hlastDir
          refine ActiveControlAtUnrootedPrefixOutcome.backwardOwner
            Q.lastLink parent ?_ hlastDir hparent hsub ?_
          · change Q.lastLink ∈ C.path.links
            rw [hpath]
            exact hmem
          · rintro ⟨a, ha, hareach⟩
            apply hnotRooted
            have hs : Q.lastLink.path.start = Q.terminal := by
              simp [FiniteTrace.terminal, Link.exit, hlastDir]
            exact ⟨a, ha, by simpa only [hs, hterminal] using hareach⟩
      | forward =>
          have hlastMem : Q.lastLink ∈ (AltPath.finite Q).links :=
            Q.lastLink_mem_links
          have hlastMemC : Q.lastLink ∈ C.path.links := by
            simpa only [hpath] using hlastMem
          have hentryCases := Q.initial_or_backwardOwner_eq_forwardStart
            hbackQ Q.lastLink hlastMem hlastDir
          have finish_eq : Q.lastLink.path.finish = c.1 := by
            have he : Q.lastLink.path.finish = Q.terminal := by
              simp [FiniteTrace.terminal, Link.exit, hlastDir]
            exact he.trans hterminal
          cases hentryCases with
          | inl hinitial =>
              by_cases hentryRoot : ∃ a ∈ A, Relation.ReflTransGen
                  (fun x y ↦
                    (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
                  a Q.lastLink.path.start
              · by_cases hmeet : Q.lastLink.path.walk.Meets T
                · obtain ⟨D⟩ := exists_activeControlAtStoppedPrefix
                    U S K T A c Q.lastLink hlastMemC hlastDir hentryRoot hmeet
                  exact .stopped D
                · exfalso
                  apply hnotRooted
                  obtain ⟨a, ha, haEntry⟩ := hentryRoot
                  exact ⟨a, ha, haEntry.trans (by
                    simpa only [finish_eq] using
                      activeForwardNoHit_reaches_finish
                        U S K T c Q.lastLink hlastMemC hlastDir hmeet)⟩
              · refine ActiveControlAtUnrootedPrefixOutcome.initial ?_
                rintro ⟨a, ha, hareach⟩
                apply hentryRoot
                have hQI : Q.initial = Tr.initial := by
                  simpa only [C, hpath, AltPath.initial] using C.initial_eq
                exact ⟨a, ha, by simpa only [hinitial, hQI] using hareach⟩
          | inr hbackward =>
              obtain ⟨b, hb, hbdir, parent, hparent, hbsub, hbstart⟩ :=
                hbackward
              have hbC : b ∈ C.path.links := by
                simpa only [hpath] using hb
              by_cases hentryRoot : ∃ a ∈ A, Relation.ReflTransGen
                  (fun x y ↦
                    (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
                  a Q.lastLink.path.start
              · by_cases hmeet : Q.lastLink.path.walk.Meets T
                · obtain ⟨D⟩ := exists_activeControlAtStoppedPrefix
                    U S K T A c Q.lastLink hlastMemC hlastDir hentryRoot hmeet
                  exact .stopped D
                · exfalso
                  apply hnotRooted
                  obtain ⟨a, ha, haEntry⟩ := hentryRoot
                  exact ⟨a, ha, haEntry.trans (by
                    simpa only [finish_eq] using
                      activeForwardNoHit_reaches_finish
                        U S K T c Q.lastLink hlastMemC hlastDir hmeet)⟩
              · refine ActiveControlAtUnrootedPrefixOutcome.backwardOwner
                  b parent hbC hbdir hparent hbsub ?_
                rintro ⟨a, ha, hareach⟩
                apply hentryRoot
                exact ⟨a, ha, by simpa only [hbstart] using hareach⟩

end GroundingErasedDecode
end Erdos599

#print axioms Erdos599.GroundingErasedDecode.activeControlAt_unrooted_prefix_outcome
