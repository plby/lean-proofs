/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TerminalOutsideSplice
import ErdosProblems.Erdos599.Blueprint930

/-!
# A concrete 9.30 replacement from a fresh real path

Once the hammock argument supplies a finite real path from a whole-blueprint
terminal to the current slice, meeting the old carrier only at its start,
the remaining 9.30 assertions follow from the literal diamond construction.
In particular, the old-vertex accounting is proved here rather than required
of the path-producing argument.  For this fresh terminal diamond,
`Section9Environment.ofDiamond` also proves full predecessor preservation.
That stronger property is not asserted for imaginary-edge subdivisions.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- A literal diamond is an ordinary extension of its input blueprint. -/
theorem ordinaryExtends_diamond
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish}) :
    W.OrdinaryExtends (W.diamond q hq P hstart hfresh) := by
  constructor
  · change W.vertexSet ⊆ (W.diamond q hq P hstart hfresh).vertexSet
    rw [vertexSet_diamond]
    exact Set.subset_union_left
  · change W.edgeSet ⊆ (W.diamond q hq P hstart hfresh).edgeSet
    rw [edgeSet_diamond]
    exact Set.subset_union_left

/-- A diamond preserves every old real terminal other than the splice
vertex. -/
theorem realTerminals_diamond_preserved
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish}) :
    W.realPart.terminals \ {q.finish} ⊆
      (W.diamond q hq P hstart hfresh).realPart.terminals := by
  intro x hx
  refine ⟨(ordinaryExtends_diamond W q hq P hstart hfresh).1 hx.1.1, ?_⟩
  rintro ⟨y, hy⟩
  have hyEdge : (x, y) ∈ (W.diamond q hq P hstart hfresh).edgeSet := hy.1
  rw [edgeSet_diamond] at hyEdge
  rcases hyEdge with hyW | hyP
  · exact hx.1.2 ⟨y, ⟨hyW, hy.2⟩⟩
  · have hxP : x ∈ P.support := (P.edgeSet_subset_support_prod hyP).1
    exact hx.2 (hfresh ⟨hx.1.1, hxP⟩)

/-- The endpoint of the appended path is a terminal of the resulting
whole blueprint. -/
theorem finish_mem_terminalSet_diamond
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish}) :
    P.finish ∈ (W.diamond q hq P hstart hfresh).terminalSet := by
  let hqfresh : q.support ∩ P.support ⊆ {q.finish} :=
    fun _ hx ↦ hfresh ⟨⟨.inl q, hq, hx.1⟩, hx.2⟩
  refine ⟨.inl (diamondPath q P hstart hqfresh), ?_, ?_⟩
  · exact Or.inr (Set.mem_singleton_iff.mpr rfl)
  · change some (diamondPath q P hstart hqfresh).finish = some P.finish
    rw [diamondPath_finish]

/-- Appending a fresh finite real path gives all concrete coupled
replacement fields, including the old-vertex accounting. -/
def CoupledHammockReplacement.ofFreshPath
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish})
    {T : Set V} (hfinish : P.finish ∈ T) :
    CoupledHammockReplacement W W
      (W.diamond q hq P hstart hfresh) q.finish P.finish T := by
  let U := W.diamond q hq P hstart hfresh
  have hordinary : W.OrdinaryExtends U :=
    ordinaryExtends_diamond W q hq P hstart hfresh
  have hterminal : q.finish ∈ W.terminalSet := ⟨.inl q, hq, rfl⟩
  have hPvertices : P.support ⊆ U.realPart.vertices := by
    change P.support ⊆ U.vertexSet
    rw [vertexSet_diamond]
    exact Set.subset_union_right
  have hPedges : P.edgeSet ⊆ U.realPart.edges := by
    intro e he
    refine ⟨?_, P.edgeSet_subset_adj he⟩
    change e ∈ (W.diamond q hq P hstart hfresh).edgeSet
    rw [edgeSet_diamond]
    exact Or.inr he
  have hpreserves : W.realPart.terminals \ {q.finish} ⊆ U.realPart.terminals :=
    realTerminals_diamond_preserved W q hq P hstart hfresh
  refine {
    isCutAt := isCutAt_self_of_mem_terminalSet W hterminal
    ordinaryExtends := hordinary
    path := P
    path_start := hstart
    path_finish := rfl
    path_vertices := hPvertices
    path_edges := hPedges
    endpoint_mem_slice := hfinish
    endpoint_terminal := finish_mem_terminalSet_diamond W q hq P hstart hfresh
    preserves_other_terminals := hpreserves
    endpoint_fresh := ?_
    real_part_extends := hordinary.realPart_extends
    old_vertices_accounted := ?_ }
  · intro hx
    exact hx.2 (hfresh ⟨hx.1.1, P.finish_mem_support⟩)
  · intro x hxW
    by_cases hxu : x = q.finish
    · subst x
      right
      exact ⟨P, Set.mem_singleton P.finish, hPvertices, hPedges,
        hstart ▸ P.start_mem_support⟩
    · by_cases hxTerminal : x ∈ W.terminalSet
      · left
        left
        refine ⟨?_, hxTerminal⟩
        by_contra hxNewTerminal
        obtain ⟨y, hxy⟩ := U.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
          (hordinary.1 hxW) hxNewTerminal
        change (x, y) ∈ (W.diamond q hq P hstart hfresh).edgeSet at hxy
        rw [edgeSet_diamond] at hxy
        rcases hxy with hxy | hxy
        · exact (mem_familyGraph_terminals_of_mem_terminalSet hxTerminal).2
            ⟨y, hxy⟩
        · exact hxu (Set.mem_singleton_iff.1
            (hfresh ⟨hxW, (P.edgeSet_subset_support_prod hxy).1⟩))
      · left
        right
        obtain ⟨y, hxy⟩ :=
          W.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet hxW hxTerminal
        exact ⟨y, hxy, hordinary.2 hxy⟩

/-- A replacement beginning at the exact one-edge cut also supplies the
replacement relative to the original blueprint.  Only the cut vertex can
have lost an outgoing edge, and the stored real path accounts for it. -/
def CoupledHammockReplacement.afterCut
    {W cut U : LinkageBlueprint Gamma Y kappa} {u z : V} {T : Set V}
    (hcut : W.IsCutAt cut u) (hu : u ∈ W.realPart.terminals)
    (R : CoupledHammockReplacement cut cut U u z T) :
    CoupledHammockReplacement W cut U u z T := by
  have hvertices : cut.vertexSet = W.vertexSet := by
    rcases hcut with ⟨_, rfl⟩ | ⟨v, hv⟩
    · rfl
    · exact hv.vertices_eq
  have hreal : W.realPart.Extends cut.realPart := by
    rcases hcut with ⟨_, rfl⟩ | ⟨v, hv⟩
    · exact FamilyGraph.extends_refl _
    · exact hv.realPart_extends_cut hu
  have hterminals : W.realPart.terminals ⊆ cut.realPart.terminals := by
    rcases hcut with ⟨_, rfl⟩ | ⟨v, hv⟩
    · exact Set.Subset.rfl
    · exact hv.preserves_realTerminals
  refine {
    isCutAt := hcut
    ordinaryExtends := R.ordinaryExtends
    path := R.path
    path_start := R.path_start
    path_finish := R.path_finish
    path_vertices := R.path_vertices
    path_edges := R.path_edges
    endpoint_mem_slice := R.endpoint_mem_slice
    endpoint_terminal := R.endpoint_terminal
    preserves_other_terminals := fun _ hx ↦
      R.preserves_other_terminals ⟨hterminals hx.1, hx.2⟩
    endpoint_fresh := fun hx ↦ R.endpoint_fresh ⟨hterminals hx.1, hx.2⟩
    real_part_extends := FamilyGraph.extends_trans hreal R.real_part_extends
    old_vertices_accounted := ?_ }
  intro x hxW
  by_cases hxu : x = u
  · subst x
    right
    exact ⟨R.path, by simpa only [R.path_finish] using Set.mem_singleton z,
      R.path_vertices, R.path_edges,
      by simpa only [R.path_start] using R.path.start_mem_support⟩
  · have hxCut : x ∈ cut.vertexSet := hvertices.symm ▸ hxW
    rcases R.old_vertices_accounted hxCut with (hxTerm | hxEdge) | hxDone
    · left
      left
      refine ⟨hxTerm.1, ?_⟩
      by_contra hxNotTerminal
      obtain ⟨y, hxy⟩ :=
        W.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet hxW hxNotTerminal
      have hxyCut : (x, y) ∈ cut.edgeSet := by
        rcases hcut with ⟨_, rfl⟩ | ⟨v, hv⟩
        · exact hxy
        · rw [hv.edges_eq]
          exact ⟨hxy, fun heq ↦ hxu (congrArg Prod.fst heq)⟩
      exact (mem_familyGraph_terminals_of_mem_terminalSet hxTerm.2).2
        ⟨y, hxyCut⟩
    · left
      right
      obtain ⟨y, hxyCut, hxyU⟩ := hxEdge
      exact ⟨y, hcut.ordinaryExtends_original.2 hxyCut, hxyU⟩
    · exact Or.inr hxDone

/-- The same concrete finite-path construction handles a real terminal
whose outgoing imaginary edge has first been cut. -/
def CoupledHammockReplacement.ofFreshPathAfterCut
    {W cut : LinkageBlueprint Gamma Y kappa}
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ cut.paths)
    (hcut : W.IsCutAt cut q.finish)
    (hu : q.finish ∈ W.realPart.terminals)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : cut.vertexSet ∩ P.support ⊆ {q.finish})
    {T : Set V} (hfinish : P.finish ∈ T) :
    CoupledHammockReplacement W cut
      (cut.diamond q hq P hstart hfresh) q.finish P.finish T :=
  CoupledHammockReplacement.afterCut hcut hu
    (CoupledHammockReplacement.ofFreshPath cut q hq P hstart hfresh hfinish)

/-- A backward link of an alternating path avoiding all reference
components that meet the old carrier belongs to an entirely fresh reference
component.  One of its two distinct endpoints differs from the initial
vertex, and witnesses the required avoidance. -/
theorem fresh_reference_of_backward_link
    (W : LinkageBlueprint Gamma Y kappa) {u : V}
    (R : InfiniteTrace Gamma.graph)
    (hsafe : IsSafe Y (.infinite R))
    (hcontact : Disjoint ((AltPath.infinite R).vertexSet \ {u})
      (meetingVertices Gamma Y W.vertexSet))
    (i : ℕ) (hdir : (R.link i).direction = .backward) :
    ∃ p ∈ Y, (R.link i).path.support ⊆ p.support ∧
      Disjoint p.support W.vertexSet := by
  classical
  obtain ⟨p, hpY, hsub⟩ := hsafe.isAlternating.2.1 (R.link i) ⟨i, rfl⟩ hdir
  let x := if (R.link i).path.start = u then
    (R.link i).path.finish else (R.link i).path.start
  have hxu : x ≠ u := by
    dsimp only [x]
    split
    · rename_i hstart
      intro hfinish
      exact (R.link i).nontrivial (hstart.trans hfinish.symm)
    · assumption
  have hxLink : x ∈ (R.link i).path.support := by
    dsimp only [x]
    split
    · exact (R.link i).path.finish_mem_support
    · exact (R.link i).path.start_mem_support
  have hxR : x ∈ (AltPath.infinite R).vertexSet :=
    Set.mem_iUnion.2 ⟨i, hxLink⟩
  refine ⟨p, hpY, hsub.1, Set.disjoint_left.2 ?_⟩
  intro w hwp hwW
  have hxMeeting : x ∈ meetingVertices Gamma Y W.vertexSet :=
    support_subset_meetingVertices Gamma Y W.vertexSet hpY
      ⟨w, hwp, hwW⟩ (hsub.1 hxLink)
  exact Set.disjoint_left.1 hcontact ⟨hxR, hxu⟩ hxMeeting

/-- An infinite safe hammock member with contact-carrier avoidance gives
a fresh finite real path to the reference frontier.  Follow its first
forward link and then the forward tail of the fresh reference path met by
its first backward link, erasing any loops in that finite walk. -/
theorem exists_freshPath_of_infinite_contactAvoidance
    (W : LinkageBlueprint Gamma Y kappa) {u : V} {T : Set V}
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hYterminal : Gamma.terminalFrontier Y ⊆ T)
    (huW : u ∈ W.vertexSet)
    (Q : AltPath Gamma.graph) (hsafe : IsSafe Y Q)
    (hinitial : Q.initial = u) (hinfinite : Q.IsInfinite)
    (havoid : Disjoint (Q.vertexSet \ {u}) W.vertexSet)
    (hcontact : Disjoint (Q.vertexSet \ {u})
      (meetingVertices Gamma Y W.vertexSet)) :
    ∃ P : FinitePath Gamma.graph,
      P.start = u ∧ P.finish ∈ T ∧ W.vertexSet ∩ P.support ⊆ {u} := by
  cases Q with
  | trivial x => exact False.elim hinfinite
  | finite F => exact False.elim hinfinite
  | infinite R =>
      have hforward : (R.link 0).direction = .forward := by
        cases hdir : (R.link 0).direction with
        | forward => rfl
        | backward =>
            obtain ⟨p, hpY, hsub, hdisjoint⟩ :=
              fresh_reference_of_backward_link W R hsafe hcontact 0 hdir
            have huLink : u ∈ (R.link 0).path.support := by
              rw [← hinitial]
              exact (R.link 0).entry_mem_support
            exact False.elim (Set.disjoint_left.1 hdisjoint (hsub huLink) huW)
      have hbackward : (R.link 1).direction = .backward := by
        cases hdir : (R.link 1).direction with
        | backward => rfl
        | forward =>
            exact False.elim ((R.alternates 0) (hforward.trans hdir.symm))
      obtain ⟨p, hpY, hsub, hpAvoid⟩ :=
        fresh_reference_of_backward_link W R hsafe hcontact 1 hbackward
      obtain ⟨p, rfl⟩ := hYfinite hpY
      let F := (R.link 0).path
      have hFstart : F.start = u := by
        simpa only [AltPath.initial, InfiniteTrace.initial, Link.entry,
          hforward] using hinitial
      have hFfinish : F.finish ∈ p.support := by
        have hjoin : F.finish = (R.link 1).path.finish := by
          simpa only [Link.exit, Link.entry, hforward, hbackward] using R.joins 0
        rw [hjoin]
        exact hsub (R.link 1).path.finish_mem_support
      let tail := p.suffixFrom F.finish hFfinish
      let tw : Walk Gamma.graph F.finish p.finish :=
        RelationalRoof.castStart Gamma.graph.Adj
          (p.suffixFrom_start F.finish hFfinish) tail.walk
      let joined := F.walk.append tw
      obtain ⟨r, hr⟩ :=
        RelationalRoof.exists_pathTo_support_subset (R := Gamma.graph.Adj) joined
      let P : FinitePath Gamma.graph :=
        { start := F.start, finish := p.finish, walk := r.1, isPath := r.2 }
      refine ⟨P, hFstart, hYterminal ⟨.inl p, hpY, rfl⟩, ?_⟩
      intro x hx
      have hxJoined : x ∈ joined.support := hr hx.2
      rw [Walk.support_append] at hxJoined
      rcases List.mem_append.1 hxJoined with hxF | hxTail
      · by_contra hxu
        have hxQ : x ∈ (AltPath.infinite R).vertexSet :=
          Set.mem_iUnion.2 ⟨0, hxF⟩
        exact Set.disjoint_left.1 havoid ⟨hxQ, hxu⟩ hx.1
      · have hxTail' : x ∈ tail.support := by
          change x ∈ tail.walk.support
          have hcast : tw.support = tail.walk.support :=
            RelationalRoof.support_castStart Gamma.graph.Adj
              (p.suffixFrom_start F.finish hFfinish) tail.walk
          exact hcast ▸ List.mem_of_mem_tail hxTail
        exact False.elim (Set.disjoint_left.1 hpAvoid
          (p.suffixFrom_support_subset F.finish hFfinish hxTail') hx.1)

/-- The terminal-outside-slice branch of 9.30 is constructive when the
finite reference warp ends in the current slice.  A large hammock can avoid
the complete reference components meeting the old blueprint, not only the
old blueprint vertices themselves. -/
theorem terminalOutsideHammockReplacementCompiler_of_reference_frontier
    (hkappa : aleph0 ≤ kappa) (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    {T Z persistent : Set V}
    (hYterminal : Gamma.terminalFrontier Y ⊆ T) :
    TerminalOutsideHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent := by
  intro W u _Q hW hpersistent hu huterm huT
    _hsafe _hinitial _hinfinite _havoid
  have hWcard : #W.vertexSet ≤ kappa :=
    W.mk_vertexSet_le_of_mk_paths_le hkappa hW.card_paths
  have hcontactCard : #(meetingVertices Gamma Y W.vertexSet) ≤ kappa :=
    mk_meetingVertices_le Gamma Y W.vertexSet hYwarp hkappa hWcard
  have hreserved : #(W.vertexSet ∪ meetingVertices Gamma Y W.vertexSet : Set V) ≤
      kappa :=
    (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le hkappa hWcard hcontactCard)
  have hhammock := terminal_outside_slice_has_infinite_hammock hW hpersistent huterm huT
  obtain ⟨Q, hsafe, hinitial, hinfinite, havoid⟩ :=
    exists_safe_infinite_hammock_path_avoiding hhammock hreserved
  have havoidW : Disjoint (Q.vertexSet \ {u}) W.vertexSet :=
    havoid.mono_right Set.subset_union_left
  have hcontact : Disjoint (Q.vertexSet \ {u})
      (meetingVertices Gamma Y W.vertexSet) :=
    havoid.mono_right Set.subset_union_right
  obtain ⟨P, hPstart, hPfinish, hPfresh⟩ :=
    exists_freshPath_of_infinite_contactAvoidance W hYfinite hYterminal
      hu.1 Q hsafe hinitial hinfinite havoidW hcontact
  obtain ⟨q, hq, hqterm⟩ := huterm
  rcases q with q | q
  · have hqfinish : q.finish = u := Option.some.inj hqterm
    have hstart : P.start = q.finish := hPstart.trans hqfinish.symm
    have hfresh : W.vertexSet ∩ P.support ⊆ {q.finish} := by
      simpa only [hqfinish] using hPfresh
    refine ⟨W.diamond q hq P hstart hfresh, P.finish, ?_⟩
    have R := CoupledHammockReplacement.ofFreshPath
      W q hq P hstart hfresh hPfinish
    simpa only [hqfinish] using (Nonempty.intro R)
  · simp at hqterm

#print axioms CoupledHammockReplacement.ofFreshPath
#print axioms CoupledHammockReplacement.ofFreshPathAfterCut
#print axioms exists_freshPath_of_infinite_contactAvoidance
#print axioms terminalOutsideHammockReplacementCompiler_of_reference_frontier

end LinkageBlueprint
end Blueprint
end Erdos599
