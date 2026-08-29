/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingMacroChain

/-!
# The root of the terminal component of a finite alternating switch

An alternating trace is not itself a directed path in the switched
relation: backward links are deleted rather than traversed backwards.
Nevertheless its terminal has a very small source classification.  If the
last link is backward, the terminal is the ambient start of that backward
link.  If the last link is forward, either it is the only link, or its
predecessor is backward and the predecessor's ambient start is the entry of
the last forward link.

Thus the terminal is reachable through the inserted forward relation either
from the trace initial, or from the ambient start of one of its backward
links.  This is the local root-transfer fact used in Assertion 8.22; the
separate grounding argument only has to root those two kinds of anchors.
-/

noncomputable section

open Set

namespace Erdos599
namespace Alternating

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace FiniteTrace

/-- The edges of a forward link in a finite trace belong to the aggregate
forward edge set of the trace. -/
theorem link_edgeSet_subset_directionEdges_forward
    (Q : FiniteTrace Gamma.graph) (i : Fin (Q.lastIndex + 1))
    (hi : (Q.link i).direction = .forward) :
    (Q.link i).path.edgeSet ⊆
      (AltPath.finite Q).directionEdges .forward := by
  intro e he
  simp only [AltPath.directionEdges, AltPath.links, FiniteTrace.links,
    Set.mem_iUnion, Set.mem_range]
  exact ⟨Q.link i, ⟨i, rfl⟩, hi, he⟩

/-- A forward link gives directed reachability from its traversal entry to
its traversal exit in every relation containing the aggregate forward edge
set. -/
theorem reflTransGen_entry_exit_of_forward
    (Q : FiniteTrace Gamma.graph) (i : Fin (Q.lastIndex + 1))
    (hi : (Q.link i).direction = .forward)
    {E : Set (V × V)}
    (hforward : (AltPath.finite Q).directionEdges .forward ⊆ E) :
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
      (Q.link i).entry (Q.link i).exit := by
  have hwalk : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ (Q.link i).path.edgeSet)
      (Q.link i).path.start (Q.link i).path.finish :=
    Walk.reflTransGen_edgeSet (Q.link i).path.walk
  have hmono : (Q.link i).path.edgeSet ⊆ E :=
    (Q.link_edgeSet_subset_directionEdges_forward i hi).trans hforward
  have hreach := Relation.ReflTransGen.mono
    (r := fun x y ↦ (x, y) ∈ (Q.link i).path.edgeSet)
    (p := fun x y ↦ (x, y) ∈ E)
    (fun _ _ h ↦ hmono h) _ _ hwalk
  simpa [Link.entry, Link.exit, hi] using hreach

/-- A forward link reaches each of its support vertices in every relation
containing the aggregate forward edge set. -/
theorem reflTransGen_entry_vertex_of_forward
    (Q : FiniteTrace Gamma.graph) (i : Fin (Q.lastIndex + 1))
    (hi : (Q.link i).direction = .forward)
    {E : Set (V × V)}
    (hforward : (AltPath.finite Q).directionEdges .forward ⊆ E)
    {x : V} (hx : x ∈ (Q.link i).path.support) :
    Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E)
      (Q.link i).entry x := by
  let p := (Q.link i).path
  let q := p.firstHit {x} ⟨x, hx, Set.mem_singleton x⟩
  have hpE : p.edgeSet ⊆ E :=
    (Q.link_edgeSet_subset_directionEdges_forward i hi).trans hforward
  have hqE : q.edgeSet ⊆ E :=
    (p.firstHit_edgeSet_subset {x} ⟨x, hx, Set.mem_singleton x⟩).trans
      hpE
  have hreach : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ E) q.start q.finish :=
    Relation.ReflTransGen.mono
      (r := fun u v ↦ (u, v) ∈ q.edgeSet)
      (p := fun u v ↦ (u, v) ∈ E)
      (fun _ _ h ↦ hqE h) q.start q.finish
        (Walk.reflTransGen_edgeSet q.walk)
  have hfinish : q.finish = x := by
    simpa only [Set.mem_singleton_iff] using
      p.firstHit_finish_mem {x} ⟨x, hx, Set.mem_singleton x⟩
  have hstart : q.start = p.start := rfl
  simpa only [p, hstart, hfinish, Link.entry, hi] using hreach

/-- The source-side start of a forward link is either the whole trace
initial vertex or the ambient start of its immediately preceding backward
link.  In the latter case the backward link is packaged with its owner in
the reference warp. -/
theorem initial_or_backwardOwner_eq_forwardStart
    (Q : FiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hback : BackwardLinksOn Y (.finite Q))
    (l : Link Gamma.graph) (hl : l ∈ (AltPath.finite Q).links)
    (hldir : l.direction = .forward) :
    l.path.start = Q.initial ∨
      ∃ (b : Link Gamma.graph), b ∈ (AltPath.finite Q).links ∧
        b.direction = .backward ∧
        ∃ parent ∈ Y, b.path.IsSubpathOf parent ∧
          b.path.start = l.path.start := by
  change l ∈ Q.links at hl
  rcases hl with ⟨i, rfl⟩
  cases hi : i.1 with
  | zero =>
      left
      have hizero : i = (0 : Fin (Q.lastIndex + 1)) := by
        apply Fin.ext
        exact hi
      have hdir0 : (Q.link (0 : Fin (Q.lastIndex + 1))).direction =
          .forward := by
        rw [← hizero]
        exact hldir
      rw [hizero]
      change (Q.link (0 : Fin (Q.lastIndex + 1))).path.start =
        (Q.link (0 : Fin (Q.lastIndex + 1))).entry
      simp [Link.entry, hdir0]
  | succ n =>
      have hn : n < Q.lastIndex := by omega
      let j : Fin Q.lastIndex := ⟨n, hn⟩
      let pred : Fin (Q.lastIndex + 1) := Fin.castSucc j
      have hipred : i = j.succ := by
        apply Fin.ext
        change i.1 = n + 1
        exact hi
      have hpredDir : (Q.link pred).direction = .backward := by
        have halt := Q.alternates j
        change (Q.link pred).direction ≠ (Q.link j.succ).direction at halt
        rw [← hipred, hldir] at halt
        cases hp : (Q.link pred).direction with
        | forward => exact False.elim (halt hp)
        | backward => rfl
      have hpredMem : Q.link pred ∈ (AltPath.finite Q).links :=
        ⟨pred, rfl⟩
      obtain ⟨parent, hparent, hsub⟩ :=
        hback (Q.link pred) hpredMem hpredDir
      right
      refine ⟨Q.link pred, hpredMem, hpredDir,
        parent, hparent, hsub, ?_⟩
      calc
        (Q.link pred).path.start = (Q.link pred).exit := by
          simp [Link.exit, hpredDir]
        _ = (Q.link j.succ).entry := Q.joins j
        _ = (Q.link i).entry := by rw [hipred]
        _ = (Q.link i).path.start := by simp [Link.entry, hldir]

/-- Every vertex on a forward link belongs to a directed switched
component whose local root is either the trace initial or the ambient start
of an earlier backward link.  Unlike full `vertexSet` membership, this
statement never treats an interior point of a deleted backward run as
rooted. -/
theorem initial_or_backwardOwner_reaches_forwardVertex
    (Q : FiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hback : BackwardLinksOn Y (.finite Q))
    {E : Set (V × V)}
    (hforward : (AltPath.finite Q).directionEdges .forward ⊆ E)
    {x : V} (hx : x ∈ (AltPath.finite Q).directionVertices .forward) :
    Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) Q.initial x ∨
      ∃ (l : Link Gamma.graph), l ∈ (AltPath.finite Q).links ∧
        l.direction = .backward ∧
        ∃ parent ∈ Y, l.path.IsSubpathOf parent ∧
          Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E)
            l.path.start x := by
  simp only [AltPath.directionVertices, Set.mem_iUnion] at hx
  obtain ⟨l, hl, hldir, hxl⟩ := hx
  change l ∈ Q.links at hl
  rcases hl with ⟨i, rfl⟩
  have hreach := Q.reflTransGen_entry_vertex_of_forward i hldir hforward hxl
  cases hi : i.1 with
  | zero =>
      left
      have hizero : i = ⟨0, Nat.zero_lt_succ Q.lastIndex⟩ := by
        apply Fin.ext
        exact hi
      simpa only [FiniteTrace.initial, FiniteTrace.firstLink, hizero] using
        hreach
  | succ n =>
      have hn : n < Q.lastIndex := by omega
      let j : Fin Q.lastIndex := ⟨n, hn⟩
      let pred : Fin (Q.lastIndex + 1) := Fin.castSucc j
      have hipred : i = j.succ := by
        apply Fin.ext
        change i.1 = n + 1
        exact hi
      have hpredDir : (Q.link pred).direction = .backward := by
        have halt := Q.alternates j
        change (Q.link pred).direction ≠ (Q.link j.succ).direction at halt
        rw [← hipred, hldir] at halt
        cases hp : (Q.link pred).direction with
        | forward => exact False.elim (halt hp)
        | backward => rfl
      have hpredMem : Q.link pred ∈ (AltPath.finite Q).links :=
        ⟨pred, rfl⟩
      obtain ⟨parent, hparent, hsub⟩ :=
        hback (Q.link pred) hpredMem hpredDir
      right
      refine ⟨Q.link pred, hpredMem, hpredDir, parent, hparent, hsub, ?_⟩
      have hjoin : (Q.link pred).path.start = (Q.link i).entry := by
        calc
          (Q.link pred).path.start = (Q.link pred).exit := by
            simp [Link.exit, hpredDir]
          _ = (Q.link j.succ).entry := Q.joins j
          _ = (Q.link i).entry := by rw [hipred]
      simpa only [hjoin] using hreach

/-- If the trace initial and every possible backward-owner anchor are
rooted in `A`, then every actual forward-route vertex is rooted in `A`.
This is the pointwise counterpart of `exists_root_reaching_terminal`. -/
theorem exists_root_reaching_forwardVertex
    (Q : FiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hback : BackwardLinksOn Y (.finite Q))
    {E : Set (V × V)}
    (hforward : (AltPath.finite Q).directionEdges .forward ⊆ E)
    {A : Set V}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a Q.initial)
    (hbackward : ∀ (l : Link Gamma.graph),
      l ∈ (AltPath.finite Q).links → l.direction = .backward →
      ∀ parent ∈ Y, l.path.IsSubpathOf parent →
        ∃ a ∈ A,
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
            a l.path.start)
    {x : V} (hx : x ∈ (AltPath.finite Q).directionVertices .forward) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a x := by
  rcases Q.initial_or_backwardOwner_reaches_forwardVertex
      hback hforward hx with hreach |
      ⟨l, hl, hldir, parent, hparent, hsub, hreach⟩
  · obtain ⟨a, ha, haroot⟩ := hinitial
    exact ⟨a, ha, haroot.trans hreach⟩
  · obtain ⟨a, ha, haroot⟩ :=
      hbackward l hl hldir parent hparent hsub
    exact ⟨a, ha, haroot.trans hreach⟩

/-- The terminal of a finite alternating trace is reachable through its
forward edges either from the trace initial itself or from the ambient
start of a backward link.  The latter link comes with its actual reference
warp owner.

This is deliberately a reachability statement, not a claim that the
alternating trace is a directed path after switching. -/
theorem initial_or_backwardOwner_reaches_terminal
    (Q : FiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hback : BackwardLinksOn Y (.finite Q))
    {E : Set (V × V)}
    (hforward : (AltPath.finite Q).directionEdges .forward ⊆ E) :
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
        Q.initial Q.terminal ∨
      ∃ (l : Link Gamma.graph), l ∈ (AltPath.finite Q).links ∧
        l.direction = .backward ∧
        ∃ parent ∈ Y, l.path.IsSubpathOf parent ∧
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
            l.path.start Q.terminal := by
  cases hlast : Q.lastLink.direction with
  | backward =>
      right
      have hmem : Q.lastLink ∈ (AltPath.finite Q).links := by
        exact Q.lastLink_mem_links
      obtain ⟨parent, hparent, hsub⟩ :=
        hback Q.lastLink hmem hlast
      refine ⟨Q.lastLink, hmem, hlast, parent, hparent, hsub, ?_⟩
      have hterminal : Q.lastLink.path.start = Q.terminal := by
        simp [FiniteTrace.terminal, Link.exit, hlast]
      rw [hterminal]
  | forward =>
      cases hindex : Q.lastIndex with
      | zero =>
          left
          let i : Fin (Q.lastIndex + 1) :=
            ⟨0, by simp [hindex]⟩
          have hilast : Q.link i = Q.lastLink := by
            apply congrArg Q.link
            apply Fin.ext
            simp [i, hindex]
          have hi : (Q.link i).direction = .forward := by
            rw [hilast]
            exact hlast
          have hreach := Q.reflTransGen_entry_exit_of_forward i hi hforward
          have hinitial : (Q.link i).entry = Q.initial := by
            simp [FiniteTrace.initial, FiniteTrace.firstLink, i]
          have hterminal : (Q.link i).exit = Q.terminal := by
            rw [hilast]
            rfl
          simpa [hinitial, hterminal] using hreach
      | succ n =>
          right
          let i : Fin Q.lastIndex := ⟨n, by simp [hindex]⟩
          let pred : Fin (Q.lastIndex + 1) := Fin.castSucc i
          let last : Fin (Q.lastIndex + 1) := i.succ
          have hlastIndex : Q.link last = Q.lastLink := by
            apply congrArg Q.link
            apply Fin.ext
            simp [last, i, hindex]
          have hlastDir : (Q.link last).direction = .forward := by
            rw [hlastIndex]
            exact hlast
          have hpredDir : (Q.link pred).direction = .backward := by
            have halt := Q.alternates i
            change (Q.link pred).direction ≠ (Q.link last).direction at halt
            rw [hlastDir] at halt
            cases hp : (Q.link pred).direction with
            | forward => exact False.elim (halt hp)
            | backward => rfl
          have hpredMem : Q.link pred ∈ (AltPath.finite Q).links := by
            exact ⟨pred, rfl⟩
          obtain ⟨parent, hparent, hsub⟩ :=
            hback (Q.link pred) hpredMem hpredDir
          refine ⟨Q.link pred, hpredMem, hpredDir,
            parent, hparent, hsub, ?_⟩
          have hlastReach :=
            Q.reflTransGen_entry_exit_of_forward last hlastDir hforward
          have hjoin : (Q.link pred).exit = (Q.link last).entry := by
            exact Q.joins i
          have hpredStart : (Q.link pred).path.start =
              (Q.link pred).exit := by
            simp [Link.exit, hpredDir]
          have hterminal : (Q.link last).exit = Q.terminal := by
            rw [hlastIndex]
            rfl
          rw [hpredStart, hjoin]
          rw [← hterminal]
          exact hlastReach

/-- Root every possible local terminal anchor, and the terminal of the
whole finite trace is rooted.  In the grounding application `A` is the
original source with one unused source deleted. -/
theorem exists_root_reaching_terminal
    (Q : FiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hback : BackwardLinksOn Y (.finite Q))
    {E : Set (V × V)}
    (hforward : (AltPath.finite Q).directionEdges .forward ⊆ E)
    {A : Set V}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a Q.initial)
    (hbackward : ∀ (l : Link Gamma.graph),
      l ∈ (AltPath.finite Q).links → l.direction = .backward →
      ∀ parent ∈ Y, l.path.IsSubpathOf parent →
        ∃ a ∈ A,
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
            a l.path.start) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a Q.terminal := by
  rcases Q.initial_or_backwardOwner_reaches_terminal hback hforward with
      htrace | ⟨l, hl, hldir, parent, hparent, hsub, htrace⟩
  · obtain ⟨a, ha, haroot⟩ := hinitial
    exact ⟨a, ha, haroot.trans htrace⟩
  · obtain ⟨a, ha, haroot⟩ :=
      hbackward l hl hldir parent hparent hsub
    exact ⟨a, ha, haroot.trans htrace⟩

/-- In the literal one-trace switch, every forward edge is present.  This
specializes the preceding root transfer to the conventional switched edge
relation. -/
theorem initial_or_backwardOwner_reaches_terminal_switchedEdges
    (Q : FiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hback : BackwardLinksOn Y (.finite Q))
    (hoff : ForwardLinksOff Y (.finite Q)) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ switchedEdges Y (.finite Q))
        Q.initial Q.terminal ∨
      ∃ (l : Link Gamma.graph), l ∈ (AltPath.finite Q).links ∧
        l.direction = .backward ∧
        ∃ parent ∈ Y, l.path.IsSubpathOf parent ∧
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ switchedEdges Y (.finite Q))
            l.path.start Q.terminal := by
  apply Q.initial_or_backwardOwner_reaches_terminal hback
  intro e he
  right
  refine ⟨?_, ?_⟩
  · rw [(AltPath.finite Q).edgeSet_eq_directionEdges_union]
    exact Or.inl he
  · intro heY
    exact Set.disjoint_left.1 hoff.directionEdges_disjoint he heY

end FiniteTrace
end Alternating
end Erdos599
