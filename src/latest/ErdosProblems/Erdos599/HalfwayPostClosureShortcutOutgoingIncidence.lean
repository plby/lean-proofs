/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureShortcutForwardIncidence

/-!
# Forward incidence leaving actual shortcut contacts

The tail of an actual shortcut is a closed nonterminal vertex of its parent
compressed route.  Its following raw edge cannot be backward, because every
backward link avoids the closed set.  Hence it has a forward outgoing edge.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- Coordinate-free forward incidence leaving a closed nonterminal vertex. -/
theorem assigned_closed_nonterminal_hasOutgoing_forward
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    {x : V}
    (hxTrace : x ∈
      (A.assignment.produced.bracket.assignment.assigned s).vertexSet)
    (hxX : x ∈ Rlimit.closedSet)
    (hxTerminal :
      (A.assignment.produced.bracket.assignment.assigned s).terminal? ≠
        some x) :
    ∃ b, (x, b) ∈
      (A.assignment.produced.bracket.assignment.assigned s).directionEdges
        .forward := by
  cases A.compressor s with
  | trivial w hQ =>
      have hxw : x = w := by
        rw [hQ] at hxTrace
        simpa [AltPath.vertexSet] using hxTrace
      exact False.elim (hxTerminal (by rw [hQ, hxw]; rfl))
  | finite S hQ =>
      have hxFinite : x ∈
          (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).vertexSet := by
        rw [← hQ]
        exact hxTrace
      let n := S.toFiniteRunWalk.vertexPosition x hxFinite
      have hnle : n ≤ S.lastEdge := by
        have hnle' := S.toFiniteRunWalk.vertexPosition_le_final x hxFinite
        rw [S.finiteWalk_finalPosition] at hnle'
        exact hnle'
      have hvn : S.vertex n = x :=
        S.toFiniteRunWalk.vertex_vertexPosition x hxFinite
      have hnlt : n < S.lastEdge := by
        apply lt_of_le_of_ne hnle
        intro hne
        apply hxTerminal
        rw [hQ]
        simp only [AltPath.terminal?, FiniteRunWalk.toFiniteTrace_terminal,
          Option.some.injEq]
        calc
          S.toFiniteRunWalk.vertex S.toFiniteRunWalk.finalPosition =
              S.toFiniteRunWalk.vertex S.lastEdge :=
            congrArg S.toFiniteRunWalk.vertex S.finiteWalk_finalPosition
          _ = S.vertex S.lastEdge := rfl
          _ = S.vertex n := congrArg S.vertex hne.symm
          _ = x := hvn
      let k : Fin S.lastEdge := ⟨n, hnlt⟩
      have hbackwardOff : ∀ l ∈ (AltPath.finite
          S.toFiniteRunWalk.toFiniteTrace).links,
          l.direction = .backward → Disjoint l.path.support Rlimit.closedSet := by
        intro l hl hdir
        apply A.toPostClosureProducedAssignment
          |>.assigned_backwardLink_disjoint_closedSet s l
        · rw [hQ]
          exact hl
        · exact hdir
      have hkX : S.vertex k.1 ∈ Rlimit.closedSet := by
        change S.vertex n ∈ Rlimit.closedSet
        rw [hvn]
        exact hxX
      have hcolour : S.colour k = .forward :=
        S.colour_eq_forward_of_vertex_mem Rlimit.closedSet
          hbackwardOff k hkX
      have hraw := S.rawEdge_mem_directionEdges k
      rw [hcolour] at hraw
      refine ⟨S.vertex (k.1 + 1), ?_⟩
      rw [hQ]
      have hvk : S.vertex k.1 = x := hvn
      simpa only [RunCompressor.FiniteInput.rawEdge, hcolour, hvk]
        using hraw
  | infinite S hchange hQ =>
      have hxTrace' : x ∈
          (S.toInfiniteRunWalk hchange).toInfiniteTrace.vertexSet := by
        rwa [hQ] at hxTrace
      rw [S.toInfiniteTrace_vertexSet hchange] at hxTrace'
      obtain ⟨n, hvn⟩ := hxTrace'
      have hbackwardOff : ∀ l ∈ (AltPath.infinite
          (S.toInfiniteRunWalk hchange).toInfiniteTrace).links,
          l.direction = .backward → Disjoint l.path.support Rlimit.closedSet := by
        intro l hl hdir
        apply A.toPostClosureProducedAssignment
          |>.assigned_backwardLink_disjoint_closedSet s l
        · rw [hQ]
          exact hl
        · exact hdir
      have hnX : S.vertex n ∈ Rlimit.closedSet := by
        rw [hvn]
        exact hxX
      have hcolour : S.colour n = .forward :=
        S.colour_eq_forward_of_vertex_mem hchange Rlimit.closedSet
          hbackwardOff n hnX
      have hraw := S.rawEdge_mem_directionEdges hchange n
      rw [hcolour] at hraw
      refine ⟨S.vertex (n + 1), ?_⟩
      rw [hQ]
      simpa only [RunCompressor.InfiniteInput.rawEdge, hcolour, hvn]
        using hraw

/-- Every shortcut tail of the chosen actual segmentation has an outgoing
forward edge in its parent assigned trace. -/
theorem actualSegmentation_shortcut_tail_hasOutgoing_forward
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    {x y : V}
    (hxy : (x, y) ∈
      (A.actualClosedClassifiedContactSegmentation s).shortcutEdges) :
    ∃ b, (x, b) ∈
      (A.assignment.produced.bracket.assignment.assigned s).directionEdges
        .forward := by
  apply A.assigned_closed_nonterminal_hasOutgoing_forward s
  · exact (A.actualClosedClassifiedContactSegmentation s)
      |>.contactSet_subset_vertexSet
        ((A.actualClosedClassifiedContactSegmentation s)
          |>.endpoints_mem_contactSet hxy).1
  · exact A.actualClosedClassifiedContactSegmentation_contactSet_subset s
      ((A.actualClosedClassifiedContactSegmentation s)
        |>.endpoints_mem_contactSet hxy).1
  · exact A.actualClosedClassifiedContactSegmentation_shortcut_tail_not_terminal
      s hxy

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.actualSegmentation_shortcut_tail_hasOutgoing_forward
