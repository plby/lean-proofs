/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureOldRoofIncidence

/-!
# Forward incidence at actual shortcut contacts

At a noninitial closed vertex of an actual compressed assignment the
preceding raw edge cannot be backward, since all backward links avoid the
closed set.  Thus every shortcut head has a literal incoming forward edge
in the same assigned route.  This retains the side of the corresponding
occurrence before the shortcut replaces the intervening route segment.
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

/-- Coordinate-free forward incidence at a closed noninitial vertex. -/
theorem assigned_closed_noninitial_hasIncoming_forward
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    {x : V}
    (hxTrace : x ∈
      (A.assignment.produced.bracket.assignment.assigned s).vertexSet)
    (hxX : x ∈ Rlimit.closedSet)
    (hxInitial : x ≠
      (A.assignment.produced.bracket.assignment.assigned s).initial) :
    ∃ a, (a, x) ∈
      (A.assignment.produced.bracket.assignment.assigned s).directionEdges
        .forward := by
  cases A.compressor s with
  | trivial w hQ =>
      have hxw : x = w := by
        rw [hQ] at hxTrace
        simpa [AltPath.vertexSet] using hxTrace
      exact False.elim (hxInitial (by rw [hQ, hxw]; rfl))
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
      have hvn : S.vertex n = x := by
        exact S.toFiniteRunWalk.vertex_vertexPosition x hxFinite
      have hnpos : 0 < n := by
        by_contra hnpos
        have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
        apply hxInitial
        rw [hQ]
        calc
          x = S.vertex n := hvn.symm
          _ = S.vertex 0 := congrArg S.vertex hnzero
          _ = (AltPath.finite
              S.toFiniteRunWalk.toFiniteTrace).initial :=
            S.toFiniteRunWalk.toFiniteTrace_initial.symm
      let k : Fin S.lastEdge := ⟨n - 1, by omega⟩
      have hkn : k.1 + 1 = n := by
        dsimp [k]
        omega
      have hbackwardOff : ∀ l ∈ (AltPath.finite
          S.toFiniteRunWalk.toFiniteTrace).links,
          l.direction = .backward → Disjoint l.path.support Rlimit.closedSet := by
        intro l hl hdir
        apply A.toPostClosureProducedAssignment
          |>.assigned_backwardLink_disjoint_closedSet s l
        · rw [hQ]
          exact hl
        · exact hdir
      have hkX : S.vertex (k.1 + 1) ∈ Rlimit.closedSet := by
        rw [hkn, hvn]
        exact hxX
      have hcolour : S.colour k = .forward :=
        S.colour_eq_forward_of_next_vertex_mem Rlimit.closedSet
          hbackwardOff k hkX
      have hraw := S.rawEdge_mem_directionEdges k
      rw [hcolour] at hraw
      refine ⟨S.vertex k.1, ?_⟩
      rw [hQ]
      simpa only [RunCompressor.FiniteInput.rawEdge, hcolour, hkn, hvn]
        using hraw
  | infinite S hchange hQ =>
      have hxTrace' : x ∈ (S.toInfiniteRunWalk hchange).toInfiniteTrace.vertexSet := by
        rwa [hQ] at hxTrace
      rw [S.toInfiniteTrace_vertexSet hchange] at hxTrace'
      obtain ⟨n, hvn⟩ := hxTrace'
      have hnpos : 0 < n := by
        by_contra hnpos
        have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
        apply hxInitial
        rw [hQ]
        calc
          x = S.vertex n := hvn.symm
          _ = S.vertex 0 := congrArg S.vertex hnzero
          _ = (AltPath.infinite
              (S.toInfiniteRunWalk hchange).toInfiniteTrace).initial :=
            (S.toInfiniteRunWalk hchange).toInfiniteTrace_initial.symm
      let k := n - 1
      have hkn : k + 1 = n := by
        dsimp [k]
        omega
      have hbackwardOff : ∀ l ∈ (AltPath.infinite
          (S.toInfiniteRunWalk hchange).toInfiniteTrace).links,
          l.direction = .backward → Disjoint l.path.support Rlimit.closedSet := by
        intro l hl hdir
        apply A.toPostClosureProducedAssignment
          |>.assigned_backwardLink_disjoint_closedSet s l
        · rw [hQ]
          exact hl
        · exact hdir
      have hkX : S.vertex (k + 1) ∈ Rlimit.closedSet := by
        rw [hkn, hvn]
        exact hxX
      have hcolour : S.colour k = .forward :=
        S.colour_eq_forward_of_next_vertex_mem hchange Rlimit.closedSet
          hbackwardOff k hkX
      have hraw := S.rawEdge_mem_directionEdges hchange k
      rw [hcolour] at hraw
      refine ⟨S.vertex k, ?_⟩
      rw [hQ]
      simpa only [RunCompressor.InfiniteInput.rawEdge, hcolour, hkn, hvn]
        using hraw

/-- Every shortcut head of a complete actual segmentation has an incoming
forward edge in its parent assigned trace. -/
theorem segmentation_shortcut_head_hasIncoming_forward
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (S : ClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (A.assignment.produced.bracket.assignment.assigned s)
      Rlimit.closedSet C.persistent)
    (hcontacts : S.contactSet ⊆ Rlimit.closedSet)
    {x y : V} (hxy : (x, y) ∈ S.shortcutEdges) :
    ∃ a, (a, y) ∈
      (A.assignment.produced.bracket.assignment.assigned s).directionEdges
        .forward := by
  apply A.assigned_closed_noninitial_hasIncoming_forward s
  · exact S.contactSet_subset_vertexSet (S.endpoints_mem_contactSet hxy).2
  · exact hcontacts (S.endpoints_mem_contactSet hxy).2
  · exact S.shortcut_head_ne_initial hxy

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.segmentation_shortcut_head_hasIncoming_forward
