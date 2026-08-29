/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TwoWarpMatchingProjection

/-!
# Finite prefixes of a two-warp matching component

An internal cut occurrence need not be an unmatched endpoint of its whole
matching component.  This module therefore isolates the exact finite object
obtained by cutting a component between two occurrences: a positive simple
port sequence whose consecutive ports are literal matching steps.  It has no
spurious unmatched-root or maximal-terminal field.

The prefix is compiled by identity contraction, chronological loop erasure,
and maximal-run compression.  Projected-root uniqueness is an explicit input;
in the intended application it follows from cutting at the first later
closed-set contact.
-/

namespace Erdos599
namespace TwoWarpMatchingTraversal

open Set DirectedPath
open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

noncomputable section

/-- A nonempty simple interval of a directed matching-component traversal. -/
structure FinitePortPrefix (W Y : Set Gamma.DPath) (root : V) where
  lastIndex : Nat
  positive : 0 < lastIndex
  port : Fin (lastIndex + 1) → Port V
  starts : port 0 = .inl root
  steps : ∀ i : Fin lastIndex, Step W Y (port i.castSucc) (port i.succ)
  injective : Function.Injective port

namespace FinitePortPrefix

variable {W Y : Set Gamma.DPath} {root : V}

/-- Restrict a finite maximal component to an actual interval of port
occurrences. -/
def ofFiniteTraversalInterval {componentRoot prefixRoot : V}
    (T : FiniteTraversal W Y componentRoot)
    (a b : Nat) (hab : a < b) (hb : b ≤ T.lastIndex)
    (hstart : T.port ⟨a, by omega⟩ = .inl prefixRoot) :
    FinitePortPrefix W Y prefixRoot where
  lastIndex := b - a
  positive := Nat.sub_pos_of_lt hab
  port i := T.port ⟨a + i.1, by omega⟩
  starts := by
    simpa using hstart
  steps := by
    intro i
    let j : Fin T.lastIndex := ⟨a + i.1, by omega⟩
    have hleft :
        (⟨a + i.castSucc.1, by omega⟩ : Fin (T.lastIndex + 1)) =
          j.castSucc := by
      apply Fin.ext
      simp [j]
    have hright :
        (⟨a + i.succ.1, by omega⟩ : Fin (T.lastIndex + 1)) =
          j.succ := by
      apply Fin.ext
      simp [j]
      omega
    change Step W Y (T.port ⟨a + i.castSucc.1, by omega⟩)
      (T.port ⟨a + i.succ.1, by omega⟩)
    rw [hleft, hright]
    exact T.steps j
  injective := by
    intro i j hij
    have hindex :
        (⟨a + i.1, by omega⟩ : Fin (T.lastIndex + 1)) =
          ⟨a + j.1, by omega⟩ := T.injective hij
    apply Fin.ext
    have := congrArg Fin.val hindex
    exact Nat.add_left_cancel this

/-- Restrict an infinite maximal component to an actual bounded interval of
port occurrences. -/
def ofInfiniteTraversalInterval {componentRoot prefixRoot : V}
    (T : InfiniteTraversal W Y componentRoot)
    (a b : Nat) (hab : a < b)
    (hstart : T.port a = .inl prefixRoot) :
    FinitePortPrefix W Y prefixRoot where
  lastIndex := b - a
  positive := Nat.sub_pos_of_lt hab
  port i := T.port (a + i.1)
  starts := by
    simpa using hstart
  steps := by
    intro i
    have hleft : a + i.castSucc.1 = a + i.1 := by simp
    have hright : a + i.succ.1 = a + i.1 + 1 := by
      simp
      omega
    change Step W Y (T.port (a + i.castSucc.1)) (T.port (a + i.succ.1))
    rw [hleft, hright]
    exact T.steps (a + i.1)
  injective := by
    intro i j hij
    have hindex : a + i.1 = a + j.1 := T.injective hij
    exact Fin.ext (Nat.add_left_cancel hindex)

def projectedVertex (P : FinitePortPrefix W Y root)
    (i : Fin (P.lastIndex + 1)) : V :=
  projectPort (P.port i)

@[simp] theorem projectedVertex_zero (P : FinitePortPrefix W Y root) :
    P.projectedVertex 0 = root := by
  simp [projectedVertex, P.starts]

/-- First-return geometry supplies projected-root uniqueness: all strict
interior occurrences lie outside the closed set and the final contact is not
the starting vertex. -/
theorem projectedRoot_unique_of_first_return
    (P : FinitePortPrefix W Y root) {X : Set V}
    (hrootX : root ∈ X)
    (hinterior : ∀ i : Fin (P.lastIndex + 1),
      0 < i.1 → i.1 < P.lastIndex → P.projectedVertex i ∉ X)
    (hterminal : P.projectedVertex
      ⟨P.lastIndex, Nat.lt_succ_self _⟩ ≠ root) :
    ∀ i, P.projectedVertex i = P.projectedVertex 0 → i.1 = 0 := by
  intro i hi
  by_contra hi0
  have hipos : 0 < i.1 := Nat.pos_of_ne_zero hi0
  by_cases hilast : i.1 = P.lastIndex
  · have hieq : i = ⟨P.lastIndex, Nat.lt_succ_self _⟩ := Fin.ext hilast
    apply hterminal
    calc
      P.projectedVertex ⟨P.lastIndex, Nat.lt_succ_self _⟩ =
          P.projectedVertex i := congrArg P.projectedVertex hieq.symm
      _ = P.projectedVertex 0 := hi
      _ = root := P.projectedVertex_zero
  · have hilt : i.1 < P.lastIndex := by omega
    have hiRoot : P.projectedVertex i = root := hi.trans P.projectedVertex_zero
    have hiX : P.projectedVertex i ∈ X := by
      rw [hiRoot]
      exact hrootX
    exact hinterior i hipos hilt hiX

/-- Chronological erasure never retains an identity matching step. -/
theorem finiteLoopIndex_is_actual (P : FinitePortPrefix W Y root)
    {k : Nat} (hk : k < finiteLoopLength P.projectedVertex) :
    P.projectedVertex (finiteLoopIndex P.projectedVertex k) ≠
      P.projectedVertex ⟨(finiteLoopIndex P.projectedVertex k).1 + 1, by
        have := finiteLoopIndex_lt_top_of_lt_length P.projectedVertex hk
        omega⟩ := by
  intro heq
  have hlast := finiteLoopIndex_is_last P.projectedVertex k
    (j := ⟨(finiteLoopIndex P.projectedVertex k).1 + 1, by
      have := finiteLoopIndex_lt_top_of_lt_length P.projectedVertex hk
      omega⟩) heq.symm
  have hle := Fin.mk_le_mk.mp hlast
  omega

noncomputable def retainedColour (P : FinitePortPrefix W Y root)
    (k : Fin (finiteLoopLength P.projectedVertex)) : Direction :=
  match P.port (finiteLoopIndex P.projectedVertex k.1) with
  | .inl _ => .forward
  | .inr _ => .backward

/-- Compile a first-return prefix once its projected root has no later
occurrence inside the prefix. -/
noncomputable def compressorInput (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0) :
    RunCompressor.FiniteInput Gamma.graph where
  lastEdge := finiteLoopLength P.projectedVertex
  lastEdge_pos := finiteLoopLength_pos P.positive P.projectedVertex hrootUnique
  vertex := finiteLoopVertex P.projectedVertex
  vertex_injective_on := fun hi hj h =>
    finiteLoopVertex_injective_on P.projectedVertex hi hj h
  colour := P.retainedColour
  forward_adj := by
    intro k hdir
    let i := finiteLoopIndex P.projectedVertex k.1
    have hi : i.1 < P.lastIndex :=
      finiteLoopIndex_lt_top_of_lt_length P.projectedVertex k.2
    have hactual := P.finiteLoopIndex_is_actual k.2
    let j : Fin P.lastIndex := ⟨i.1, hi⟩
    have hcast : j.castSucc = i := Fin.ext rfl
    have hsucc : j.succ =
        (⟨i.1 + 1, by omega⟩ : Fin (P.lastIndex + 1)) := Fin.ext rfl
    have hstep := P.steps j
    rcases step_of_project_ne hstep hactual with
      ⟨x, y, hleft, hright, hW, _hY⟩ |
      ⟨x, y, hleft, _hright, _hY, _hW⟩
    · rw [hcast] at hleft
      rw [hsucc] at hright
      dsimp [i] at hleft hright
      rcases finiteLoopVertex_succ P.projectedVertex k.2 with ⟨hcur, hnext⟩
      rw [hcur, hnext]
      have hadj := familyEdges_subset_adj W hW
      simpa [projectedVertex, hleft, hright] using hadj
    · exfalso
      rw [hcast] at hleft
      change (match P.port i with
        | .inl _ => Direction.forward
        | .inr _ => Direction.backward) = .forward at hdir
      rw [hleft] at hdir
      contradiction
  backward_adj := by
    intro k hdir
    let i := finiteLoopIndex P.projectedVertex k.1
    have hi : i.1 < P.lastIndex :=
      finiteLoopIndex_lt_top_of_lt_length P.projectedVertex k.2
    have hactual := P.finiteLoopIndex_is_actual k.2
    let j : Fin P.lastIndex := ⟨i.1, hi⟩
    have hcast : j.castSucc = i := Fin.ext rfl
    have hsucc : j.succ =
        (⟨i.1 + 1, by omega⟩ : Fin (P.lastIndex + 1)) := Fin.ext rfl
    have hstep := P.steps j
    rcases step_of_project_ne hstep hactual with
      ⟨x, y, hleft, _hright, _hW, _hY⟩ |
      ⟨x, y, hleft, hright, hY, _hW⟩
    · exfalso
      rw [hcast] at hleft
      change (match P.port i with
        | .inl _ => Direction.forward
        | .inr _ => Direction.backward) = .backward at hdir
      rw [hleft] at hdir
      contradiction
    · rw [hcast] at hleft
      rw [hsucc] at hright
      dsimp [i] at hleft hright
      rcases finiteLoopVertex_succ P.projectedVertex k.2 with ⟨hcur, hnext⟩
      rw [hcur, hnext]
      have hadj := familyEdges_subset_adj Y hY
      simpa [projectedVertex, hleft, hright] using hadj

noncomputable def compiledRunWalk (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0) :
    FiniteRunWalk Gamma.graph :=
  (P.compressorInput hrootUnique).toFiniteRunWalk

/-- Every retained raw edge keeps its exact matching colour and family
membership. -/
theorem compressorInput_edge (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0)
    (k : Fin (P.compressorInput hrootUnique).lastEdge) :
    ((P.compressorInput hrootUnique).colour k = .forward ∧
      ((P.compressorInput hrootUnique).vertex k,
        (P.compressorInput hrootUnique).vertex (k.1 + 1)) ∈ familyEdges W ∧
      ((P.compressorInput hrootUnique).vertex k,
        (P.compressorInput hrootUnique).vertex (k.1 + 1)) ∉ familyEdges Y) ∨
    ((P.compressorInput hrootUnique).colour k = .backward ∧
      ((P.compressorInput hrootUnique).vertex (k.1 + 1),
        (P.compressorInput hrootUnique).vertex k) ∈ familyEdges Y ∧
      ((P.compressorInput hrootUnique).vertex (k.1 + 1),
        (P.compressorInput hrootUnique).vertex k) ∉ familyEdges W) := by
  let i := finiteLoopIndex P.projectedVertex k.1
  have hi : i.1 < P.lastIndex :=
    finiteLoopIndex_lt_top_of_lt_length P.projectedVertex k.2
  have hactual := P.finiteLoopIndex_is_actual k.2
  let j : Fin P.lastIndex := ⟨i.1, hi⟩
  have hcast : j.castSucc = i := Fin.ext rfl
  have hsucc : j.succ =
      (⟨i.1 + 1, by omega⟩ : Fin (P.lastIndex + 1)) := Fin.ext rfl
  have hstep := P.steps j
  rcases step_of_project_ne hstep hactual with
    ⟨x, y, hleft, hright, hW, hY⟩ |
    ⟨x, y, hleft, hright, hY, hW⟩
  · left
    rw [hcast] at hleft
    rw [hsucc] at hright
    dsimp [i] at hleft hright
    rcases finiteLoopVertex_succ P.projectedVertex k.2 with ⟨hcur, hnext⟩
    refine ⟨?_, ?_, ?_⟩
    · change P.retainedColour k = .forward
      simp [retainedColour, hleft]
    · change (finiteLoopVertex P.projectedVertex k.1,
          finiteLoopVertex P.projectedVertex (k.1 + 1)) ∈ familyEdges W
      rw [hcur, hnext]
      simpa [projectedVertex, hleft, hright] using hW
    · change (finiteLoopVertex P.projectedVertex k.1,
          finiteLoopVertex P.projectedVertex (k.1 + 1)) ∉ familyEdges Y
      rw [hcur, hnext]
      simpa [projectedVertex, hleft, hright] using hY
  · right
    rw [hcast] at hleft
    rw [hsucc] at hright
    dsimp [i] at hleft hright
    rcases finiteLoopVertex_succ P.projectedVertex k.2 with ⟨hcur, hnext⟩
    refine ⟨?_, ?_, ?_⟩
    · change P.retainedColour k = .backward
      simp [retainedColour, hleft]
    · change (finiteLoopVertex P.projectedVertex (k.1 + 1),
          finiteLoopVertex P.projectedVertex k.1) ∈ familyEdges Y
      rw [hcur, hnext]
      simpa [projectedVertex, hleft, hright] using hY
    · change (finiteLoopVertex P.projectedVertex (k.1 + 1),
          finiteLoopVertex P.projectedVertex k.1) ∉ familyEdges W
      rw [hcur, hnext]
      simpa [projectedVertex, hleft, hright] using hW

/-- Every forward run of the compiled prefix consists of literal forward-warp
edges and avoids every reference-warp edge. -/
theorem compiledRunWalk_forward_edge_mem
    (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0)
    (i : Fin ((P.compiledRunWalk hrootUnique).lastIndex + 1))
    (hdir : ((P.compiledRunWalk hrootUnique).run i).link.direction =
      .forward) :
    ((P.compiledRunWalk hrootUnique).run i).link.path.edgeSet ⊆
      familyEdges W := by
  let S := P.compressorInput hrootUnique
  change (S.projectedRun (S.runIndex i)).link.path.edgeSet ⊆ familyEdges W
  change (S.projectedRun (S.runIndex i)).link.direction = .forward at hdir
  intro e he
  have hprov := S.projectedRun_edge_provenance (S.runIndex i) he
  rcases hprov with ⟨_hforward, k, hk, rfl⟩ |
      ⟨hbackward, k, hk, rfl⟩
  · have hcolour : S.colour ⟨RunCompressor.runLower S.runs (S.runIndex i) + k,
        by
          exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
            (S.runUpper_le_lastEdge (S.runIndex i))⟩ = .forward := by
      exact (S.colour_run_offset (S.runIndex i) hk).trans
        ((S.projectedRun_direction (S.runIndex i)).symm.trans hdir)
    let r : Fin (P.compressorInput hrootUnique).lastEdge :=
      ⟨RunCompressor.runLower S.runs (S.runIndex i) + k, by
        change RunCompressor.runLower S.runs (S.runIndex i) + k < S.lastEdge
        exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
          (S.runUpper_le_lastEdge (S.runIndex i))⟩
    rcases P.compressorInput_edge hrootUnique r with h | h
    · simpa [S, r] using h.2.1
    · rw [h.1] at hcolour
      contradiction
  · rw [hdir] at hbackward
    contradiction

theorem compiledRunWalk_forward_edge_not_mem_reference
    (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0)
    (i : Fin ((P.compiledRunWalk hrootUnique).lastIndex + 1))
    (hdir : ((P.compiledRunWalk hrootUnique).run i).link.direction =
      .forward) :
    Disjoint (((P.compiledRunWalk hrootUnique).run i).link.path.edgeSet)
      (familyEdges Y) := by
  let S := P.compressorInput hrootUnique
  change Disjoint ((S.projectedRun (S.runIndex i)).link.path.edgeSet)
    (familyEdges Y)
  change (S.projectedRun (S.runIndex i)).link.direction = .forward at hdir
  rw [Set.disjoint_left]
  intro e he hYmem
  have hprov := S.projectedRun_edge_provenance (S.runIndex i) he
  rcases hprov with ⟨_hforward, k, hk, rfl⟩ |
      ⟨hbackward, k, hk, rfl⟩
  · have hcolour : S.colour ⟨RunCompressor.runLower S.runs (S.runIndex i) + k,
        by
          exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
            (S.runUpper_le_lastEdge (S.runIndex i))⟩ = .forward := by
      exact (S.colour_run_offset (S.runIndex i) hk).trans
        ((S.projectedRun_direction (S.runIndex i)).symm.trans hdir)
    let r : Fin (P.compressorInput hrootUnique).lastEdge :=
      ⟨RunCompressor.runLower S.runs (S.runIndex i) + k, by
        change RunCompressor.runLower S.runs (S.runIndex i) + k < S.lastEdge
        exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
          (S.runUpper_le_lastEdge (S.runIndex i))⟩
    rcases P.compressorInput_edge hrootUnique r with h | h
    · apply h.2.2
      simpa [S, r] using hYmem
    · rw [h.1] at hcolour
      contradiction
  · rw [hdir] at hbackward
    contradiction

/-- Every backward run of the compiled prefix is made of literal reference
edges in the backward traversal direction. -/
theorem compiledRunWalk_backward_edge_mem
    (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0)
    (i : Fin ((P.compiledRunWalk hrootUnique).lastIndex + 1))
    (hdir : ((P.compiledRunWalk hrootUnique).run i).link.direction =
      .backward) :
    ((P.compiledRunWalk hrootUnique).run i).link.path.edgeSet ⊆
      familyEdges Y := by
  let S := P.compressorInput hrootUnique
  change (S.projectedRun (S.runIndex i)).link.path.edgeSet ⊆ familyEdges Y
  change (S.projectedRun (S.runIndex i)).link.direction = .backward at hdir
  intro e he
  have hprov := S.projectedRun_edge_provenance (S.runIndex i) he
  rcases hprov with ⟨hforward, k, hk, rfl⟩ |
      ⟨_hbackward, k, hk, rfl⟩
  · rw [hdir] at hforward
    contradiction
  · have hcolour : S.colour ⟨RunCompressor.runLower S.runs (S.runIndex i) + k,
        by
          exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
            (S.runUpper_le_lastEdge (S.runIndex i))⟩ = .backward := by
      exact (S.colour_run_offset (S.runIndex i) hk).trans
        ((S.projectedRun_direction (S.runIndex i)).symm.trans hdir)
    let r : Fin (P.compressorInput hrootUnique).lastEdge :=
      ⟨RunCompressor.runLower S.runs (S.runIndex i) + k, by
        change RunCompressor.runLower S.runs (S.runIndex i) + k < S.lastEdge
        exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
          (S.runUpper_le_lastEdge (S.runIndex i))⟩
    rcases P.compressorInput_edge hrootUnique r with h | h
    · rw [h.1] at hcolour
      contradiction
    · simpa [S, r] using h.2.1

@[simp] theorem compiledRunWalk_initial (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0) :
    (P.compiledRunWalk hrootUnique).vertex 0 = root := by
  change finiteLoopVertex P.projectedVertex 0 = root
  rw [finiteLoopVertex_zero_of_root_unique P.projectedVertex hrootUnique]
  exact P.projectedVertex_zero

@[simp] theorem compiledRunWalk_terminal (P : FinitePortPrefix W Y root)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0) :
    let Q := P.compiledRunWalk hrootUnique
    Q.vertex (Q.run Q.lastRunIndex).last =
      P.projectedVertex ⟨P.lastIndex, Nat.lt_succ_self _⟩ := by
  let S := P.compressorInput hrootUnique
  change S.vertex ((S.toFiniteRunWalk).run
      S.toFiniteRunWalk.lastRunIndex).last = _
  rw [S.toFiniteRunWalk_final_last]
  change finiteLoopVertex P.projectedVertex
      (finiteLoopLength P.projectedVertex) = _
  exact finiteLoopVertex_last P.projectedVertex

end FinitePortPrefix

end


end TwoWarpMatchingTraversal
end Erdos599
