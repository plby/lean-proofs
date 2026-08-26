/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.VossCase3

/-! # Classification of the returns of a maximum ear -/

open SimpleGraph

namespace Erdos1091.Voss

theorem mixed_returns_impossible
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}
    (C : G.Walk z z) (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v)
    {d t : V} (hdC : d ∈ C.support) (hdE : d ∉ E.walk.support)
    (hret : G.Adj E.walk.snd d) (ht : t ∈ E.walk.support)
    (hyt : G.Adj E.walk.penultimate t)
    (hnot : s(E.walk.penultimate, t) ∉ E.walk.edges) : False := by
  by_cases htStart : t = E.start
  · subst t
    exact mixed_returns_to_initial_impossible C hC hno E hlen hdC hdE hret hyt hnot
  · exact mixed_returns_internal_not_initial_impossible C hC hno E hlen hmax hdegree
      hdC hdE hret ht htStart hyt hnot

namespace Ear

/-- After eliminating both mixed placements and both external returns,
every pair of off-ear returns is the single inner closing edge. -/
theorem returns_eq_inner_endpoints
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}
    (C : G.Walk z z) (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v)
    {x y : V} (hx : G.Adj E.walk.snd x) (hy : G.Adj E.walk.penultimate y)
    (hxNot : s(E.walk.snd, x) ∉ E.walk.edges)
    (hyNot : s(E.walk.penultimate, y) ∉ E.walk.edges)
    (hxMem : x ∈ E.walk.support ∨ x ∈ C.support)
    (hyMem : y ∈ E.walk.support ∨ y ∈ C.support) :
    x = E.walk.penultimate ∧ y = E.walk.snd := by
  by_cases hxE : x ∈ E.walk.support
  · by_cases hyE : y ∈ E.walk.support
    · exact E.returns_inside_eq C hC.1 hC.2.1 hno hlen hxE hyE hx hy hxNot hyNot
    · have hrlen : 3 ≤ E.reverse.walk.length := by
        simpa only [reverse, Walk.length_reverse] using hlen
      have hrmax : ∀ P : AttachmentPath G {v | v ∈ C.support},
          P.walk.length + 1 ≤ E.reverse.walk.length := by
        simpa only [reverse, Walk.length_reverse] using hmax
      have hyR : y ∉ E.reverse.walk.support := by
        simpa only [reverse, Walk.support_reverse, List.mem_reverse] using hyE
      have hxR : x ∈ E.reverse.walk.support := by
        simpa only [reverse, Walk.support_reverse, List.mem_reverse] using hxE
      have hret : G.Adj E.reverse.walk.snd y := by simpa only [reverse, Walk.snd_reverse] using hy
      have hlast : G.Adj E.reverse.walk.penultimate x := by
        simpa only [reverse, Walk.penultimate_reverse] using hx
      have hnot : s(E.reverse.walk.penultimate, x) ∉ E.reverse.walk.edges := by
        simpa only [reverse, Walk.penultimate_reverse, Walk.edges_reverse,
          List.mem_reverse] using hxNot
      exact (mixed_returns_impossible C hC hno E.reverse hrlen hrmax hdegree
        (hyMem.resolve_left hyE) hyR hret hxR hlast hnot).elim
  · by_cases hyE : y ∈ E.walk.support
    · exact (mixed_returns_impossible C hC hno E hlen hmax hdegree
        (hxMem.resolve_left hxE) hxE hx hyE hy hyNot).elim
    · exact (external_returns_impossible C hC hno E hlen
        (hxMem.resolve_left hxE) (hyMem.resolve_left hyE) hxE hyE hx hy).elim

/-- The inner endpoints of every maximum ear are joined by an actual
chord, not merely by a path edge. -/
theorem inner_closing_chord
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}
    (C : G.Walk z z) (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v) :
    E.walk.IsChord s(E.walk.snd, E.walk.penultimate) := by
  obtain ⟨x, y, hx, hy, hxNot, hyNot, hxMem, hyMem⟩ := E.exists_two_returns hlen hmax hdegree
  obtain ⟨rfl, rfl⟩ := E.returns_eq_inner_endpoints C hC hno hlen hmax hdegree
    hx hy hxNot hyNot hxMem hyMem
  exact ⟨hx, hxNot, E.walk.getVert_mem_support 1, E.walk.getVert_mem_support _⟩

/-- The first inner vertex has no neighbours besides its two ear
neighbours and the inner closing edge. -/
theorem adj_snd_cases
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}
    (C : G.Walk z z) (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v) {w : V} (hw : G.Adj E.walk.snd w) :
    w = E.start ∨ w = E.walk.getVert 2 ∨ w = E.walk.penultimate := by
  by_cases hwEdge : s(E.walk.snd, w) ∈ E.walk.edges
  · have hc := path_edge_at_index E.walk E.isPath (i := 1) (by omega) (by omega) hwEdge
    simpa only [Nat.reduceSub, Walk.getVert_zero, Nat.reduceAdd] using hc.imp_right Or.inl
  · have he := E.inner_closing_chord C hC hno hlen hmax hdegree
    have heRev : E.walk.IsChord s(E.walk.penultimate, E.walk.snd) := by
      simpa only [Sym2.eq_swap] using he
    have hrmax : ∀ P : AttachmentPath G {v | v ∈ C.support},
        P.walk.length + 1 ≤ E.reverse.walk.length := by
      simpa only [reverse, Walk.length_reverse] using hmax
    have hwR : G.Adj E.reverse.walk.penultimate w := by
      simpa only [reverse, Walk.penultimate_reverse] using hw
    have hwMem : w ∈ E.walk.support ∨ w ∈ C.support := by
      simpa only [reverse, Walk.length_reverse, Walk.support_reverse, List.mem_reverse,
        Set.mem_ofPred_eq] using
        E.reverse.neighbor_penultimate_mem (by simpa only [reverse, Walk.length_reverse] using
          (show 2 ≤ E.walk.length by omega)) hrmax hwR
    have heq := E.returns_eq_inner_endpoints C hC hno hlen hmax hdegree
      hw (Walk.isChord_sym2Mk.mp heRev).1 hwEdge heRev.2.1 hwMem
      (Or.inl (E.walk.getVert_mem_support 1))
    exact Or.inr (Or.inr heq.1)

/-- Both inner endpoints of a maximum ear have degree at most three. -/
theorem degree_snd_le_three
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}
    (C : G.Walk z z) (hC : IsShortestOddCycle C) (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {v | v ∈ C.support}) (hlen : 3 ≤ E.walk.length)
    (hmax : ∀ P : AttachmentPath G {v | v ∈ C.support}, P.walk.length + 1 ≤ E.walk.length)
    (hdegree : ∀ v, 3 ≤ G.degree v) : G.degree E.walk.snd ≤ 3 := by
  classical
  have hsub : G.neighborFinset E.walk.snd ⊆ {E.start, E.walk.getVert 2, E.walk.penultimate} := by
    intro w hw
    have hc := E.adj_snd_cases C hC hno hlen hmax hdegree (by simpa using hw)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
  have hcard := Finset.card_le_card hsub
  have h₁ := Finset.card_insert_le E.start ({E.walk.getVert 2, E.walk.penultimate} : Finset V)
  have h₂ := Finset.card_insert_le (E.walk.getVert 2) ({E.walk.penultimate} : Finset V)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  simp only [Finset.card_singleton] at h₂
  omega

end Ear

#print axioms Ear.inner_closing_chord
#print axioms Ear.degree_snd_le_three

end Erdos1091.Voss
