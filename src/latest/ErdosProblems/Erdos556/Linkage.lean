/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos556.Basic

/-!
# Vertex 2-connectivity and cycle-linkage bookkeeping for Erdős Problem 58

This file deliberately keeps the usual deletion definition of vertex
2-connectivity separate from the conclusion of the two-path form of Menger's
theorem.  `TwoLinkage` is the finite certificate delivered by that theorem.

The last section contains the length and parity calculation used when two
vertex-disjoint cycles are joined by a `TwoLinkage`: of the parallel and
crossed pairings, exactly one consists of odd closed walks, and the sum of the
two lengths in either pairing is the sum of the old cycle lengths plus twice
the total length of the linking paths.
-/

namespace Erdos556

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- The standard finite-graph definition of vertex 2-connectivity: there are
at least three vertices, the graph is connected, and deleting any one vertex
leaves a connected graph. -/
def TwoConnected (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧ G.Connected ∧
    ∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected

namespace TwoConnected

theorem card_three_le (hG : TwoConnected G) : 3 ≤ Fintype.card V := hG.1

theorem connected (hG : TwoConnected G) : G.Connected := hG.2.1

theorem delete_connected (hG : TwoConnected G) (v : V) :
    (G.induce ({v}ᶜ : Set V)).Connected :=
  hG.2.2 v

theorem nontrivial (hG : TwoConnected G) : Nontrivial V := by
  exact Fintype.one_lt_card_iff_nontrivial.mp (by
    have h := hG.card_three_le
    omega)

theorem exists_ne (hG : TwoConnected G) (v : V) : ∃ w : V, w ≠ v := by
  letI := hG.nontrivial
  exact _root_.exists_ne v

theorem exists_two_ne (hG : TwoConnected G) (v : V) :
    ∃ x y : V, x ≠ v ∧ y ≠ v ∧ x ≠ y := by
  have hcard : 2 ≤ Fintype.card ({v}ᶜ : Set V) := by
    rw [Fintype.card_compl_set, Set.card_singleton]
    have h := hG.card_three_le
    omega
  letI : Nontrivial ({v}ᶜ : Set V) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne ({v}ᶜ : Set V)
  have hx : (x : V) ≠ v := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2
  have hy : (y : V) ≠ v := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y.2
  exact ⟨x, y, hx, hy, fun h ↦ hxy (Subtype.ext h)⟩

/-- In a 2-connected graph, any two vertices other than `z` can be joined by
a simple path avoiding `z`.  This is the direct path-level content of the
connectivity of `G - z`. -/
theorem exists_path_avoiding (hG : TwoConnected G) (z : V) {x y : V}
    (hx : x ≠ z) (hy : y ≠ z) :
    ∃ p : G.Walk x y, p.IsPath ∧ z ∉ p.support := by
  let x' : ({z}ᶜ : Set V) := ⟨x, hx⟩
  let y' : ({z}ᶜ : Set V) := ⟨y, hy⟩
  obtain ⟨p, hp⟩ := (hG.delete_connected z).exists_isPath x' y'
  let e : G.induce ({z}ᶜ : Set V) ↪g G :=
    SimpleGraph.Embedding.induce ({z}ᶜ : Set V)
  let q := p.map e.toHom
  have hqpath : q.IsPath := hp.map e.injective
  have hqavoid : z ∉ q.support := by
    intro hz
    have hsupport : q.support = p.support.map e := by
      exact SimpleGraph.Walk.support_map e.toHom p
    rw [hsupport, List.mem_map] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have hwne : (w : V) ≠ z := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using w.2
    exact hwne hwz
  have hex : e x' = x := by rfl
  have hey : e y' = y := by rfl
  let q' : G.Walk x y := q.copy hex hey
  have hq'path : q'.IsPath :=
    (SimpleGraph.Walk.isPath_copy q hex hey).2 hqpath
  have hq'avoid : z ∉ q'.support := by
    simpa only [q', SimpleGraph.Walk.support_copy] using hqavoid
  exact ⟨q', hq'path, hq'avoid⟩

/-- Any two distinct neighbors of a vertex in a 2-connected graph lie with
that vertex on a simple cycle.  This is a useful rigorously proved special
linkage consequence which needs only one application of
`exists_path_avoiding`, rather than the full two-set Menger theorem. -/
theorem exists_cycle_through_two_neighbors (hG : TwoConnected G)
    {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : y ≠ z) :
    ∃ c : G.Walk x x, c.IsCycle := by
  obtain ⟨p, hp, hpx⟩ :=
    hG.exists_path_avoiding x hxy.ne.symm hxz.ne.symm
  let q : G.Walk y x := p.concat hxz.symm
  have hq : q.IsPath := hp.concat hpx hxz.symm
  have hedge : s(x, y) ∉ q.edges := by
    intro hedge
    have hedge' : s(y, x) ∈ q.edges := by
      simpa only [Sym2.eq_swap] using hedge
    have hlen : q.length = 1 := hq.length_eq_one_of_mem_edges hedge'
    have hplen : p.length = 0 := by
      have hq_length : q.length = p.length + 1 := by simp [q]
      omega
    exact hyz (p.eq_of_length_eq_zero hplen)
  exact ⟨Walk.cons hxy q, (Walk.cons_isCycle_iff q hxy).2 ⟨hq, hedge⟩⟩

end TwoConnected

/-! ## Two-linkage certificates -/

/-- A certificate consisting of two fully vertex-disjoint paths from `A` to
`B`.  Disjointness of their complete supports implies, in particular, that
the two endpoints in `A` are distinct and the two endpoints in `B` are
distinct.  The `interior` fields record the usual truncation convention in
the set form of Menger's theorem. -/
structure TwoLinkage (G : SimpleGraph V) (A B : Set V) where
  a₁ : V
  a₂ : V
  b₁ : V
  b₂ : V
  p : G.Walk a₁ b₁
  q : G.Walk a₂ b₂
  p_isPath : p.IsPath
  q_isPath : q.IsPath
  a₁_mem : a₁ ∈ A
  a₂_mem : a₂ ∈ A
  b₁_mem : b₁ ∈ B
  b₂_mem : b₂ ∈ B
  disjoint_support : p.support.Disjoint q.support
  p_interior : ∀ x ∈ p.support.tail.dropLast, x ∉ A ∪ B
  q_interior : ∀ x ∈ q.support.tail.dropLast, x ∉ A ∪ B

namespace TwoLinkage

variable {A B : Set V}

theorem a_ne (L : TwoLinkage G A B) : L.a₁ ≠ L.a₂ := by
  intro h
  exact L.disjoint_support L.p.start_mem_support (h.symm ▸ L.q.start_mem_support)

theorem b_ne (L : TwoLinkage G A B) : L.b₁ ≠ L.b₂ := by
  intro h
  exact L.disjoint_support L.p.end_mem_support (h.symm ▸ L.q.end_mem_support)

theorem p_nonempty (L : TwoLinkage G A B) (hAB : Disjoint A B) : 0 < L.p.length := by
  by_contra h
  have hp0 : L.p.length = 0 := by omega
  have hab : L.a₁ = L.b₁ := L.p.eq_of_length_eq_zero hp0
  exact Set.disjoint_left.1 hAB L.a₁_mem (hab.symm ▸ L.b₁_mem)

theorem q_nonempty (L : TwoLinkage G A B) (hAB : Disjoint A B) : 0 < L.q.length := by
  by_contra h
  have hq0 : L.q.length = 0 := by omega
  have hab : L.a₂ = L.b₂ := L.q.eq_of_length_eq_zero hq0
  exact Set.disjoint_left.1 hAB L.a₂_mem (hab.symm ▸ L.b₂_mem)

theorem total_length_pos (L : TwoLinkage G A B) (hAB : Disjoint A B) :
    0 < L.p.length + L.q.length := by
  have hp := L.p_nonempty hAB
  omega

end TwoLinkage


end Erdos556

#print axioms Erdos556.TwoConnected.exists_path_avoiding

namespace Erdos556

open SimpleGraph

theorem TwoConnected.iso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : TwoConnected G) (e : G ≃g H) : TwoConnected H := by
  classical
  refine ⟨?_, hG.connected.map e.toHom e.surjective, ?_⟩
  · rw [← Fintype.card_congr e.toEquiv]
    exact hG.card_three_le
  · intro w
    have hbij : Set.BijOn e ({e.symm w}ᶜ : Set V) ({w}ᶜ : Set W) := by
      refine ⟨?_, e.injective.injOn, ?_⟩
      · intro x hx
        change e x ≠ w
        intro heq
        apply hx
        exact e.injective (heq.trans (e.apply_symm_apply w).symm)
      · intro y hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        intro h
        exact hy (e.symm.injective h)
    let f := e.induce hbij
    exact (hG.delete_connected (e.symm w)).map f.toHom f.surjective

#print axioms TwoConnected.iso

end Erdos556
