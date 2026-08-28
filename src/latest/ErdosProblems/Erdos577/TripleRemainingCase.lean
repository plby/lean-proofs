import ErdosProblems.Erdos577.TripleForbiddenTriangles

/-! The remaining C configuration: its actual paw, excluded center edge and equal-score chain. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure CCase (p : Paw G) (a : Finset V) (w u v : V) : Prop where
  first_mem : u ∈ a
  second_mem : v ∈ a
  marked_mem : w ∈ ({u, v} : Finset V)
  triangle : G.IsNClique 3 {p.center, u, v}
  complement_quad : QuadOn G ((p.triangle ∪ a) \ {p.center, u, v})
  complement_score : edgeCount G a ≤ edgeCount G ((p.triangle ∪ a) \ {p.center, u, v})
  core_budget : contacts G {p.center, u, v} (p.triangle ∪ a) ≤ 17

variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {w u v : V}

omit [Fintype V] in
lemma CCase.core_subset (s : CCase p a w u v) :
    ({p.center, u, v} : Finset V) ⊆ p.triangle ∪ a :=
  insert_subset (mem_union_left _ p.center_mem_triangle)
    (insert_subset (mem_union_right _ s.first_mem)
      (singleton_subset_iff.mpr (mem_union_right _ s.second_mem)))

def CCase.paw (s : CCase p a w u v) (h : HighCore c p q a w) : Paw G :=
  Paw.ofVertices p.leaf p.center u v p.pendant.ne
    (fun he ↦ h.leaf_outside_core (he.symm ▸ mem_union_right _ s.first_mem))
    (fun he ↦ h.leaf_outside_core (he.symm ▸ mem_union_right _ s.second_mem))
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).1.ne
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).2.1.ne
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).2.2.ne p.pendant
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).1
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).2.1
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).2.2

lemma CCase.paw_apply (s : CCase p a w u v) (h : HighCore c p q a w) (i : Fin 4) :
    (s.paw h).vertices i = ![p.leaf, p.center, u, v] i := rfl

lemma CCase.paw_triangle (s : CCase p a w u v) (h : HighCore c p q a w) :
    (s.paw h).triangle = {p.center, u, v} := rfl

theorem CCase.center_nonadj (s : CCase p a w u v) (h : HighCore c p q a w)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    ¬G.Adj p.center (q 3) := by
  intro hlink
  have hrw : p.center ≠ w := fun he ↦ disjoint_left.mp
    (h.toConfiguration.paw_disjoint_block h.core_block)
    (p.support_eq ▸ mem_insert_of_mem p.center_mem_triangle) (he.symm ▸ h.marked)
  have hwtri : w ∈ ({p.center, u, v} : Finset V) := mem_insert_of_mem s.marked_mem
  have htwo := JointFinal.two_neighbors_degree
    (mem_insert_self p.center ({u, v} : Finset V)) hwtri hrw hlink.symm
    ((h.exposed_row w h.marked).mpr rfl)
  have hquad := QuadOn.of_triangle s.triangle
    (fun hh ↦ h.exposed_outside_core (s.core_subset hh)) htwo
  have hf : LocalFactor G (insert (q 3) (p.triangle ∪ a)) := by
    refine ⟨insert (q 3) ({p.center, u, v} : Finset V), insert_subset_insert (q 3) s.core_subset,
      hquad, ?_⟩
    convert s.complement_quad using 1
    ext z
    by_cases he : z = q 3
    · subst z
      simp [h.exposed_outside_core]
    · simp [he]
  exact h.toConfiguration.no_exposed_core_factor hcard hn h.core_block h.core_ne hf

theorem CCase.exists_chain (s : CCase p a w u v) (h : HighCore c p q a w)
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    ∃ d : TriangleChain G, d.Strong ∧ (s.paw h).support = d.remainder ∧
      d.terminal = p.leaf ∧ d.triangle = {p.center, u, v} ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      ∀ j ∈ c.blocks, j ≠ a → j ∈ d.blocks := by
  let d := c.presentPaw p h.paw
  have hd : d.Feasible := hc.presentPaw_feasible p h.paw
  have hsub : (s.paw h).triangle ⊆ d.triangle ∪ a := s.core_subset
  have hquad : QuadOn G ((d.triangle ∪ a) \ (s.paw h).triangle) := s.complement_quad
  have hscore : edgeCount G a ≤ edgeCount G ((d.triangle ∪ a) \ (s.paw h).triangle) :=
    s.complement_score
  obtain ⟨e, he, hp, ht, htri, heE, heC, hbs⟩ :=
    hd.exchange_core_triangle hcard hn h.core_block (s.paw h) rfl hsub hquad hscore
  refine ⟨e, he, hp, ht, htri.trans (s.paw_triangle h), heE, heC, ?_⟩
  intro j hj hja
  rw [hbs]
  exact mem_union_left _ (mem_erase.mpr ⟨hja, hj⟩)

lemma CCase.exposed_pair_degree (s : CCase p a w u v) (h : HighCore c p q a w) :
    degreeIn G (q 3) {u, v} = 1 := by
  have hsub : ({u, v} : Finset V) ⊆ a :=
    insert_subset s.first_mem (singleton_subset_iff.mpr s.second_mem)
  have he : ({u, v} : Finset V).filter (G.Adj (q 3)) = {w} := by
    ext z
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hz, hadj⟩
      exact (h.exposed_row z (hsub hz)).mp hadj
    · intro hz
      subst z
      exact ⟨s.marked_mem, (h.exposed_row w h.marked).mpr rfl⟩
  rw [degreeIn, he, card_singleton]

end Erdos577.UniversalTriple
