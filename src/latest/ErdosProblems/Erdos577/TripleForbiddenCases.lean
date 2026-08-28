import ErdosProblems.Erdos577.TripleHeavyCount

/-! The two explicit forbidden-triangle hypotheses and their actual ordered paws. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure UCase (p : Paw G) (a : Finset V) (w u v : V) : Prop where
  triangle : G.IsNClique 3 {w, u, v}
  subset : {w, u, v} ⊆ (p.triangle ∪ a) \ {p.center, p.vertices 2}
  bridge : G.Adj p.center u
  complement_quad : QuadOn G ((p.triangle ∪ a) \ {w, u, v})
  complement_score : edgeCount G a ≤ edgeCount G ((p.triangle ∪ a) \ {w, u, v})
  final_quad : QuadOn G ((p.triangle ∪ a) \ {u, v, p.center})
  left_quad : QuadOn G ((p.triangle ∪ a) \ {p.vertices 2, w, u})
  right_quad : QuadOn G ((p.triangle ∪ a) \ {p.vertices 2, w, v})

structure VCase (p : Paw G) (a : Finset V) (w u v : V) : Prop where
  triangle : G.IsNClique 3 {p.center, u, v}
  subset : {p.center, u, v} ⊆ (p.triangle ∪ a) \ {w, p.vertices 2}
  bridge : G.Adj w u
  complement_quad : QuadOn G ((p.triangle ∪ a) \ {p.center, u, v})
  complement_score : edgeCount G a ≤ edgeCount G ((p.triangle ∪ a) \ {p.center, u, v})
  final_quad : QuadOn G ((p.triangle ∪ a) \ {u, v, w})
  left_quad : QuadOn G ((p.triangle ∪ a) \ {p.vertices 2, p.center, u})
  right_quad : QuadOn G ((p.triangle ∪ a) \ {p.vertices 2, p.center, v})

variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {w u v : V}

omit [Fintype V] in
lemma UCase.rows_data (s : UCase p a w u v) :
    u ∈ p.triangle ∪ a ∧ v ∈ p.triangle ∪ a ∧ u ≠ v ∧
      u ≠ p.center ∧ u ≠ p.vertices 2 ∧ v ≠ p.center ∧ v ≠ p.vertices 2 := by
  have hu := mem_sdiff.mp (s.subset (by simp : u ∈ ({w, u, v} : Finset V)))
  have hv := mem_sdiff.mp (s.subset (by simp : v ∈ ({w, u, v} : Finset V)))
  have hu' : u ≠ p.center ∧ u ≠ p.vertices 2 := by
    simpa only [mem_insert, mem_singleton, not_or] using hu.2
  have hv' : v ≠ p.center ∧ v ≠ p.vertices 2 := by
    simpa only [mem_insert, mem_singleton, not_or] using hv.2
  have he := SimpleGraph.is3Clique_triple_iff.mp s.triangle
  exact ⟨hu.1, hv.1, he.2.2.ne, hu'.1, hu'.2, hv'.1, hv'.2⟩

omit [Fintype V] in
lemma VCase.rows_data (s : VCase p a w u v) :
    u ∈ p.triangle ∪ a ∧ v ∈ p.triangle ∪ a ∧ u ≠ v ∧
      u ≠ p.center ∧ u ≠ p.vertices 2 ∧ v ≠ p.center ∧ v ≠ p.vertices 2 := by
  have hu := mem_sdiff.mp (s.subset (by simp : u ∈ ({p.center, u, v} : Finset V)))
  have hv := mem_sdiff.mp (s.subset (by simp : v ∈ ({p.center, u, v} : Finset V)))
  have hu' : u ≠ w ∧ u ≠ p.vertices 2 := by
    simpa only [mem_insert, mem_singleton, not_or] using hu.2
  have hv' : v ≠ w ∧ v ≠ p.vertices 2 := by
    simpa only [mem_insert, mem_singleton, not_or] using hv.2
  have he := SimpleGraph.is3Clique_triple_iff.mp s.triangle
  exact ⟨hu.1, hv.1, he.2.2.ne, he.1.ne.symm, hu'.2, he.2.1.ne.symm, hv'.2⟩

def UCase.paw (s : UCase p a w u v) (h : HighCore c p q a w) : Paw G :=
  Paw.ofVertices (q 3) w u v
    ((h.exposed_row w h.marked).mpr rfl).ne
    (fun he ↦ h.exposed_outside_core (he.symm ▸ s.rows_data.1))
    (fun he ↦ h.exposed_outside_core (he.symm ▸ s.rows_data.2.1))
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).1.ne
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).2.1.ne
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).2.2.ne
    ((h.exposed_row w h.marked).mpr rfl)
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).1
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).2.1
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).2.2

def VCase.paw (s : VCase p a w u v) (h : HighCore c p q a w) : Paw G :=
  Paw.ofVertices p.leaf p.center u v p.pendant.ne
    (fun he ↦ h.leaf_outside_core (he.symm ▸ s.rows_data.1))
    (fun he ↦ h.leaf_outside_core (he.symm ▸ s.rows_data.2.1))
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).1.ne
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).2.1.ne
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).2.2.ne p.pendant
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).1
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).2.1
    (SimpleGraph.is3Clique_triple_iff.mp s.triangle).2.2

lemma UCase.paw_apply (s : UCase p a w u v) (h : HighCore c p q a w) (i : Fin 4) :
    (s.paw h).vertices i = ![q 3, w, u, v] i := rfl

lemma VCase.paw_apply (s : VCase p a w u v) (h : HighCore c p q a w) (i : Fin 4) :
    (s.paw h).vertices i = ![p.leaf, p.center, u, v] i := rfl

lemma UCase.paw_triangle (s : UCase p a w u v) (h : HighCore c p q a w) :
    (s.paw h).triangle = {w, u, v} := rfl

lemma VCase.paw_triangle (s : VCase p a w u v) (h : HighCore c p q a w) :
    (s.paw h).triangle = {p.center, u, v} := rfl

end Erdos577.UniversalTriple
