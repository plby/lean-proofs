import ErdosProblems.Erdos577.FullLeafEquality

/-! The two actual matching triples used in the six-row alternative. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

lemma Configuration.matched_second_subset (h : Configuration c p s a y) :
    FullLeafEquality.matchedSecond p s a y ⊆ p.triangle ∪ a :=
  (filter_subset _ _).trans h.second_five_subset

lemma Configuration.matched_triples_disjoint (h : Configuration c p s a y) :
    Disjoint (s.erase y) (FullLeafEquality.matchedSecond p s a y) :=
  h.triple_second_disjoint.mono_right (filter_subset _ _)

lemma Configuration.matched_second_disjoint_block (h : Configuration c p s a y)
    {j : Finset V} (hj : j ∈ c.blocks) (hja : j ≠ a) :
    Disjoint (FullLeafEquality.matchedSecond p s a y) j :=
  (h.core_disjoint_block hj hja).mono_left h.matched_second_subset

theorem Maximal.first_matched_neighbor (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {u : V} (hu : u ∈ s.erase y) :
    ∃ v ∈ FullLeafEquality.matchedSecond p s a y, G.Adj u v := by
  have hpos : 0 < degreeIn G u (insert (p.vertices 3) a) := by
    rw [hm.first_matching_degree hcard hdeg hn hu]
    decide
  obtain ⟨v, hv⟩ := card_pos.mp hpos
  obtain ⟨hv, huv⟩ := mem_filter.mp hv
  refine ⟨v, mem_filter.mpr ⟨hv, ?_⟩, huv⟩
  exact card_pos.mpr ⟨u, mem_filter.mpr ⟨hu, huv.symm⟩⟩

theorem Maximal.matched_core_complement (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    G.IsNClique 4 ((p.triangle ∪ a) \ FullLeafEquality.matchedSecond p s a y) := by
  have hcore := hm.equality_core_complete hcard hdeg hn
  refine ⟨hcore.isClique.subset (coe_subset.mpr sdiff_subset), ?_⟩
  rw [card_sdiff_of_subset hm.1.matched_second_subset, hcore.card_eq,
    (hm.matched_second_triangle hcard hdeg hn).card_eq]

end Erdos577.FullLeafCore
