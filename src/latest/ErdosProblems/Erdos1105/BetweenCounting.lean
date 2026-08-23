import ErdosProblems.Erdos1105.Disintegration
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Erdos1105

open SimpleGraph Finset

lemma degreeWithin_le_card {V : Type*} (G : SimpleGraph V) (A : Finset V) (v : V) :
    degreeWithin G A v ≤ A.card := by
  classical
  exact card_filter_le _ _

lemma all_adj_of_degreeWithin_eq_card {V : Type*} (G : SimpleGraph V) (A : Finset V) (v : V)
    (hdeg : degreeWithin G A v = A.card) : ∀ x ∈ A, G.Adj v x := by
  classical
  have hfilter : A.filter (G.Adj v) = A :=
    eq_of_subset_of_card_le (filter_subset _ _) (by exact hdeg.ge)
  intro x hx
  exact (mem_filter.mp (hfilter ▸ hx)).2

theorem between_degree_right {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {A B : Finset V} (hAB : Disjoint A B)
    {y : V} (hy : y ∈ B) :
    (G.between (A : Set V) (B : Set V)).degree y = degreeWithin G A y := by
  classical
  rw [← card_neighborFinset_eq_degree]
  apply congrArg Finset.card
  ext x
  simp only [mem_neighborFinset, between_adj, mem_coe, mem_filter]
  constructor
  · rintro ⟨hxy, h | h⟩
    · exact (Finset.disjoint_left.mp hAB h.1 hy).elim
    · exact ⟨h.2, hxy⟩
  · rintro ⟨hx, hxy⟩
    exact ⟨hxy, Or.inr ⟨hy, hx⟩⟩

theorem between_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {A B : Finset V} (hAB : Disjoint A B) :
    (G.between (A : Set V) (B : Set V)).edgeFinset.card = ∑ y ∈ B, degreeWithin G A y := by
  classical
  have hbip := G.between_isBipartiteWith (show Disjoint (A : Set V) (B : Set V) from
    Set.disjoint_left.mpr (fun x hx hy ↦ Finset.disjoint_left.mp hAB hx hy))
  rw [← isBipartiteWith_sum_degrees_eq_card_edges hbip.symm]
  exact sum_congr rfl (fun y hy ↦ between_degree_right G hAB hy)

/-- Count all edges of a graph having a vertex cover `A`: edges inside
`A`, followed by edges from its complement into `A`. -/
theorem vertex_cover_edge_count_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (hcover : ∀ x y, G.Adj x y → x ∈ A ∨ y ∈ A) :
    G.edgeFinset.card ≤ (E767EGApi.edgesInside G A).card +
      ∑ y ∈ Aᶜ, degreeWithin G A y := by
  classical
  have hsub : G.edgeFinset ⊆ E767EGApi.edgesInside G A ∪
      (G.between (A : Set V) (↑(Aᶜ) : Set V)).edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : G.Adj x y := mem_edgeFinset.mp he
      by_cases hx : x ∈ A
      · by_cases hy : y ∈ A
        · apply mem_union_left
          apply mem_filter.mpr
          refine ⟨he, ?_⟩
          intro z hz
          have hz : z = x ∨ z = y := by simpa using hz
          rcases hz with rfl | rfl <;> assumption
        · exact mem_union_right _ (mem_edgeFinset.mpr ⟨hxy, Or.inl ⟨hx, mem_compl.mpr hy⟩⟩)
      · have hy := (hcover x y hxy).resolve_left hx
        exact mem_union_right _ (mem_edgeFinset.mpr ⟨hxy, Or.inr ⟨mem_compl.mpr hx, hy⟩⟩)
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  have hcross := between_edge_count G (A := A) (B := Aᶜ) disjoint_compl_right
  omega

theorem vertex_cover_edge_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (hcover : ∀ x y, G.Adj x y → x ∈ A ∨ y ∈ A) :
    G.edgeFinset.card ≤ A.card.choose 2 + ∑ y ∈ Aᶜ, degreeWithin G A y :=
  (vertex_cover_edge_count_le G A hcover).trans
    (Nat.add_le_add_right (edgesInside_le_choose G A) _)

end Erdos1105

#print axioms Erdos1105.vertex_cover_edge_bound
