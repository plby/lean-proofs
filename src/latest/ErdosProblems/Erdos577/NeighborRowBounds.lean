import ErdosProblems.Erdos577.LocalPathPartition

/-! Disjoint neighbor rows and the row consequences of a forbidden universal insertion. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma no_common_of_universal_insertion (x y z : V) (s : Finset V)
    (hn : ¬CommonReplacement G x y z s)
    (hrep : ∀ u ∈ s, QuadOn G (insert z (s.erase u))) :
    ∀ u ∈ s, ¬(G.Adj x u ∧ G.Adj y u) := by
  intro u hu hh
  exact hn ⟨u, hu, hh.1, hh.2, hrep u hu⟩

variable [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma neighbor_filters_disjoint (x y : V) (s : Finset V)
    (h : ∀ u ∈ s, ¬(G.Adj x u ∧ G.Adj y u)) :
    Disjoint (s.filter (G.Adj x)) (s.filter (G.Adj y)) := by
  apply disjoint_left.mpr
  intro u hu hv
  exact h u (mem_filter.mp hu).1 ⟨(mem_filter.mp hu).2, (mem_filter.mp hv).2⟩

omit [DecidableEq V] in
lemma degree_pair_le_card (x y : V) (s : Finset V)
    (h : ∀ u ∈ s, ¬(G.Adj x u ∧ G.Adj y u)) :
    degreeIn G x s + degreeIn G y s ≤ s.card := by
  classical
  have hd := neighbor_filters_disjoint x y s h
  calc
    _ = (s.filter (G.Adj x) ∪ s.filter (G.Adj y)).card :=
      (card_union_of_disjoint hd).symm
    _ ≤ s.card := card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))

omit [DecidableEq V] in
lemma degree_triple_le_card (x y z : V) (s : Finset V)
    (hxy : ∀ u ∈ s, ¬(G.Adj x u ∧ G.Adj y u))
    (hxz : ∀ u ∈ s, ¬(G.Adj x u ∧ G.Adj z u))
    (hyz : ∀ u ∈ s, ¬(G.Adj y u ∧ G.Adj z u)) :
    degreeIn G x s + degreeIn G y s + degreeIn G z s ≤ s.card := by
  classical
  have hxy' := neighbor_filters_disjoint x y s hxy
  have hxz' := neighbor_filters_disjoint x z s hxz
  have hyz' := neighbor_filters_disjoint y z s hyz
  calc
    _ = ((s.filter (G.Adj x) ∪ s.filter (G.Adj y)) ∪ s.filter (G.Adj z)).card := by
      rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hxz', hyz'⟩),
        card_union_of_disjoint hxy']
      rfl
    _ ≤ s.card := card_le_card (union_subset
      (union_subset (filter_subset _ _) (filter_subset _ _)) (filter_subset _ _))

end Erdos577
