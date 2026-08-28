import ErdosProblems.Erdos577.NeighborRowBounds
import ErdosProblems.Erdos577.HighPairLeafExchange
import ErdosProblems.Erdos577.PathMiddleReplacements

/-! Two rows avoiding an opposite leaf pair force a common allowed leaf insertion. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma neighbor_union_complement_bound (x y z : V) (s : Finset V)
    (hxy : ∀ u ∈ s, ¬(G.Adj x u ∧ G.Adj y u))
    (hxz : ∀ u ∈ s, ¬(G.Adj x u ∧ G.Adj z u)) :
    (s.filter (G.Adj y) ∪ s.filter (G.Adj z)).card + degreeIn G x s ≤ s.card := by
  have hd : Disjoint (s.filter (G.Adj y) ∪ s.filter (G.Adj z)) (s.filter (G.Adj x)) :=
    disjoint_union_left.mpr ⟨(neighbor_filters_disjoint x y s hxy).symm,
      (neighbor_filters_disjoint x z s hxz).symm⟩
  have hh := card_le_card (union_subset
    (union_subset (filter_subset (G.Adj y) s) (filter_subset (G.Adj z) s))
    (filter_subset (G.Adj x) s))
  rw [card_union_of_disjoint hd] at hh
  exact hh

lemma Quadrilateral.opposite_pair_common (q : Quadrilateral G) (x y z : V)
    (hx : x ∉ q.support)
    (hrow : ∀ j : Fin 4, G.Adj x (q j) ↔ (5 : ℕ).testBit j.val = true)
    (hxy : ∀ u ∈ q.support, ¬(G.Adj x u ∧ G.Adj y u))
    (hxz : ∀ u ∈ q.support, ¬(G.Adj x u ∧ G.Adj z u))
    (hthree : 3 ≤ degreeIn G y q.support + degreeIn G z q.support) :
    CommonReplacement G y z x q.support := by
  have hcap := neighbor_union_complement_bound x y z q.support hxy hxz
  have hx2 : degreeIn G x q.support = 2 := by rw [q.degree_eq_mask x 5 hrow]; decide +kernel
  rw [q.card_support, hx2] at hcap
  obtain ⟨u, hu, hyu, hzu⟩ :=
    common_neighbor_of_union_bound (G := G) y z q.support 2 (by omega) (by omega)
  obtain ⟨i, rfl⟩ := (q.mem_support u).mp hu
  have hnx : ¬G.Adj x (q i) := fun he ↦ hxy (q i) hu ⟨he, hyu⟩
  have hi : i = 1 ∨ i = 3 := by
    fin_cases i
    · exact False.elim (hnx ((hrow 0).mpr (by decide)))
    · exact Or.inl rfl
    · exact False.elim (hnx ((hrow 2).mpr (by decide)))
    · exact Or.inr rfl
  exact ⟨q i, hu, hyu, hzu, q.high_pair_replace x hx hrow i hi⟩

end Erdos577
