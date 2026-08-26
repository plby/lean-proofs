import ErdosProblems.Erdos556.DeletionEdges
import ErdosProblems.Erdos556.Separation
import ErdosProblems.Erdos556.PieceFamilies

/-!
# Edge accounting for decomposition

A small side of a separation can be removed at a cost proportional to its
own order. The quadratic error potential pays for splitting two large sides.
-/

namespace Erdos556

open SimpleGraph Finset

theorem edge_count_le_induce_compl_add_sum_degree {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    G.edgeFinset.card ≤ (G.induce (S : Set V)ᶜ).edgeFinset.card +
      ∑ v ∈ S, G.degree v := by
  classical
  let A := G.edgeFinset.filter (fun e => e.toFinset ⊆ Sᶜ)
  let B := S.biUnion (fun v => G.incidenceFinset v)
  have hcover : G.edgeFinset ⊆ A ∪ B := by
    intro e he
    by_cases h : e.toFinset ⊆ Sᶜ
    · exact mem_union_left _ (mem_filter.mpr ⟨he, h⟩)
    · obtain ⟨x, hxe, hx⟩ := not_subset.mp h
      have hxS : x ∈ S := by simpa only [mem_compl, not_not] using hx
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨x, hxS, ?_⟩
      rw [G.incidenceFinset_eq_filter]
      exact mem_filter.mpr ⟨he, by simpa using hxe⟩
  have hA : A.card = (G.induce (S : Set V)ᶜ).edgeFinset.card := by
    have h := congrArg Finset.card (G.map_edgeFinset_induce (s := (S : Set V)ᶜ))
    simp only [card_map] at h
    have heq : G.edgeFinset ∩ ((S : Set V)ᶜ).toFinset.sym2 = A := by
      simp [A, G.filter_edgeFinset_toFinset_subset]
    rw [heq] at h
    exact h.symm
  have hB : B.card ≤ ∑ v ∈ S, G.degree v := by
    simpa only [G.card_incidenceFinset_eq_degree] using
      (card_biUnion_le : B.card ≤ ∑ v ∈ S, (G.incidenceFinset v).card)
  exact (card_le_card hcover).trans ((card_union_le A B).trans (by omega))

theorem edge_count_le_induce_compl_add_card_mul_of_degree_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (d : ℕ)
    (hd : ∀ v ∈ S, G.degree v ≤ d) :
    G.edgeFinset.card ≤ (G.induce (S : Set V)ᶜ).edgeFinset.card + S.card * d := by
  have hsum : (∑ v ∈ S, G.degree v) ≤ S.card * d := by
    calc
      (∑ v ∈ S, G.degree v) ≤ ∑ _v ∈ S, d := sum_le_sum hd
      _ = S.card * d := by simp
  exact (edge_count_le_induce_compl_add_sum_degree G S).trans (by omega)

theorem decomposition_split_potential (r a b s N : ℕ)
    (ha : r < a) (hb : r < b) (hs : s ≤ 1) (hN : a + b + s = N) :
    (r + 1) ^ 2 * a + a ^ 2 + ((r + 1) ^ 2 * b + b ^ 2) +
      (r + 1) * (s * N) ≤ (r + 1) ^ 2 * N + N ^ 2 := by
  have hra : r + 1 ≤ a := ha
  have hrb : r + 1 ≤ b := hb
  have h1 := Nat.mul_le_mul_right b hra
  have h2 := Nat.mul_le_mul_right a hrb
  interval_cases s <;> nlinarith

#print axioms edge_count_le_induce_compl_add_sum_degree
#print axioms decomposition_split_potential

end Erdos556
