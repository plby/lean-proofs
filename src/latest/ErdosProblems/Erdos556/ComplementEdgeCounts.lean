import ErdosProblems.Erdos556.Basic
import Mathlib.Data.Nat.Choose.Cast

/-!
# Edge counts in a graph and its complement
-/

namespace Erdos556

open SimpleGraph Finset

theorem edge_count_add_complement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  classical
  have hdisj : Disjoint G.edgeFinset Gᶜ.edgeFinset := by
    rw [Finset.disjoint_left]
    intro e he hec
    rcases e with ⟨⟨u, v⟩⟩
    have hG : G.Adj u v := by simpa using he
    have hc : Gᶜ.Adj u v := by simpa using hec
    have hc' : u ≠ v ∧ ¬ G.Adj u v := by simpa only [compl_adj] using hc
    exact hc'.2 hG
  have hunion : G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset := by
    ext e
    rcases e with ⟨⟨u, v⟩⟩
    simp only [mem_union, mem_edgeFinset, mem_edgeSet, top_adj, compl_adj]
    constructor
    · rintro (h | h)
      · exact h.ne
      · exact h.1
    · intro hne
      by_cases h : G.Adj u v
      · exact Or.inl h
      · exact Or.inr ⟨hne, h⟩
  calc
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (G.edgeFinset ∪ Gᶜ.edgeFinset).card :=
      (card_union_of_disjoint hdisj).symm
    _ = (Fintype.card V).choose 2 := by rw [hunion, card_edgeFinset_top_eq_card_choose_two]

theorem twice_edge_count_add_complement_real {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * ((G.edgeFinset.card : ℝ) + Gᶜ.edgeFinset.card) =
      (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
  have h : (G.edgeFinset.card : ℝ) + Gᶜ.edgeFinset.card = ((Fintype.card V).choose 2 : ℝ) := by
    exact_mod_cast edge_count_add_complement G
  rw [h, Nat.cast_choose_two]
  ring

theorem twice_edge_count_le_order_real {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
  have h : (G.edgeFinset.card : ℝ) ≤ ((Fintype.card V).choose 2 : ℝ) := by
    exact_mod_cast G.card_edgeFinset_le_card_choose_two
  rw [Nat.cast_choose_two] at h
  linarith

theorem complement_induce_eq {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (G.induce S)ᶜ = Gᶜ.induce S := by
  ext x y
  simp only [compl_adj, induce_adj, ne_eq, Subtype.coe_inj]

#print axioms twice_edge_count_add_complement_real

end Erdos556
