import ErdosProblems.Erdos556.ThreeColourDecomposition
import ErdosProblems.Erdos556.GraphUnionCounts

/-! The retained edge total and the common deleted-edge budget. -/

namespace Erdos556

open SimpleGraph Finset

theorem ThreeColourDecomposition.parts_disjoint {V : Type*}
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) (i : Fin 3) :
    Disjoint (h.bipartite i) (h.sparse i) := by
  apply SimpleGraph.disjoint_left.mpr
  intro u v hB hF
  exact (h.bipartite_off i u v hB).1 (h.sparse_on i u v hF).1

theorem ThreeColourDecomposition.retained_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) :
    Nat.card h.retained.edgeSet =
      ∑ i, (Nat.card (h.bipartite i).edgeSet + Nat.card (h.sparse i).edgeSet) := by
  have hdis (i j : Fin 3) (hij : i ≠ j) :
      Disjoint (h.bipartite i ⊔ h.sparse i) (h.bipartite j ⊔ h.sparse j) :=
    (c.graphs_disjoint i j hij).mono (sup_le (h.bipartite_le i) (h.sparse_le i))
      (sup_le (h.bipartite_le j) (h.sparse_le j))
  dsimp only [retained]
  rw [natCard_edges_iSup _ hdis]
  apply sum_congr rfl
  intro i _
  exact natCard_edges_sup _ _ (h.parts_disjoint i)

theorem ThreeColourDecomposition.missing_edge_count_le {V : Type*} [Fintype V] [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) :
    (Nat.card h.missing.edgeSet : ℝ) ≤ 3 * E := by
  have hcol : (∑ i, (Nat.card (c.graph i).edgeSet : ℝ)) = Nat.card (⊤ : SimpleGraph V).edgeSet := by
    exact_mod_cast c.sum_edge_counts
  have hret : (Nat.card h.retained.edgeSet : ℝ) =
      ∑ i, ((Nat.card (h.bipartite i).edgeSet : ℝ) + Nat.card (h.sparse i).edgeSet) := by
    exact_mod_cast h.retained_edge_count
  have hcomp : (Nat.card h.retained.edgeSet : ℝ) + Nat.card h.missing.edgeSet =
      Nat.card (⊤ : SimpleGraph V).edgeSet := by
    exact_mod_cast natCard_edges_add_complement h.retained
  have hsum : (∑ i, (Nat.card (c.graph i).edgeSet : ℝ)) ≤
      (∑ i, ((Nat.card (h.bipartite i).edgeSet : ℝ) + Nat.card (h.sparse i).edgeSet)) + 3 * E := by
    calc
      _ ≤ ∑ i, ((Nat.card (h.bipartite i).edgeSet : ℝ) + Nat.card (h.sparse i).edgeSet + E) :=
        sum_le_sum (fun i _ => h.edge_loss i)
      _ = _ := by rw [sum_add_distrib]; simp
  linarith

theorem ThreeColourDecomposition.sparse_edge_count_le {V : Type*} [Fintype V] [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) (i : Fin 3) :
    (Nat.card (h.sparse i).edgeSet : ℝ) ≤ D * (h.stars i).card := by
  classical
  have hsupp : (h.sparse i).support ⊆ (h.stars i : Set V) := by
    intro u hu
    obtain ⟨v, huv⟩ := hu
    exact (h.sparse_on i u v huv).1
  have hcount := (h.sparse i).card_edgeFinset_induce_of_support_subset hsupp
  simp only [edgeFinset_card_eq_natCard_edgeSet] at hcount
  have hd := h.hereditary_density i (h.stars i)
  rw [hcount] at hd
  exact hd

#print axioms ThreeColourDecomposition.missing_edge_count_le

end Erdos556
