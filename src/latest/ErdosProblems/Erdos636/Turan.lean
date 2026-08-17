import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A coarse Turán bound for independent sets

The maximal-independent-set covering argument gives an independent set `S` whose closed
neighbourhoods cover the graph.  Since every closed neighbourhood has at most `maxDegree + 1`
vertices, this proves `|V| ≤ |S| (maxDegree + 1)`.
-/

namespace Erdos636

open SimpleGraph

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every finite graph has an independent set whose cardinality, multiplied by one more than
the maximum degree, is at least the number of vertices. -/
theorem exists_indepSet_card_mul_maxDegree_add_one :
    ∃ S : Finset V,
      G.IsIndepSet S ∧ Fintype.card V ≤ S.card * (G.maxDegree + 1) := by
  classical
  obtain ⟨S, hS⟩ := G.maximumIndepSet_exists
  have hdom : ∀ v : V, v ∈ S ∨ ∃ u ∈ S, G.Adj u v := by
    intro v
    by_cases hv : v ∈ S
    · exact Or.inl hv
    · right
      by_contra! hnot
      have hins : G.IsIndepSet (insert v S : Finset V) := by
        rw [isIndepSet_iff]
        intro a ha b hb hab
        simp only [Finset.coe_insert, Set.mem_insert_iff] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact (hab rfl).elim
        · simpa [G.adj_comm] using hnot b hb
        · exact hnot a ha
        · exact hS.isIndepSet ha hb hab
      have hcard := hS.maximum (insert v S) hins
      simp [hv] at hcard
  refine ⟨S, hS.isIndepSet, ?_⟩
  let closedN : V → Finset V := fun v ↦ insert v (G.neighborFinset v)
  have hcover : (Finset.univ : Finset V) ⊆ S.biUnion closedN := by
    intro v _
    rcases hdom v with hv | ⟨u, hu, huv⟩
    · exact Finset.mem_biUnion.mpr ⟨v, hv, by simp [closedN]⟩
    · exact Finset.mem_biUnion.mpr ⟨u, hu, by simp [closedN, huv]⟩
  calc
    Fintype.card V = (Finset.univ : Finset V).card := by simp
    _ ≤ (S.biUnion closedN).card := Finset.card_le_card hcover
    _ ≤ S.card * (G.maxDegree + 1) := by
      apply Finset.card_biUnion_le_card_mul
      intro v _
      simp only [closedN, Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),
        G.card_neighborFinset_eq_degree]
      exact Nat.add_le_add_right (G.degree_le_maxDegree v) 1

end Erdos636
