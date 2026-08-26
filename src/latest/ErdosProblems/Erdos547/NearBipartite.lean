import ErdosProblems.Erdos547.NearClique

/-!
# The near-complete bipartite case
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

open scoped Classical in
theorem ramsey_of_dense_bipartite_pair {m : ℕ} (hm : 20 ≤ m)
    (T : SimpleGraph (Fin (m + 1))) (hT : T.IsTree)
    (R : SimpleGraph (Fin (2 * m))) (d : ℕ) (hd : 20 * d ≤ m)
    (A B : Finset (Fin (2 * m))) (hA : A.Nonempty) (hdis : Disjoint A B)
    (hAB : ∀ a ∈ A, m ≤ degreeIn R B a + d)
    (hBA : ∀ b ∈ B, m ≤ degreeIn R A b + d) : T ⊑ R ∨ T ⊑ Rᶜ := by
  classical
  let : Nontrivial (Fin (m + 1)) := Fintype.one_lt_card_iff_nontrivial.mp (by
    simp only [Fintype.card_fin]; omega)
  obtain ⟨X, Y, hpart, hcover⟩ := exists_tree_bipartition T hT
  have hcover : X ∪ Y = Finset.univ := by
    simpa only [Finset.ext_iff, Finset.mem_union] using hcover
  by_cases hsmallX : 10 * X.card ≤ m
  · exact ramseyAt_of_small_bipartition (by omega) T hT X Y hpart hcover hsmallX R
  by_cases hsmallY : 10 * Y.card ≤ m
  · exact ramseyAt_of_small_bipartition (by omega) T hT Y X hpart.symm
      (by simpa only [Finset.union_comm] using hcover) hsmallY R
  have hXY : X.card + Y.card = m + 1 := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_coe.mp hpart.disjoint),
      hcover, Finset.card_univ, Fintype.card_fin]
  have hX : X.Nonempty := Finset.card_pos.mp (by omega)
  left
  apply isContained_of_bipartite_cross_degree T R hT X Y hpart hX A B hdis hA
  · intro a ha
    have hdeg := hAB a ha
    omega
  · intro b hb
    have hdeg := hBA b hb
    omega

end Erdos547

#print axioms Erdos547.ramsey_of_dense_bipartite_pair
