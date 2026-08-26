import ErdosProblems.Erdos547.DenseCrossAbsorption
import ErdosProblems.Erdos547.SparseCross
import ErdosProblems.Erdos547.Unbalanced

/-!
# The near-clique case of the Ramsey embedding argument

All numerical estimates are integral. The coarse constant `20000` leaves
room for the floor in the sparse-pair pruning threshold.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph BigOperators

open scoped Classical in
theorem exists_tree_bipartition {U : Type*} [Fintype U] [Nontrivial U]
    (T : SimpleGraph U) (hT : T.IsTree) :
    ∃ X Y : Finset U, T.IsBipartiteWith (X : Set U) (Y : Set U) ∧ X ∪ Y = Finset.univ := by
  classical
  obtain ⟨X, Y, hpart⟩ := hT.isBipartite.exists_isBipartiteWith
  refine ⟨X.toFinset, Y.toFinset, by simpa using hpart, ?_⟩
  ext v
  simp only [Finset.mem_union, Set.mem_toFinset, Finset.mem_univ, iff_true]
  have hpos := hT.connected.preconnected.degree_pos_of_nontrivial v
  have hv := (T.degree_pos_iff_mem_support v).mp hpos
  exact isBipartiteWith_support_subset hpart hv

open scoped Classical in
/-- A monochromatic near-clique of order at most `m` forces the Ramsey
conclusion once `m` is at least `20000` times its degree deficit. -/
theorem ramsey_of_near_clique {m : ℕ} (T : SimpleGraph (Fin (m + 1)))
    (hT : T.IsTree) (R : SimpleGraph (Fin (2 * m))) (d : ℕ)
    (hd : 0 < d) (hm : 20000 * d ≤ m)
    (A : Finset (Fin (2 * m))) (hA : A.Nonempty) (hAsize : A.card ≤ m)
    (hAdeg : ∀ z ∈ A, m ≤ degreeIn R A z + d) : T ⊑ R ∨ T ⊑ Rᶜ := by
  classical
  have hm2 : 2 ≤ m := by omega
  let : Nontrivial (Fin (m + 1)) := Fintype.one_lt_card_iff_nontrivial.mp (by
    simp only [Fintype.card_fin]; omega)
  obtain ⟨X, Y, hpart, hcover⟩ := exists_tree_bipartition T hT
  have hcover : X ∪ Y = Finset.univ := by
    simpa only [Finset.ext_iff, Finset.mem_union] using hcover
  by_cases hsmallX : 10 * X.card ≤ m
  · exact ramseyAt_of_small_bipartition hm2 T hT X Y hpart hcover hsmallX R
  by_cases hsmallY : 10 * Y.card ≤ m
  · exact ramseyAt_of_small_bipartition hm2 T hT Y X hpart.symm
      (by simpa only [Finset.union_comm] using hcover) hsmallY R
  have hXY : X.card + Y.card = m + 1 := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_coe.mp hpart.disjoint),
      hcover, Finset.card_univ, Fintype.card_fin]
  let W := (Finset.univ : Finset (Fin (2 * m))) \ A
  have hdis : Disjoint A W := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzW
    exact (Finset.mem_sdiff.mp hzW).2 hzA
  have hAW : A.card + W.card = 2 * m := by
    have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin (2 * m))) A
    simpa [W, Nat.add_comm] using h
  have hAlo : m + 1 ≤ A.card + d := by
    obtain ⟨z, hz⟩ := hA
    have hdeg := hAdeg z hz
    have hbound := degreeIn_add_one_le_card R A hz
    omega
  have hWlo : m ≤ W.card := by omega
  have hWsize : W.card ≤ m + d := by omega
  by_cases hcross : 20 * (d : ℝ) * m < ∑ a ∈ A, (degreeIn R W a : ℝ)
  · exact Or.inl (isContained_of_dense_cross_edges T R hT d m hd (by omega)
      (Fintype.card_fin (m + 1)) A W hdis hAsize hWsize hAdeg hcross)
  let t := m / 25
  have htupper : 25 * t ≤ m := Nat.mul_div_le m 25
  have htlower : m ≤ 26 * t := by dsimp [t]; omega
  have hbudgetNat : 20 * d * m ≤ t ^ 2 := by
    have hmul := Nat.mul_le_mul_right m hm
    have hsq := Nat.mul_self_le_mul_self htlower
    nlinarith
  have hbudget : (∑ a ∈ A, degreeIn R W a) ≤ t ^ 2 := by
    have hreal : (∑ a ∈ A, (degreeIn R W a : ℝ)) ≤ (20 * d * m : ℕ) := by
      push_cast
      exact le_of_not_gt hcross
    have hnat : (∑ a ∈ A, degreeIn R W a) ≤ 20 * d * m := by exact_mod_cast hreal
    exact hnat.trans hbudgetNat
  obtain ⟨P, hPA, Q, hQW, hPsize, _, hPdeg, hQdeg⟩ :=
    prune_sparse_cross_pair R A W hdis t hbudget
  have hP : P.Nonempty := Finset.card_pos.mp (by omega)
  have hX : X.Nonempty := Finset.card_pos.mp (by omega)
  right
  apply isContained_of_bipartite_cross_degree T Rᶜ hT X Y hpart hX P Q
    (hdis.mono hPA hQW) hP
  · intro p hp
    have hdeg : W.card ≤ degreeIn Rᶜ Q p + 2 * t := by
      convert hPdeg p hp using 1
      congr 2
    omega
  · intro q hq
    have hdeg : A.card ≤ degreeIn Rᶜ P q + 2 * t := by
      convert hQdeg q hq using 1
      congr 2
    omega

end Erdos547

#print axioms Erdos547.ramsey_of_near_clique
