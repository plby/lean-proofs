import ErdosProblems.Erdos556.CoreCleaning
import ErdosProblems.Erdos556.MappedDensity

/-! A near-clique without a prescribed cycle cannot have substantially more vertices. -/

namespace Erdos556

open SimpleGraph Finset

theorem near_clique_order_bound_of_forbidden_cycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (n : ℕ) (hn : 8 ≤ n)
    (hno : ¬ cycleGraph n ⊑ G) :
    n * S.card ≤ n * n + 16 * Nat.card (Gᶜ.induce (S : Set V)).edgeSet := by
  classical
  let q := n / 4
  obtain ⟨A, hAS, hbad, hclean⟩ := exists_clean_core Gᶜ S q
  have hAn : A.card < n := by
    by_contra hlarge
    obtain ⟨C, hCA, hCc⟩ := exists_subset_card_eq (show n ≤ A.card by omega)
    have hCS : C ⊆ S := hCA.trans hAS
    have hCcore : ∀ v ∈ C, C.card ≤ (G.neighborFinset v ∩ C).card + (q + 1) :=
      dense_core_after_cleaning G C S q hCS (fun v hv => hclean v (hCA hv))
    obtain ⟨v, c, hc, hlen⟩ := exists_cycle_of_dense_core G C ∅ (q + 1)
      (by simp) (by simp only [card_empty, add_zero, hCc]; omega)
      (by simp only [card_empty, zero_add, hCc]; dsimp only [q]; omega) hCcore
      (by intro v hv; simp at hv)
    apply hno
    apply (cycleGraph_isContained_iff (by omega : 2 < n)).mpr
    exact ⟨v, c, hc, by simpa only [card_empty, add_zero, hCc] using hlen⟩
  have hq : n ≤ 8 * q := by dsimp only [q]; omega
  have hloss := Nat.mul_le_mul_right (S.card - A.card) hq
  rw [edgeFinset_card_eq_natCard_edgeSet] at hbad
  have hNl : n * (S.card - A.card) ≤ 16 * Nat.card (Gᶜ.induce (S : Set V)).edgeSet := by
    nlinarith only [hloss, hbad]
  have hAc := card_le_card hAS
  have hsum := Nat.sub_add_cancel hAc
  have hAn' := Nat.mul_le_mul_left n hAn.le
  nlinarith only [hNl, hsum, hAn']

#print axioms near_clique_order_bound_of_forbidden_cycle

end Erdos556
