import Arxiv.Arxiv2411_18291.PairNeighbors

/-! # Degree bounds force a large maximum matching -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V]

theorem card_pair_inter_indicator (S : Finset V) {a b : V} (hab : a ≠ b) :
    ({a, b} ∩ S).card = (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0) := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb, hab]

theorem IsMaximumVertexPacking.crossed_neighbor_indicators_le {H D : Finset (Block V 2)}
    (hD : IsMaximumVertexPacking H D) {P : Block V 2} (hP : P ∈ D)
    {u v a b : V} (hu : u ∉ vertexSupport D) (hv : v ∉ vertexSupport D)
    (huv : u ≠ v) (ha : a ∈ P.val) (hb : b ∈ P.val) (hab : a ≠ b) :
    (if a ∈ pairNeighbors H u then 1 else 0) +
      (if b ∈ pairNeighbors H v then 1 else 0) ≤ (1 : ℕ) := by
  by_cases hua : a ∈ pairNeighbors H u
  · by_cases hvb : b ∈ pairNeighbors H v
    · exact (hD.no_cross hP hu hv huv ha hb hab
        ((mem_pairNeighbors H u a).mp hua) ((mem_pairNeighbors H v b).mp hvb)).elim
    · simp only [if_pos hua, if_neg hvb, add_zero, le_refl]
  · simp only [if_neg hua, zero_add]
    split_ifs <;> omega

theorem IsMaximumVertexPacking.neighbors_on_pair_le {H D : Finset (Block V 2)}
    (hD : IsMaximumVertexPacking H D) {P : Block V 2} (hP : P ∈ D)
    {u v : V} (hu : u ∉ vertexSupport D) (hv : v ∉ vertexSupport D) (huv : u ≠ v) :
    (P.val ∩ pairNeighbors H u).card + (P.val ∩ pairNeighbors H v).card ≤ 2 := by
  obtain ⟨a, b, hab, hPval⟩ := card_eq_two.mp P.property
  have ha : a ∈ P.val := by simp [hPval]
  have hb : b ∈ P.val := by simp [hPval]
  have h₁ := hD.crossed_neighbor_indicators_le hP hu hv huv ha hb hab
  have h₂ := hD.crossed_neighbor_indicators_le hP hu hv huv hb ha hab.symm
  rw [hPval, card_pair_inter_indicator _ hab, card_pair_inter_indicator _ hab]
  omega

theorem IsMaximumVertexPacking.degree_sum_le {H D : Finset (Block V 2)}
    (hD : IsMaximumVertexPacking H D) {u v : V}
    (hu : u ∉ vertexSupport D) (hv : v ∉ vertexSupport D) (huv : u ≠ v) :
    (H.filter fun Q => u ∈ Q.val).card + (H.filter fun Q => v ∈ Q.val).card ≤
      2 * D.card := by
  rw [← card_pairNeighbors, ← card_pairNeighbors,
    hD.packing.card_eq_sum_inter (hD.neighbors_subset_support hu),
    hD.packing.card_eq_sum_inter (hD.neighbors_subset_support hv), ← sum_add_distrib]
  calc
    _ ≤ ∑ _P ∈ D, 2 := sum_le_sum fun P hP => hD.neighbors_on_pair_le hP hu hv huv
    _ = _ := by simp [mul_comm]

theorem exists_pair_packing_leave_bound (S : Finset V) (H : Finset (Block V 2))
    (hHS : ∀ Q ∈ H, Q.val ⊆ S) (δ : ℝ)
    (hdegree : ∀ u ∈ S, δ ≤ ((H.filter fun Q => u ∈ Q.val).card : ℝ)) :
    ∃ D : Finset (Block V 2), D ⊆ H ∧ IsVertexPacking D ∧
      ((S \ vertexSupport D).card : ℝ) ≤ max 1 ((S.card : ℝ) - 2 * δ) := by
  obtain ⟨D, hD⟩ := exists_maximum_vertex_packing H
  refine ⟨D, hD.subset, hD.packing, ?_⟩
  by_cases hsmall : (S \ vertexSupport D).card ≤ 1
  · exact (by exact_mod_cast hsmall : ((S \ vertexSupport D).card : ℝ) ≤ 1).trans
      (le_max_left _ _)
  · obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp (by omega : 1 < (S \ vertexSupport D).card)
    obtain ⟨huS, huD⟩ := mem_sdiff.mp hu
    obtain ⟨hvS, hvD⟩ := mem_sdiff.mp hv
    have hsum : ((H.filter fun Q => u ∈ Q.val).card : ℝ) +
        ((H.filter fun Q => v ∈ Q.val).card : ℝ) ≤ 2 * (D.card : ℝ) := by
      exact_mod_cast hD.degree_sum_le huD hvD huv
    have hmatched : δ ≤ (D.card : ℝ) := by
      have hu := hdegree u huS
      have hv := hdegree v hvS
      linarith only [hu, hv, hsum]
    have hsub : vertexSupport D ⊆ S := by
      intro x hx
      obtain ⟨Q, hQ, hxQ⟩ := mem_biUnion.mp hx
      exact hHS Q (hD.subset hQ) hxQ
    have hcard : ((S \ vertexSupport D).card : ℝ) = (S.card : ℝ) - 2 * D.card := by
      rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub),
        hD.packing.card_vertexSupport, Nat.cast_mul, Nat.cast_ofNat]
      ring
    apply le_trans _ (le_max_right _ _)
    rw [hcard]
    linarith only [hmatched]

end Arxiv2411_18291
