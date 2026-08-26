import ErdosProblems.Erdos745.ComponentCountUpper

/-! # Fixed-order non-tree component estimates -/

open scoped BigOperators

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

theorem connected_not_tree_card_edges {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hc : G.Connected) (hnt : ¬ G.IsTree) :
    Fintype.card V ≤ G.edgeSet.ncard := by
  have hle := hc.card_vert_le_card_edgeSet_add_one
  have hne : Nat.card G.edgeSet + 1 ≠ Nat.card V := by
    intro he
    exact hnt (SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hc, he⟩)
  rw [Nat.card_coe_set_eq, ← Fintype.card_eq_nat_card] at hle hne
  omega

def labelledGraphCount (k : ℕ) : ℕ := Nat.card (SimpleGraph (Fin k))

theorem sum_constant_graph_shapes {n : ℕ} (S : Finset (Fin n)) (a : ℝ) :
    (∑ _H : SimpleGraph S, a) = (labelledGraphCount S.card : ℝ) * a := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply congrArg (fun m : ℕ ↦ (m : ℝ) * a)
  rw [Fintype.card_eq_nat_card]
  calc
    _ = Nat.card (SimpleGraph (Fin (Fintype.card S))) :=
      Nat.card_congr (Fintype.equivFin S).simpleGraph
    _ = _ := by rw [Fintype.card_coe]; rfl

theorem probability_contains_shape (lam : ℝ) (n : ℕ) (S : Finset (Fin n))
    (H : SimpleGraph S) :
    probability lam n (fun G ↦ H ≤ G.induce (S : Set (Fin n))) =
      (edgeProbability lam n : ℝ) ^ H.edgeSet.ncard := by
  have h := probability_edge_cylinder lam n (edgeCoordinates (extendGraph S H)) ∅
    (Finset.disjoint_empty_right _)
  simpa only [Finset.disjoint_empty_left, and_true, Finset.card_empty, pow_zero,
    mul_one, edgeCoordinates_subset_iff_le, extendGraph_le_iff, card_edgeCoordinates,
    ncard_edgeSet_extendGraph] using h

def IsNonTreeComponentSet {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  IsComponentSet G S ∧ ¬ (G.induce (S : Set (Fin n))).IsTree

theorem probability_contains_nonTree_shape_le (lam : ℝ) (n : ℕ) (S : Finset (Fin n))
    (H : SimpleGraph S) :
    probability lam n (fun G ↦ H.Connected ∧ ¬ H.IsTree ∧ H ≤ G.induce (S : Set (Fin n))) ≤
      (edgeProbability lam n : ℝ) ^ S.card := by
  by_cases hH : H.Connected ∧ ¬ H.IsTree
  · have hcard : S.card ≤ H.edgeSet.ncard := by
      simpa only [Fintype.card_coe] using connected_not_tree_card_edges hH.1 hH.2
    calc
      _ ≤ probability lam n (fun G ↦ H ≤ G.induce (S : Set (Fin n))) :=
        probability_mono (fun _ hG ↦ hG.2.2)
      _ = _ := probability_contains_shape lam n S H
      _ ≤ _ := pow_le_pow_of_le_one (edgeProbability lam n).property.1
        (edgeProbability lam n).property.2 hcard
  · have hevent : (fun G : SimpleGraph (Fin n) ↦
        H.Connected ∧ ¬ H.IsTree ∧ H ≤ G.induce (S : Set (Fin n))) =
        (fun _ ↦ False) := by
      funext G
      apply propext
      exact ⟨fun h ↦ hH ⟨h.1, h.2.1⟩, False.elim⟩
    rw [hevent, probability_false]
    exact pow_nonneg (edgeProbability lam n).property.1 _

theorem probability_isNonTreeComponentSet_le (lam : ℝ) (n : ℕ) (S : Finset (Fin n)) :
    probability lam n (fun G ↦ IsNonTreeComponentSet G S) ≤
      (labelledGraphCount S.card : ℝ) * (edgeProbability lam n : ℝ) ^ S.card := by
  calc
    _ ≤ probability lam n (fun G ↦ ∃ H : SimpleGraph S,
        H.Connected ∧ ¬ H.IsTree ∧ H ≤ G.induce (S : Set (Fin n))) := by
      apply probability_mono
      intro G hG
      exact ⟨G.induce (S : Set (Fin n)),
        ((isComponentSet_iff_connected_closed G S).mp hG.1).1, hG.2, le_rfl⟩
    _ ≤ ∑ H : SimpleGraph S, probability lam n
        (fun G ↦ H.Connected ∧ ¬ H.IsTree ∧ H ≤ G.induce (S : Set (Fin n))) :=
      probability_exists_le _ _ _
    _ ≤ ∑ _H : SimpleGraph S, (edgeProbability lam n : ℝ) ^ S.card :=
      Finset.sum_le_sum (fun H _ ↦ probability_contains_nonTree_shape_le lam n S H)
    _ = _ := sum_constant_graph_shapes S _

theorem sum_probability_nonTree_components_le (lam : ℝ) (n k : ℕ) :
    (∑ S ∈ Finset.univ.powersetCard k, probability lam n (fun G ↦ IsNonTreeComponentSet G S)) ≤
      (n.choose k : ℝ) * labelledGraphCount k * (edgeProbability lam n : ℝ) ^ k := by
  calc
    _ ≤ ∑ S ∈ Finset.univ.powersetCard k,
        (labelledGraphCount S.card : ℝ) * (edgeProbability lam n : ℝ) ^ S.card :=
      Finset.sum_le_sum (fun S _ ↦ probability_isNonTreeComponentSet_le lam n S)
    _ = ∑ _S ∈ Finset.univ.powersetCard k,
        (labelledGraphCount k : ℝ) * (edgeProbability lam n : ℝ) ^ k := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring

/-- For fixed `k` the expected number of non-tree components is uniformly
bounded, hence their vertex fraction vanishes. -/
theorem sum_probability_nonTree_components_le_constant {lam : ℝ} {n : ℕ}
    (hlam : 0 ≤ lam) (hn : 0 < n) (hlamn : lam ≤ n) (k : ℕ) :
    (∑ S ∈ Finset.univ.powersetCard k, probability lam n (fun G ↦ IsNonTreeComponentSet G S)) ≤
      (labelledGraphCount k : ℝ) * lam ^ k := by
  apply (sum_probability_nonTree_components_le lam n k).trans
  rw [coe_edgeProbability hlam hn hlamn]
  have hchoose : (n.choose k : ℝ) ≤ (n : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow n k
  calc
    _ ≤ (n : ℝ) ^ k * labelledGraphCount k * (lam / n) ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hchoose (Nat.cast_nonneg _))
        (pow_nonneg (div_nonneg hlam (Nat.cast_nonneg _)) _)
    _ = _ := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [div_pow]
      field_simp

end

end Erdos745
