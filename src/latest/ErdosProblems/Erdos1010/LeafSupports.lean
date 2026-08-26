import Mathlib

/-! # Two leaves with distinct supports in a sparse graph -/

open Finset

namespace Erdos1010

theorem exists_distinct_leaf_supports {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 1 ≤ G.degree v) (hedge : G.edgeFinset.card + 2 ≤ Fintype.card V) :
    ∃ u₁ u₂ w₁ w₂, G.degree u₁ = 1 ∧ G.degree u₂ = 1 ∧
      G.Adj u₁ w₁ ∧ G.Adj u₂ w₂ ∧ w₁ ≠ w₂ := by
  let L := (univ : Finset V).filter fun v ↦ G.degree v = 1
  have hsumL : (∑ v ∈ L, G.degree v) = L.card := by
    calc
      _ = ∑ _v ∈ L, 1 := sum_congr rfl fun v hv ↦ (mem_filter.mp hv).2
      _ = _ := by simp
  have hnonleaf : ∀ v ∈ Lᶜ, 2 ≤ G.degree v := by
    intro v hv
    have hn : G.degree v ≠ 1 := by simpa [L] using (mem_compl.mp hv)
    have := hmin v
    omega
  have hsumLc : 2 * Lᶜ.card ≤ ∑ v ∈ Lᶜ, G.degree v := by
    calc
      _ = ∑ _v ∈ Lᶜ, 2 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum hnonleaf
  have hsum : (∑ v ∈ L, G.degree v) + (∑ v ∈ Lᶜ, G.degree v) = 2 * G.edgeFinset.card := by
    rw [sum_add_sum_compl]
    exact G.sum_degrees_eq_twice_card_edges
  have hcard := card_add_card_compl L
  have hL4 : 4 ≤ L.card := by omega
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < L.card by omega)
  have hdu := (mem_filter.mp hu).2
  obtain ⟨w, huw, hwuniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdu
  by_contra hnone
  have hcommon : ∀ z, G.degree z = 1 → ∀ v, G.Adj z v → v = w := by
    intro z hz v hzv
    by_contra hvw
    exact hnone ⟨u, z, w, v, hdu, hz, huw, hzv, Ne.symm hvw⟩
  have hLN : L ⊆ G.neighborFinset w := by
    intro z hz
    have hdz := (mem_filter.mp hz).2
    obtain ⟨v, hzv, hvuniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdz
    rw [hcommon z hdz v hzv] at hzv
    exact (G.mem_neighborFinset w z).mpr hzv.symm
  have hwL : w ∉ L := by
    intro hw
    exact ((G.mem_neighborFinset w w).mp (hLN hw)).ne rfl
  have hdw : L.card ≤ G.degree w := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using card_le_card hLN
  have hwLc : w ∈ Lᶜ := mem_compl.mpr hwL
  have hrest : 2 * (Lᶜ.erase w).card ≤ ∑ v ∈ Lᶜ.erase w, G.degree v := by
    calc
      _ = ∑ _v ∈ Lᶜ.erase w, 2 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun v hv ↦ hnonleaf v (mem_of_mem_erase hv)
  have hrestsum := sum_erase_add Lᶜ (fun v ↦ G.degree v) hwLc
  have hrestcard := card_erase_of_mem hwLc
  omega

lemma adj_iff_eq_of_degree_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u w : V) (hu : G.degree u = 1) (huw : G.Adj u w)
    (v : V) : G.Adj u v ↔ v = w := by
  obtain ⟨z, huz, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hu
  have hwz := huniq w huw
  constructor
  · intro huv
    exact (huniq v huv).trans hwz.symm
  · rintro rfl
    exact huw

end Erdos1010
