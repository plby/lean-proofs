import ErdosProblems.Erdos1010.Even
import ErdosProblems.Erdos1010.DenseOdd
import ErdosProblems.Erdos1010.Deletion

/-! # The exact triangle supersaturation theorem for every odd order -/

open Finset

namespace Erdos1010

theorem odd_triangles {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r t : ℕ}
    (hn : Fintype.card V = 2 * r + 1) (ht : t < r)
    (hm : G.edgeFinset.card = r * (r + 1) + t) : r * t ≤ (G.cliqueFinset 3).card := by
  classical
  by_cases ht0 : t = 0
  · simp [ht0]
  have htpos : 1 ≤ t := by omega
  have hr : 1 ≤ r := by omega
  have hpoly : r * (r + 1) + t = r ^ 2 + r + t := by ring
  by_cases hlow : ∃ v, G.degree v ≤ r
  · obtain ⟨v, hv⟩ := hlow
    let H := G.induce ({v}ᶜ : Set V)
    have hnH : Fintype.card {x : V // x ∈ ({v}ᶜ : Set V)} = 2 * r := by
      rw [card_compl_singleton_subtype, hn]
      omega
    have hmH : H.edgeFinset.card = r ^ 2 + r + t - G.degree v := by
      rw [card_induce_compl_singleton_edges, hm, hpoly]
    have htri : (H.cliqueFinset 3).card ≤ (G.cliqueFinset 3).card :=
      card_induce_compl_singleton_triangles_le G v
    by_cases hvt : G.degree v ≤ t
    · have hcount : r ^ 2 + (r - 1) ≤ H.edgeFinset.card := by omega
      obtain ⟨K, hKH, hKcard⟩ := exists_subgraph_card_edges H (r ^ 2 + (r - 1)) hcount
      have hmK : K.edgeFinset.card = r ^ 2 + (r - 1) := by
        have hc : K.edgeSet.ncard = K.edgeFinset.card := by
          rw [← K.coe_edgeFinset]
          exact Set.ncard_coe_finset _
        omega
      calc
        r * t ≤ r * (r - 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ (K.cliqueFinset 3).card := even_triangles K hnH (by omega) hmK
        _ ≤ (H.cliqueFinset 3).card :=
          card_le_card (SimpleGraph.cliqueFinset_mono (G := K) (H := H) hKH)
        _ ≤ _ := htri
    · let k := r + t - G.degree v
      have htk : t ≤ k := by dsimp [k]; omega
      have hkr : k < r := by dsimp [k]; omega
      have hmH' : H.edgeFinset.card = r ^ 2 + k := by dsimp [k]; omega
      calc
        r * t ≤ r * k := Nat.mul_le_mul_left _ htk
        _ ≤ (H.cliqueFinset 3).card := even_triangles H hnH hkr hmH'
        _ ≤ _ := htri
  · have hmin : ∀ v, r + 1 ≤ G.degree v := by
      intro v
      have hnle : ¬G.degree v ≤ r := fun h ↦ hlow ⟨v, h⟩
      omega
    obtain ⟨u, hu, htu⟩ := dense_odd_vertex G hn ht hm hmin
    let H := G.induce ({u}ᶜ : Set V)
    have hnH : Fintype.card {x : V // x ∈ ({u}ᶜ : Set V)} = 2 * r := by
      rw [card_compl_singleton_subtype, hn]
      omega
    have hmH : H.edgeFinset.card = r ^ 2 + (t - 1) := by
      rw [card_induce_compl_singleton_edges, hm, hpoly, hu]
      omega
    have htri := even_triangles H hnH (show t - 1 < r by omega) hmH
    have hpart := card_induce_compl_singleton_triangles_add G u
    have hmul : r * (t - 1) + r = r * t := by
      calc
        _ = r * ((t - 1) + 1) := by ring
        _ = _ := by rw [Nat.sub_add_cancel htpos]
    change (H.cliqueFinset 3).card + (trianglesAt G u).card = (G.cliqueFinset 3).card at hpart
    omega

end Erdos1010
