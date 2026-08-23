import ErdosProblems.Erdos1105.CoreStability
import ErdosProblems.Erdos1105.CliquePaths

namespace Erdos1105

open SimpleGraph Finset

theorem cone_clique_card_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    {u : V} {k : ℕ} (hG : NoLongCycle G k) (hk : 3 ≤ k)
    (hn : k ≤ Fintype.card V) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    {S : Finset V} (hS : G.IsClique (S : Set V))
    (hcard : 3 ≤ S.card) (huS : u ∈ S) : S.card ≤ k - 2 := by
  classical
  have hlt := clique_card_lt_of_no_long_cycle G hG hk hS
  have hout : ∃ w, w ∉ S := by
    by_contra! h
    have heq : S = univ := eq_univ_of_forall h
    rw [heq, card_univ] at hlt
    omega
  obtain ⟨z, q, hq, hlen⟩ := cone_clique_extended_cycle G hu hconn hS hcard huS hout
  have h := hG z q hq
  omega

/-- Kopylov's core dichotomy, specialized to cones. The nonempty core has
order between `d+2` and `k-2` and is unchanged at threshold `k-r`. -/
theorem saturated_cone_core_dichotomy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {u : V} {k d : ℕ}
    (hG : NoLongCycle G k) (hk : 3 ≤ k) (hn : k ≤ Fintype.card V)
    (hu : G.IsUniversal u) (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (hmax : ∀ J : SimpleGraph V, G ≤ J → NoLongCycle J k → J = G)
    (hd₁ : 1 ≤ d) (hd₂ : k ≤ 2 * (d + 1)) :
    vertexCore G d = ∅ ∨
      (d + 2 ≤ (vertexCore G d).card ∧ (vertexCore G d).card ≤ k - 2 ∧
        G.IsClique (vertexCore G d : Set V) ∧
        vertexCore G (k - (vertexCore G d).card) = vertexCore G d) := by
  classical
  by_cases hempty : vertexCore G d = ∅
  · exact Or.inl hempty
  · have hne := nonempty_iff_ne_empty.mpr hempty
    have hclique := saturated_cone_core_isClique G hG hk hu hconn hmax hd₂
    have hlow := vertexCore_card_lower G d hne
    have huH := universal_mem_vertexCore G d hne hu
    have hupp := cone_clique_card_le G hG hk hn hu hconn hclique (by omega) huH
    exact Or.inr ⟨hlow, hupp, hclique,
      saturated_cone_core_stable G hG hk hu hconn hmax hclique hne
        (by omega) (by omega)⟩

theorem saturated_cone_edge_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u : V} {k d : ℕ}
    (hG : NoLongCycle G k) (hk : 3 ≤ k) (hn : k ≤ Fintype.card V)
    (hu : G.IsUniversal u) (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (hmax : ∀ J : SimpleGraph V, G ≤ J → NoLongCycle J k → J = G)
    (hd₁ : 1 ≤ d) (hd₂ : k ≤ 2 * (d + 1)) :
    G.edgeFinset.card ≤ d.choose 2 + d * (Fintype.card V - d) ∨
      ∃ r, d + 2 ≤ r ∧ r ≤ k - 2 ∧
        G.edgeFinset.card ≤ r.choose 2 + (k - r) * (Fintype.card V - r) := by
  rcases saturated_cone_core_dichotomy G hG hk hn hu hconn hmax hd₁ hd₂ with h | h
  · exact Or.inl (edges_le_of_core_empty G d h)
  · refine Or.inr ⟨(vertexCore G d).card, h.1, h.2.1, ?_⟩
    have hb := edges_le_core_bound G (k - (vertexCore G d).card)
    rwa [h.2.2.2] at hb

end Erdos1105

#print axioms Erdos1105.saturated_cone_edge_bound
