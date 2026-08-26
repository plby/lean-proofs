import ErdosProblems.Erdos73.OddCycleSeparator
import ErdosProblems.Erdos73.OddTerminalPaths
import ErdosProblems.Erdos73.HavenRegions

/-! Nested order-one cuts extract disjoint odd cycles from an odd haven. -/

namespace Erdos73.BrambleHaven
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {β : Finset (Finset V)} {q : ℕ}

theorem exists_oddCycle_list_of_hitting (h : BrambleHaven G β q) (N X : Finset V)
    {u : ℕ} (huq : u ≤ q) (hX : HitsOddTerminalPaths G N X)
    (hodd : ∀ K, ¬ (G.induce (h.region K : Set V)).IsBipartite)
    (htouch : ∀ K, K.val.card < u → ∃ v ∈ h.region K, v ∈ N)
    (p : ℕ) (K : {Y : Finset V // Y.card < q}) (hXK : X ⊆ K.val)
    (hbudget : K.val.card + p < u) :
    ∃ cs : List G.Subgraph, cs.length = p ∧
      (∀ H ∈ cs, IsOddCycleSubgraph H) ∧
      (∀ H ∈ cs, H.verts ⊆ (h.region K : Set V)) ∧
      cs.Pairwise (fun H J => Disjoint H.verts J.verts) := by
  induction p generalizing K with
  | zero => exact ⟨[], rfl, by simp, by simp, List.Pairwise.nil⟩
  | succ p ih =>
    have hRX : Disjoint (h.region K) X := (h.avoids K).mono_right hXK
    obtain ⟨H, hH, hHR, Y, hYR, hYcard, hsep⟩ :=
      exists_oddCycle_region_separator N (h.region K) (hodd K)
        (no_oddTerminalPath_in_region_of_hitting hX hRX)
    have hcard : (K.val ∪ Y).card ≤ K.val.card + 1 :=
      (card_union_le _ _).trans (Nat.add_le_add_left hYcard _)
    have hnext : (K.val ∪ Y).card + p < u := by omega
    let L : {Y : Finset V // Y.card < q} := ⟨K.val ∪ Y, by omega⟩
    have hKL : K.val ⊆ L.val := subset_union_left
    have hRL : h.region L ⊆ h.region K := h.antitone K L hKL
    have hLY : Disjoint (h.region L) Y := (h.avoids L).mono_right subset_union_right
    have hLN : ∃ v ∈ h.region L, v ∈ N := htouch L (by dsimp only [L]; omega)
    have hdisH : Disjoint (h.region L : Set V) H.verts :=
      hsep (h.region L) hRL (h.connected L) hLY hLN
    obtain ⟨cs, hlen, hcodd, hcR, hpair⟩ := ih L (hXK.trans hKL) hnext
    refine ⟨H :: cs, by simp [hlen], ?_, ?_, ?_⟩
    · intro J hJ
      rcases List.mem_cons.mp hJ with rfl | hJ
      · exact hH
      · exact hcodd J hJ
    · intro J hJ
      rcases List.mem_cons.mp hJ with rfl | hJ
      · exact hHR
      · exact (hcR J hJ).trans hRL
    · apply List.Pairwise.cons ?_ hpair
      intro J hJ
      exact hdisH.symm.mono_right (hcR J hJ)

theorem odd_terminal_paths_or_odd_cycles (h : BrambleHaven G β q)
    (N : Finset V) (k p u : ℕ) (hk : 1 ≤ k) (hu : 2 * k + p ≤ u) (huq : u ≤ q)
    (hodd : ∀ K, ¬ (G.induce (h.region K : Set V)).IsBipartite)
    (htouch : ∀ K, K.val.card < u → ∃ v ∈ h.region K, v ∈ N) :
    HasOddTerminalPathPacking G N k ∨ HasOddCyclePacking p G := by
  rcases odd_terminal_paths_packing_or_covering G N k with hpack | ⟨X, hcard, hX⟩
  · exact Or.inl hpack
  · have hbudget : X.card + p < u := by omega
    let K : {Y : Finset V // Y.card < q} := ⟨X, by omega⟩
    obtain ⟨cs, hlen, hoddcs, _, hpair⟩ :=
      h.exists_oddCycle_list_of_hitting N X huq hX hodd htouch p K subset_rfl hbudget
    exact Or.inr (hlen ▸ hasOddCyclePacking_of_pairwise_oddCycleSubgraphs cs hoddcs hpair)

end
end Erdos73.BrambleHaven
