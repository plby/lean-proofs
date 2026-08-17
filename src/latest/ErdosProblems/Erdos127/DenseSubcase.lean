import ErdosProblems.Erdos127.HeavyHalf
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The dense-remainder subcase: split an even clique in half, putting all vertices
outside the clique opposite the heavier half.  The assumptions on `s` are stated
without division, so they express the real interval `u/4 ≤ s ≤ 3u/4` exactly. -/
theorem exists_bipartite_cut_of_clique_dense_remainder
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (hU : U.Nonempty) (heven : Even #U)
    (hclique : G.IsClique (U : Set V))
    (R s : ℕ) (hs_lo : #U ≤ 4 * s) (hs_hi : 4 * s ≤ 3 * #U)
    (hx : #(G.between (U : Set V) (Uᶜ : Finset V)).edgeFinset = R * #U + s) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H ≤ G ∧ H.IsBipartite ∧
      #U * #U + 2 * #(G.between (U : Set V) (Uᶜ : Finset V)).edgeFinset + #U / 2 ≤
        4 * #H.edgeFinset := by
  classical
  let W : Finset V := Uᶜ
  let K : SimpleGraph V := G.between (U : Set V) (W : Set V)
  let x : ℕ := #K.edgeFinset
  let d : V → ℕ := fun v ↦ K.degree v
  have hUW : Disjoint U W := by
    simpa only [W] using (disjoint_compl_right : Disjoint U Uᶜ)
  have hK : K.IsBipartiteWith U W := by
    simpa only [K, W, coe_compl] using
      (G.between_isBipartiteWith
        (s := (U : Set V)) (t := (U : Set V)ᶜ) disjoint_compl_right)
  have hsumd : ∑ v ∈ U, d v = x := by
    simpa only [d, x] using K.isBipartiteWith_sum_degrees_eq_card_edges hK
  have hx' : x = R * #U + s := by simpa only [x, K, W] using hx
  have hs_lt : s < #U := by
    have hu_pos := hU.card_pos
    omega
  obtain ⟨A, hAU, hAcard, hheavy⟩ :=
    Finset.exists_half_sum_two_ge_add_min U d hU heven hs_lt hsumd hx'
  let H : SimpleGraph V := G.between (A : Set V) (Aᶜ : Finset V)
  have hHbip : H.IsBipartite := by
    simpa only [H, coe_compl] using
      (G.between_isBipartite (s := (A : Set V)) (t := (A : Set V)ᶜ) disjoint_compl_right)
  have hHA : H.IsBipartiteWith A (Aᶜ : Finset V) := by
    simpa only [H, coe_compl] using
      (G.between_isBipartiteWith
        (s := (A : Set V)) (t := (A : Set V)ᶜ) disjoint_compl_right)
  have hmin : #U / 2 ≤ 2 * min s (#U - s) := by
    have hsU : s ≤ #U := hs_lt.le
    rcases le_total s (#U - s) with hle | hle
    · rw [min_eq_left hle]
      omega
    · rw [min_eq_right hle]
      omega
  have hdeg (a : V) (ha : a ∈ A) :
      #(U \ A) + d a ≤ H.degree a := by
    have haU : a ∈ U := hAU ha
    have hKsub : K.neighborFinset a ⊆ W :=
      K.isBipartiteWith_neighborFinset_subset hK haU
    have hdisj : Disjoint (U \ A) (K.neighborFinset a) := by
      apply Finset.disjoint_left.mpr
      intro v hvU hvK
      have hvW := hKsub hvK
      exact (Finset.disjoint_left.mp hUW (mem_sdiff.mp hvU).1 hvW)
    have hsub : (U \ A) ∪ K.neighborFinset a ⊆ H.neighborFinset a := by
      intro v hv
      rw [mem_union] at hv
      rw [mem_neighborFinset]
      change G.Adj a v ∧
        (a ∈ (A : Set V) ∧ v ∈ (Aᶜ : Finset V) ∨
          a ∈ (Aᶜ : Finset V) ∧ v ∈ (A : Set V))
      rcases hv with hv | hv
      · have hvU : v ∈ U := (mem_sdiff.mp hv).1
        have hvA : v ∉ A := (mem_sdiff.mp hv).2
        have hav : a ≠ v := fun hav ↦ hvA (hav ▸ ha)
        exact ⟨hclique haU hvU hav, Or.inl ⟨ha, by simpa using hvA⟩⟩
      · have hKav : K.Adj a v := by simpa only [mem_neighborFinset] using hv
        have hvW : v ∈ W := hKsub hv
        have hvU : v ∉ U := by simpa only [W, mem_compl] using hvW
        have hvA : v ∉ A := fun hvA ↦ hvU (hAU hvA)
        have hGav : G.Adj a v := by
          change G.Adj a v ∧ _ at hKav
          exact hKav.1
        exact ⟨hGav, Or.inl ⟨ha, by simpa using hvA⟩⟩
    have hcard := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_neighborFinset_eq_degree,
      card_neighborFinset_eq_degree] at hcard
    exact hcard
  have hcut_lower : #A * #(U \ A) + (∑ a ∈ A, d a) ≤ #H.edgeFinset := by
    calc
      #A * #(U \ A) + (∑ a ∈ A, d a) =
          ∑ a ∈ A, (#(U \ A) + d a) := by
            simp [sum_add_distrib]
      _ ≤ ∑ a ∈ A, H.degree a := by
            exact sum_le_sum fun a ha ↦ hdeg a ha
      _ = #H.edgeFinset := H.isBipartiteWith_sum_degrees_eq_card_edges hHA
  have hUtwo : 2 * (#U / 2) = #U := Nat.two_mul_div_two_of_even heven
  have hdiffcard : #(U \ A) = #U / 2 := by
    rw [card_sdiff_of_subset hAU, hAcard]
    omega
  refine ⟨H, inferInstance, G.between_le, hHbip, ?_⟩
  have hheavy' : x + min s (#U - s) ≤ 2 * ∑ a ∈ A, d a := hheavy
  rw [hAcard, hdiffcard] at hcut_lower
  have hxdef : x = #(G.between (U : Set V) (Uᶜ : Finset V)).edgeFinset := by
    simp only [x, K, W]
  rw [← hxdef]
  nlinarith

end SimpleGraph

