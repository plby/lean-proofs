import ErdosProblems.Erdos19.ActiveDiracMatching
import ErdosProblems.Erdos19.SubgraphLift
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! # Extending a protected matching through a large buffer -/

namespace Erdos19

open _root_.SimpleGraph

variable {V : Type*} [Fintype V]

theorem matching_covered_buffer_card_le {G : _root_.SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching) (B W : Set V) (hBW : Disjoint B W)
    (hcross : ∀ x y, M.Adj x y → (x ∈ B ∧ y ∈ W) ∨ (x ∈ W ∧ y ∈ B)) :
    (M.verts ∩ W).ncard ≤ B.ncard := by
  classical
  have hex : ∀ v : ↥(M.verts ∩ W), ∃ w ∈ B, M.Adj v.1 w := by
    intro v
    obtain ⟨w, hw, _⟩ := hM v.2.1
    rcases hcross v.1 w hw with h | h
    · exact (Set.disjoint_left.mp hBW h.1 v.2.2).elim
    · exact ⟨w, h.2, hw⟩
  choose mate hmateB hmate using hex
  let f : ↥(M.verts ∩ W) → B := fun v ↦ ⟨mate v, hmateB v⟩
  have hf : Function.Injective f := by
    intro v w h
    have heq : mate v = mate w := congrArg Subtype.val h
    have hv : M.Adj v.1 (mate w) := heq ▸ hmate v
    exact Subtype.ext (hM.eq_of_adj_right hv (hmate w))
  simpa only [Set.fintypeCard_eq_ncard] using Fintype.card_le_of_injective f hf

theorem exists_matching_extension_with_buffer
    (G : _root_.SimpleGraph V) (P : G.Subgraph) (hP : P.IsMatching)
    (A W : Set V) (heven : Even A.ncard) (hPA : P.verts ⊆ A) (hWA : W ⊆ A)
    (hWP : Disjoint W P.verts) (d : ℕ)
    (hroom : 2 * d + (A \ (P.verts ∪ W)).ncard ≤ W.ncard)
    (hmissing : ∀ x ∈ A \ P.verts, (W \ G.neighborSet x).ncard ≤ d) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = A ∧ P ≤ M ∧
      ∀ x y, M.Adj x y → P.Adj x y ∨ x ∈ W ∨ y ∈ W := by
  classical
  let B := A \ (P.verts ∪ W)
  have hBW : Disjoint B W := by
    apply Set.disjoint_left.mpr
    intro x hx hxW
    exact hx.2 (Or.inr hxW)
  let Q := G.between B W
  have hdegree : ∀ x ∈ B, B.ncard ≤ (Q.neighborSet x).ncard := by
    intro x hx
    have hxW : x ∉ W := fun h ↦ hx.2 (Or.inr h)
    have hneighbors : Q.neighborSet x = W ∩ G.neighborSet x := by
      ext y
      change (G.Adj x y ∧ (x ∈ B ∧ y ∈ W ∨ x ∈ W ∧ y ∈ B)) ↔ y ∈ W ∧ G.Adj x y
      simp only [hx, hxW, true_and, false_and, or_false, and_comm]
    have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard W (G.neighborSet x)
    have hmiss := hmissing x ⟨hx.1, fun h ↦ hx.2 (Or.inl h)⟩
    rw [hneighbors]
    change 2 * d + B.ncard ≤ W.ncard at hroom
    omega
  obtain ⟨N₀, hN₀, hBN₀⟩ := exists_matching_covering_of_neighbor_ncard_ge Q B hdegree
  let N := liftSubgraph (show Q ≤ G from between_le) N₀
  have hN : N.IsMatching := hN₀
  have hBN : B ⊆ N.verts := hBN₀
  have hcross : ∀ x y, N.Adj x y → (x ∈ B ∧ y ∈ W) ∨ (x ∈ W ∧ y ∈ B) := by
    intro x y hxy
    exact (show Q.Adj x y from (show N₀.Adj x y from hxy).adj_sub).2
  have hNverts : N.verts ⊆ B ∪ W := by
    intro x hx
    obtain ⟨y, hy, _⟩ := hN hx
    exact (hcross x y hy).elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)
  have hNA : N.verts ⊆ A := fun x hx ↦ (hNverts hx).elim And.left (hWA ·)
  have hPN : Disjoint P.verts N.verts := by
    apply Set.disjoint_left.mpr
    intro x hxP hxN
    rcases hNverts hxN with hxB | hxW
    · exact hxB.2 (Or.inl hxP)
    · exact Set.disjoint_left.mp hWP hxW hxP
  let M₀ := P ⊔ N
  have hM₀ : M₀.IsMatching := hP.sup hN (by
    simpa only [hP.support_eq_verts, hN.support_eq_verts] using hPN)
  have hM₀A : M₀.verts ⊆ A := Set.union_subset hPA hNA
  let T := A \ M₀.verts
  have hTW : T ⊆ W := by
    intro x hx
    by_contra hxW
    have hxB : x ∈ B := ⟨hx.1, fun h ↦ h.elim (fun hxP ↦ hx.2 (Or.inl hxP)) hxW⟩
    exact hx.2 (Or.inr (hBN hxB))
  have hWsub : W ⊆ T ∪ (N.verts ∩ W) := by
    intro x hxW
    by_cases hxN : x ∈ N.verts
    · exact Or.inr ⟨hxN, hxW⟩
    · exact Or.inl ⟨hWA hxW, fun h ↦ h.elim (fun hxP ↦ Set.disjoint_left.mp hWP hxW hxP) hxN⟩
  have hWcard : W.ncard ≤ T.ncard + B.ncard :=
    ((Set.ncard_le_ncard hWsub).trans (Set.ncard_union_le _ _)).trans
      (Nat.add_le_add_left (matching_covered_buffer_card_le N hN B W hBW hcross) _)
  have hTlarge : 2 * d ≤ T.ncard := by
    change 2 * d + B.ncard ≤ W.ncard at hroom
    omega
  have hTeven : Even T.ncard := by
    have hsplit := Set.ncard_sdiff_add_ncard_of_subset hM₀A
    have hverts := matching_verts_ncard_generic M₀ hM₀
    obtain ⟨k, hk⟩ := heven
    rw [Nat.even_iff]
    change T.ncard + M₀.verts.ncard = A.ncard at hsplit
    omega
  have hTdegree : ∀ x ∈ T, T.ncard ≤ 2 * (T ∩ G.neighborSet x).ncard := by
    intro x hx
    have hmiss := hmissing x ⟨hx.1, fun hxP ↦ hx.2 (Or.inl hxP)⟩
    have hmissT : (T \ G.neighborSet x).ncard ≤ d :=
      (Set.ncard_le_ncard (Set.sdiff_subset_sdiff_left hTW)).trans hmiss
    have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard T (G.neighborSet x)
    omega
  obtain ⟨L, hL, hLT⟩ := exists_matching_on_even_set_of_dense_induced G T hTeven hTdegree
  have hM₀L : Disjoint M₀.support L.support := by
    rw [hM₀.support_eq_verts, hL.support_eq_verts, hLT]
    exact Set.disjoint_sdiff_right
  refine ⟨M₀ ⊔ L, hM₀.sup hL hM₀L, ?_, le_trans le_sup_left le_sup_left, ?_⟩
  · change M₀.verts ∪ L.verts = A
    rw [hLT]
    apply Set.Subset.antisymm (Set.union_subset hM₀A Set.sdiff_subset)
    intro x hx
    by_cases hxM : x ∈ M₀.verts
    · exact Or.inl hxM
    · exact Or.inr ⟨hx, hxM⟩
  · intro x y hxy
    rcases hxy with (hPxy | hNxy) | hLxy
    · exact Or.inl hPxy
    · exact Or.inr ((hcross x y hNxy).elim (fun h ↦ Or.inr h.2) (fun h ↦ Or.inl h.1))
    · exact Or.inr (Or.inl (hTW (hLT ▸ hLxy.fst_mem)))

#print axioms exists_matching_extension_with_buffer

end Erdos19
