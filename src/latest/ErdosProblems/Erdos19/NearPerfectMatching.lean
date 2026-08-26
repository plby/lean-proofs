import ErdosProblems.Erdos19.Vizing
import ErdosProblems.Erdos19.GraphMatching

/-! # Near-perfect matchings in almost regular graphs

The proved Vizing theorem gives the average color-class bound, and a maximum
matching is at least as large as every color class.
-/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem edge_count_le_palette_mul_maximum_matching (G : _root_.SimpleGraph V)
    (M : G.Subgraph)
    (hMmax : ∀ L : G.Subgraph, L.IsMatching → L.edgeSet.ncard ≤ M.edgeSet.ncard)
    (D : ℕ) (hmax : ∀ v, G.degree v ≤ D) :
    G.edgeSet.ncard ≤ (D + 1) * M.edgeSet.ncard := by
  classical
  obtain ⟨c, hc⟩ := Vizing.exists_proper_edgeLabeling G D hmax
  let L (a : Fin (D + 1)) : G.Subgraph :=
    { verts := (c.labelGraph a).support
      Adj := (c.labelGraph a).Adj
      adj_sub := fun h ↦ c.labelGraph_le h
      edge_vert := fun h ↦ ⟨_, h⟩
      symm := (c.labelGraph a).symm }
  have hL : ∀ a, (L a).IsMatching := by
    intro a v hv
    obtain ⟨w, hvw⟩ := hv
    refine ⟨w, hvw, ?_⟩
    intro z hvz
    obtain ⟨hvwG, hvwc⟩ := (EdgeLabeling.labelGraph_adj v w).mp hvw
    obtain ⟨hvzG, hvzc⟩ := (EdgeLabeling.labelGraph_adj v z).mp hvz
    exact hc v z w hvzG hvwG (hvzc.trans hvwc.symm)
  have hunion : (⋃ a : Fin (D + 1), (L a).edgeSet) = G.edgeSet := by
    ext e
    induction e using Sym2.inductionOn with
    | hf x y =>
      simp only [Set.mem_iUnion, Subgraph.mem_edgeSet, mem_edgeSet]
      change (∃ a, (c.labelGraph a).Adj x y) ↔ G.Adj x y
      constructor
      · rintro ⟨a, ha⟩
        exact c.labelGraph_le ha
      · intro hxy
        exact ⟨c.get x y hxy, (EdgeLabeling.labelGraph_adj x y).mpr ⟨hxy, rfl⟩⟩
  have hedge : G.edgeSet.ncard ≤ (D + 1) * M.edgeSet.ncard := by
    calc
      G.edgeSet.ncard = (⋃ a : Fin (D + 1), (L a).edgeSet).ncard := by rw [hunion]
      _ ≤ ∑ a : Fin (D + 1), (L a).edgeSet.ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _a : Fin (D + 1), M.edgeSet.ncard :=
        sum_le_sum (fun a _ ↦ hMmax (L a) (hL a))
      _ = (D + 1) * M.edgeSet.ncard := by simp
  exact hedge

theorem exists_maximum_matching_with_degree_bound (G : _root_.SimpleGraph V)
    (d D : ℕ) (hmin : ∀ v, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ D) :
    ∃ M : G.Subgraph, M.IsMatching ∧
      (∀ L : G.Subgraph, L.IsMatching → L.edgeSet.ncard ≤ M.edgeSet.ncard) ∧
      Fintype.card V * d ≤ (D + 1) * M.verts.ncard := by
  classical
  obtain ⟨M, hM, hMmax⟩ := exists_maximum_matching G
  have hedge := edge_count_le_palette_mul_maximum_matching G M hMmax D hmax
  have hdegree : Fintype.card V * d ≤ 2 * G.edgeSet.ncard := by
    calc
      Fintype.card V * d = ∑ _v : V, d := by simp
      _ ≤ ∑ v : V, G.degree v := sum_le_sum (fun v _ ↦ hmin v)
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ = 2 * G.edgeSet.ncard := by
        rw [edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard]
  have hverts := matching_verts_ncard_generic M hM
  refine ⟨M, hM, hMmax, ?_⟩
  rw [hverts]
  nlinarith only [hdegree, Nat.mul_le_mul_left 2 hedge]

theorem exists_maximum_matching_few_uncovered_of_degrees (G : _root_.SimpleGraph V)
    (d D : ℕ) (hmin : ∀ v, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ D) :
    ∃ M : G.Subgraph, M.IsMatching ∧
      (∀ L : G.Subgraph, L.IsMatching → L.edgeSet.ncard ≤ M.edgeSet.ncard) ∧
      M.vertsᶜ.ncard * (D + 1) ≤ Fintype.card V * (D + 1 - d) := by
  classical
  obtain ⟨M, hM, hMmax, hbound⟩ := exists_maximum_matching_with_degree_bound G d D hmin hmax
  refine ⟨M, hM, hMmax, ?_⟩
  have hsplit : M.vertsᶜ.ncard + M.verts.ncard = Fintype.card V := by
    rw [Set.ncard_compl, Nat.card_eq_fintype_card]
    apply Nat.sub_add_cancel
    have hs := Set.ncard_le_ncard (Set.subset_univ M.verts)
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hs
  by_cases hdD : d ≤ D + 1
  · have hp := congrArg (fun t ↦ t * (D + 1)) hsplit
    have hq := congrArg (fun t ↦ Fintype.card V * t) (Nat.sub_add_cancel hdD)
    nlinarith only [hbound, hp, hq]
  · have hV : IsEmpty V := ⟨fun v ↦ by have := (hmin v).trans (hmax v); omega⟩
    have hn : Fintype.card V = 0 := Fintype.card_eq_zero
    have hzero : M.vertsᶜ.ncard = 0 := by omega
    simp only [hzero, hn, zero_mul, le_refl]

#print axioms exists_maximum_matching_with_degree_bound
#print axioms exists_maximum_matching_few_uncovered_of_degrees

end Erdos19
