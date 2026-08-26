import ErdosProblems.Erdos19.PairColoring
import ErdosProblems.Erdos19.MatchingColorCompletion
import ErdosProblems.Erdos19.MatchingPackingAvoidance

/-! # Completing the graph part of a partially colored hypergraph -/

namespace Erdos19.SetHypergraph

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem edgeColorable_of_avoiding_matching_family {V : Type*} [Fintype V]
    (H J : SetHypergraph V) (hJH : J ⊆ H)
    (hrest : ∀ e : H, e.1 ∉ J → e.1.ncard = 2) (m D : ℕ)
    (large : J.EdgeColoring (Fin m)) (M : Fin m → H.twoGraph.Subgraph)
    (hM : ∀ i, (M i).IsMatching)
    (hdis : Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe))
    (havoid : ∀ e : J, ∀ x ∈ e.1, x ∉ (M (large.color e)).verts)
    (hbudget : ∀ v, (H.twoGraph.neighborSet v).ncard +
      (∑ i : Fin m, if v ∈ (M i).verts then 0 else 1) ≤ D + m) :
    H.EdgeColorable (m + (D + 1)) := by
  obtain ⟨pairs, hpairs, hclasses⟩ := exists_edgeLabeling_completing_matchings
    H.twoGraph M hM hdis D (by simpa only [Fintype.card_fin] using hbudget)
  obtain ⟨color⟩ := H.edgeColoring_of_large_part_and_pairLabeling J hJH hrest large pairs hpairs (by
    intro e x hx y hxy hcolor
    have hclass := hclasses ⟨s(x, y), hxy⟩ (large.color e) hcolor
    have hadj : (M (large.color e)).Adj x y := Subgraph.mem_edgeSet.mp hclass
    exact havoid e x hx hadj.fst_mem)
  refine ⟨⟨fun e ↦ finSumFinEquiv (color.color e), ?_⟩⟩
  intro e f hef hinter heq
  exact color.valid hef hinter (finSumFinEquiv.injective heq)

theorem eventually_extend_coloring_with_sparse_classes (zeta : ℝ) (hzeta : 0 < zeta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H J : SetHypergraph (Fin n), J ⊆ H →
      (∀ e : H, e.1 ∉ J → e.1.ncard = 2) →
      (∀ v, (1 - delta) * n ≤ (H.twoGraph.degree v : ℝ)) →
      ∀ m : ℕ, (m : ℝ) ≤ (1 - zeta) * n →
      ∀ large : J.EdgeColoring (Fin m), ∀ U : Set (Fin n), ∀ C : Fin m → Set (Fin n),
      (∀ e : J, e.1 ⊆ C (large.color e)) →
      (∀ i, C i ⊆ U) → (∀ i, m + (C i).ncard ≤ U.ncard) →
      (∀ i, ((C i).ncard : ℝ) ≤ delta * n) →
      (∀ v, ((∑ i : Fin m, (if v ∈ C i then 1 else 0) : ℕ) : ℝ) ≤ delta * n) →
      (∀ v, (H.twoGraph.neighborSet v).ncard +
        (∑ i : Fin m, if v ∈ C i then 1 else 0) + (if v ∈ U then 1 else 0) ≤ n - 1) →
      H.EdgeColorable n := by
  classical
  obtain ⟨delta, hd, N₀, hN₀⟩ := eventually_matching_packing_avoiding zeta hzeta
  refine ⟨delta, hd, max N₀ 1, ?_⟩
  intro n hn H J hJH hrest hG m hm large U C hcovered hCU hroom hsmall habs hbudget
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hmn : m < n := by
    have hprod := mul_pos hzeta hnR
    have h : (m : ℝ) < n := by nlinarith only [hm, hprod]
    exact_mod_cast h
  obtain ⟨M, hM, hdis, hcnt⟩ := hN₀ n ((le_max_left _ _).trans hn) H.twoGraph hG
    m hm U C hCU hroom hsmall habs
  have havoid : ∀ e : J, ∀ x ∈ e.1, x ∉ (M (large.color e)).verts := by
    intro e x hx hMx
    exact (hM (large.color e)).2 hMx (hcovered e hx)
  have hbudgetM : ∀ v, (H.twoGraph.neighborSet v).ncard +
      (∑ i : Fin m, if v ∈ (M i).verts then 0 else 1) ≤ (n - m - 1) + m := by
    intro v
    have hb := hbudget v
    have hc := hcnt v
    omega
  have hcolor := H.edgeColorable_of_avoiding_matching_family J hJH hrest m (n - m - 1)
    large M (fun i ↦ (hM i).1) hdis havoid hbudgetM
  have hpalette : m + (n - m - 1 + 1) = n := by omega
  simpa only [hpalette] using hcolor

#print axioms eventually_extend_coloring_with_sparse_classes

end Erdos19.SetHypergraph
