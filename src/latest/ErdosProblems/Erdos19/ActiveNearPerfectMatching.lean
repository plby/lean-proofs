import ErdosProblems.Erdos19.MaximumMatchingCoverage

/-! # Near-perfect matchings measured on a prescribed vertex set -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem maximum_matching_degree_bound_on (G : _root_.SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching)
    (hMmax : ∀ L : G.Subgraph, L.IsMatching → L.edgeSet.ncard ≤ M.edgeSet.ncard)
    (A : Set V) (d D : ℕ) (hmin : ∀ v ∈ A, d ≤ G.degree v)
    (hmax : ∀ v, G.degree v ≤ D) :
    A.ncard * d ≤ (D + 1) * M.verts.ncard := by
  classical
  have hedge := edge_count_le_palette_mul_maximum_matching G M hMmax D hmax
  have hdegree : A.ncard * d ≤ 2 * G.edgeSet.ncard := by
    calc
      A.ncard * d = ∑ _v ∈ A.toFinset, d := by rw [Set.ncard_eq_toFinset_card']; simp
      _ ≤ ∑ v ∈ A.toFinset, G.degree v :=
        sum_le_sum (fun v hv ↦ hmin v (Set.mem_toFinset.mp hv))
      _ ≤ ∑ v : V, G.degree v := sum_le_sum_of_subset (subset_univ _)
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ = 2 * G.edgeSet.ncard := by
        rw [edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard]
  rw [matching_verts_ncard_generic M hM]
  nlinarith only [hdegree, Nat.mul_le_mul_left 2 hedge]

theorem maximum_matching_uncovered_bound_on (G : _root_.SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching)
    (hMmax : ∀ L : G.Subgraph, L.IsMatching → L.edgeSet.ncard ≤ M.edgeSet.ncard)
    (A : Set V) (hMA : M.verts ⊆ A) (d D : ℕ)
    (hmin : ∀ v ∈ A, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ D) :
    (A \ M.verts).ncard * (D + 1) ≤ A.ncard * (D + 1 - d) := by
  have hbound := maximum_matching_degree_bound_on G M hM hMmax A d D hmin hmax
  have hsplit : (A \ M.verts).ncard + M.verts.ncard = A.ncard := by
    rw [Set.ncard_sdiff hMA]
    exact Nat.sub_add_cancel (Set.ncard_le_ncard hMA)
  by_cases hdD : d ≤ D + 1
  · have hp := congrArg (fun t ↦ t * (D + 1)) hsplit
    have hq := congrArg (fun t ↦ A.ncard * t) (Nat.sub_add_cancel hdD)
    nlinarith only [hbound, hp, hq]
  · have hA : A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have h := (hmin v hv).trans (hmax v)
      omega
    simp only [hA, Set.empty_sdiff, Set.ncard_empty, zero_mul, le_refl]

theorem exists_near_perfect_matching_on_set_covering (G : _root_.SimpleGraph V)
    (A Z : Set V) (hsupport : G.support ⊆ A)
    (hZ : ∀ z ∈ Z, Z.ncard ≤ (G.neighborSet z).ncard)
    (d D : ℕ) (hmin : ∀ v ∈ A, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ D) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts ⊆ A ∧ Z ⊆ M.verts ∧
      (A \ M.verts).ncard * (D + 1) ≤ A.ncard * (D + 1 - d) := by
  obtain ⟨M, hM, hMZ, hMmax⟩ := exists_maximum_matching_covering G Z hZ
  have hMA : M.verts ⊆ A := by
    intro v hv
    obtain ⟨w, hw, _⟩ := hM hv
    exact hsupport ⟨w, hw.adj_sub⟩
  exact ⟨M, hM, hMA, hMZ, maximum_matching_uncovered_bound_on G M hM hMmax A hMA d D hmin hmax⟩

#print axioms exists_near_perfect_matching_on_set_covering

end Erdos19
