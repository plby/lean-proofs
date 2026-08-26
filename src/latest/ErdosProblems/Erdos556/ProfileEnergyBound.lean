import ErdosProblems.Erdos556.ProfilePotentialGraph
import ErdosProblems.Erdos556.ProfileMassCounts
import ErdosProblems.Erdos556.DecompositionEdgeCounts
import ErdosProblems.Erdos556.CubeRetainedGeometry
import ErdosProblems.Erdos556.CompletePairCounts

/-! The edge budget gives an upper bound for the cube-profile energy. -/

namespace Erdos556

open SimpleGraph Finset

theorem twice_complete_edge_count {V : Type*} [Fintype V] [DecidableEq V] :
    2 * (Nat.card (⊤ : SimpleGraph V).edgeSet : ℝ) + Fintype.card V =
      (Fintype.card V : ℝ) ^ 2 := by
  classical
  rw [twice_edge_count_eq_ordered_pair_sum]
  have hd : (∑ u : V, ∑ v : V, if u = v then (1 : ℝ) else 0) = Fintype.card V := by
    simp
  rw [← hd]
  calc
    _ = ∑ u : V, ∑ v : V,
        ((if (⊤ : SimpleGraph V).Adj u v then (1 : ℝ) else 0) +
          if u = v then 1 else 0) := by simp only [sum_add_distrib]
    _ = ∑ _u : V, ∑ _v : V, (1 : ℝ) := by
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      by_cases huv : u = v <;> simp [top_adj, huv]
    _ = _ := by simp [pow_two]

def ThreeColourDecomposition.bipartiteUnion {V : Type*}
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) :
    SimpleGraph V := ⨆ i, h.bipartite i

theorem ThreeColourDecomposition.bipartiteUnion_le_potential {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) :
    h.bipartiteUnion ≤ profilePotentialGraph h.profile := by
  intro u v huv
  obtain ⟨i, hi⟩ := iSup_adj.mp huv
  exact profileOppositeAt_disjoint _ _ _ (h.bipartite_profiles_opposite i u v hi)

theorem ThreeColourDecomposition.bipartiteUnion_edge_count {V : Type*}
    [Fintype V] [DecidableEq V] {c : ThreeColouring V} {E D : ℝ}
    (h : ThreeColourDecomposition c E D) :
    Nat.card h.bipartiteUnion.edgeSet = ∑ i, Nat.card (h.bipartite i).edgeSet := by
  apply natCard_edges_iSup
  intro i j hij
  exact (c.graphs_disjoint i j hij).mono (h.bipartite_le i) (h.bipartite_le j)

theorem ThreeColourDecomposition.total_edge_budget {V : Type*}
    [Fintype V] [DecidableEq V] {c : ThreeColouring V} {E D : ℝ}
    (h : ThreeColourDecomposition c E D) :
    (Fintype.card V : ℝ) ^ 2 ≤ Fintype.card V +
      2 * Nat.card h.bipartiteUnion.edgeSet +
      2 * D * (∑ p, (profileDimension p : ℝ) * (h.profileClass p).card) + 6 * E := by
  have hret : (Nat.card h.retained.edgeSet : ℝ) =
      (Nat.card h.bipartiteUnion.edgeSet : ℝ) + ∑ i, (Nat.card (h.sparse i).edgeSet : ℝ) := by
    have hh := h.retained_edge_count
    rw [sum_add_distrib, ← h.bipartiteUnion_edge_count] at hh
    exact_mod_cast hh
  have hf : (∑ i, (Nat.card (h.sparse i).edgeSet : ℝ)) ≤
      D * (∑ p, (profileDimension p : ℝ) * (h.profileClass p).card) := by
    calc
      _ ≤ ∑ i, D * (h.stars i).card := sum_le_sum (fun i _ => h.sparse_edge_count_le i)
      _ = D * (∑ i, ((h.stars i).card : ℝ)) := (mul_sum _ _ _).symm
      _ = _ := by
        congr 1
        exact_mod_cast h.sum_stars_card
  have hcomp : (Nat.card h.retained.edgeSet : ℝ) + Nat.card h.missing.edgeSet =
      Nat.card (⊤ : SimpleGraph V).edgeSet := by
    exact_mod_cast natCard_edges_add_complement h.retained
  have hm := h.missing_edge_count_le
  have ht := twice_complete_edge_count (V := V)
  linarith

theorem ThreeColourDecomposition.raw_profile_energy_bound {V : Type*}
    [Fintype V] [DecidableEq V] {c : ThreeColouring V} {E D : ℝ}
    (h : ThreeColourDecomposition c E D) (n : ℝ) :
    (Fintype.card V : ℝ) ^ 2 -
        cubeDisjointMass (fun p => ((h.profileClass p).card : ℝ)) -
        n * (∑ p, (profileDimension p : ℝ) * (h.profileClass p).card) ≤
      Fintype.card V + (2 * D - n) *
        (∑ p, (profileDimension p : ℝ) * (h.profileClass p).card) + 6 * E := by
  have hpot := profilePotentialGraph_edge_count h.profile
  have hle : (Nat.card h.bipartiteUnion.edgeSet : ℝ) ≤
      Nat.card (profilePotentialGraph h.profile).edgeSet := by
    exact_mod_cast natCard_edges_mono _ _ h.bipartiteUnion_le_potential
  have hb := h.total_edge_budget
  change 2 * (Nat.card (profilePotentialGraph h.profile).edgeSet : ℝ) =
    cubeDisjointMass (fun p => ((h.profileClass p).card : ℝ)) at hpot
  nlinarith

theorem ThreeColourDecomposition.free_coordinate_mass_le {V : Type*}
    [Fintype V] [DecidableEq V] {c : ThreeColouring V} {E D : ℝ}
    (h : ThreeColourDecomposition c E D) :
    (∑ p, (profileDimension p : ℝ) * (h.profileClass p).card) ≤ 3 * Fintype.card V := by
  have hs : (∑ i, (h.stars i).card) ≤ 3 * Fintype.card V := by
    calc
      _ ≤ ∑ _i : Fin 3, Fintype.card V := sum_le_sum (fun i _ => card_le_univ _)
      _ = _ := by simp
  rw [h.sum_stars_card] at hs
  exact_mod_cast hs

#print axioms ThreeColourDecomposition.raw_profile_energy_bound

end Erdos556
