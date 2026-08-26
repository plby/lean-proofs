import ErdosProblems.Erdos73.HavenOddPaths
import ErdosProblems.Erdos73.HavenWallTerminals
import ErdosProblems.Erdos73.ParityPaths
import ErdosProblems.Erdos73.ControlledBalancedWall

/-! A controlled balanced wall has arbitrarily many disjoint parity-breaking paths. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {g n q : ℕ}

theorem WallGridAnchor.exists_parityBreaking_paths
    {β : Finset (Finset V)} {h : BrambleHaven G β q}
    {M : MinorModel (squareGrid n) G} {S : GraphSubdivisionModel (elementaryWall g g) G}
    (A : WallGridAnchor M S) (hM : NoGridRowInHavenSmallSide h M)
    (c : BipartiteColoringOn G S.vertexSet) (k p u : ℕ)
    (hk : 1 ≤ k) (hu : 2 * k + p ≤ u) (hug : 2 * u + 2 ≤ g) (huq : u ≤ q)
    (hodd : ∀ K, ¬ (G.induce (h.region K : Set V)).IsBipartite)
    (hno : ¬ HasOddCyclePacking p G) :
    ∃ P : Fin k → GraphPath G, (∀ i, IsParityBreakingPath c.color S.vertexSet (P i)) ∧
      Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet) := by
  have hg : 2 ≤ g := by omega
  obtain ⟨N, J, b, hNS, hJ, hrows, hc, _⟩ :=
    exists_monochromatic_row_terminals S hg c u hug
  have htouch : ∀ K, K.val.card < u → ∃ v ∈ h.region K, v ∈ N := by
    intro K hK
    obtain ⟨v, hvN, hvR⟩ := A.row_terminals_meet_region hM hg N J hJ hrows K hK
    exact ⟨v, hvR, hvN⟩
  rcases h.odd_terminal_paths_or_odd_cycles N k p u hk hu huq hodd htouch with hp | hp
  · exact exists_parityBreakingPathPacking_of_oddTerminalPathPacking c.color N S.vertexSet
      hNS b hc k hp
  · exact (hno hp).elim

theorem BrambleHaven.exists_controlled_balanced_wall_with_parityBreaking_paths
    {ell : ℕ} (h : BrambleHaven G (lowOrderOddSides G ell) q)
    (k p g u : ℕ) (hk : 1 ≤ k) (hu : 2 * k + p ≤ u) (hug : 2 * u + 2 ≤ g)
    (huq : u ≤ q) (horder : controlledGridBrambleBound (2 * (p * g + g)) ≤ q)
    (hno : ¬ HasOddCyclePacking p G) :
    ∃ M : MinorModel (squareGrid (2 * (p * g + g))) G,
      NoGridRowInHavenSmallSide h M ∧
      ∃ S : GraphSubdivisionModel (elementaryWall g g) G,
        Nonempty (WallGridAnchor M S) ∧
        (G.induce (S.vertexSet : Set V)).IsBipartite ∧
        ∃ c : BipartiteColoringOn G S.vertexSet, ∃ P : Fin k → GraphPath G,
          (∀ i, IsParityBreakingPath c.color S.vertexSet (P i)) ∧
          Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet) := by
  obtain ⟨M, hM, S, ⟨A⟩, hS⟩ :=
    h.exists_bipartite_wallSubdivision_with_gridAnchor p g horder hno
  let c := bipartiteColoringOnOfBipartite hS
  obtain ⟨P, hP, hdis⟩ := A.exists_parityBreaking_paths hM c k p u hk hu hug huq
    h.odd_region_of_lowOrderOddSides hno
  exact ⟨M, hM, S, ⟨A⟩, hS, c, P, hP, hdis⟩

end
end Erdos73
