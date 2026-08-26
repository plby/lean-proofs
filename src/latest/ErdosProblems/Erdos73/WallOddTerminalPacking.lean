import ErdosProblems.Erdos73.WallParityPaths

/-! Retain the interior monochromatic terminals and original odd paths for strip selection. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {g n q : ℕ}

theorem WallGridAnchor.exists_monochromatic_odd_terminal_packing
    {β : Finset (Finset V)} {h : BrambleHaven G β q}
    {M : MinorModel (squareGrid n) G} {S : GraphSubdivisionModel (elementaryWall g g) G}
    (A : WallGridAnchor M S) (hM : NoGridRowInHavenSmallSide h M)
    (c : BipartiteColoringOn G S.vertexSet) (k p u : ℕ)
    (hk : 1 ≤ k) (hu : 2 * k + p ≤ u) (hug : 2 * u + 2 ≤ g) (huq : u ≤ q)
    (hodd : ∀ K, ¬ (G.induce (h.region K : Set V)).IsBipartite)
    (hno : ¬ HasOddCyclePacking p G) :
    ∃ N : Finset V, ∃ b : Bool, N ⊆ S.vertexSet ∧ (∀ x ∈ N, c.color x = b) ∧
      (∀ x ∈ N, ∃ w : ElementaryWallVertex g g,
        x = S.branchVertex w ∧ 0 < w.val.2.val ∧ w.val.2.val + 1 < 2 * g) ∧
      HasOddTerminalPathPacking G N k := by
  have hg : 2 ≤ g := by omega
  obtain ⟨N, J, b, hNS, hJ, hrows, hc, hnails⟩ :=
    exists_monochromatic_row_terminals S hg c u hug
  have htouch : ∀ K, K.val.card < u → ∃ v ∈ h.region K, v ∈ N := by
    intro K hK
    obtain ⟨v, hvN, hvR⟩ := A.row_terminals_meet_region hM hg N J hJ hrows K hK
    exact ⟨v, hvR, hvN⟩
  have hp : HasOddTerminalPathPacking G N k :=
    (h.odd_terminal_paths_or_odd_cycles N k p u hk hu huq hodd htouch).resolve_right hno
  refine ⟨N, b, hNS, hc, ?_, hp⟩
  intro x hx
  obtain ⟨a, he⟩ := hnails x hx
  refine ⟨elementaryWallInteriorNail hg (innerRowEmbedding g a) ⟨1, by omega⟩, he, ?_, ?_⟩
  · change 0 < 2
    decide
  · change 2 + 1 < 2 * g
    omega

theorem BrambleHaven.exists_controlled_balanced_wall_with_odd_terminal_packing
    {ell : ℕ} (h : BrambleHaven G (lowOrderOddSides G ell) q)
    (k p g u : ℕ) (hk : 1 ≤ k) (hu : 2 * k + p ≤ u) (hug : 2 * u + 2 ≤ g)
    (huq : u ≤ q) (horder : controlledGridBrambleBound (2 * (p * g + g)) ≤ q)
    (hno : ¬ HasOddCyclePacking p G) :
    ∃ M : MinorModel (squareGrid (2 * (p * g + g))) G,
      NoGridRowInHavenSmallSide h M ∧
      ∃ S : GraphSubdivisionModel (elementaryWall g g) G,
        Nonempty (WallGridAnchor M S) ∧ (G.induce (S.vertexSet : Set V)).IsBipartite ∧
        ∃ c : BipartiteColoringOn G S.vertexSet, ∃ N : Finset V, ∃ b : Bool,
          N ⊆ S.vertexSet ∧ (∀ x ∈ N, c.color x = b) ∧
          (∀ x ∈ N, ∃ w : ElementaryWallVertex g g,
            x = S.branchVertex w ∧ 0 < w.val.2.val ∧ w.val.2.val + 1 < 2 * g) ∧
          HasOddTerminalPathPacking G N k := by
  obtain ⟨M, hM, S, ⟨A⟩, hS⟩ :=
    h.exists_bipartite_wallSubdivision_with_gridAnchor p g horder hno
  let c := bipartiteColoringOnOfBipartite hS
  obtain ⟨N, b, hNS, hc, hN, hp⟩ := A.exists_monochromatic_odd_terminal_packing hM c k p u
    hk hu hug huq h.odd_region_of_lowOrderOddSides hno
  exact ⟨M, hM, S, ⟨A⟩, hS, c, N, b, hNS, hc, hN, hp⟩

end
end Erdos73
