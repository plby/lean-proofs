import ErdosProblems.Erdos73.BrickSliceHandles
import ErdosProblems.Erdos73.WallOddTerminalPacking

/-! Original-haven controlled walls with arbitrarily many disjoint breaking column handles. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {g n q : ℕ}

theorem WallGridAnchor.exists_wall_with_breaking_handles
    {β : Finset (Finset V)} {h : BrambleHaven G β q}
    {M : MinorModel (squareGrid n) G} {S : GraphSubdivisionModel (elementaryWall g g) G}
    (A : WallGridAnchor M S) (hM : NoGridRowInHavenSmallSide h M)
    (col : BipartiteColoringOn G S.vertexSet) (k d t m p u : ℕ)
    (hd : 0 < d) (hnumber : 5 * (2 * k - 2) < t) (hsize : 72 * t * t + t < m)
    (hrows : 2 * t < g - 1) (hwidth : (6 * t + 1) * d ≤ g - 1)
    (hu : 2 * m + p ≤ u) (hug : 2 * u + 2 ≤ g) (huq : u ≤ q)
    (hodd : ∀ K, ¬ (G.induce (h.region K : Set V)).IsBipartite)
    (hno : ¬ HasOddCyclePacking p G) :
    ∃ S' : GraphSubdivisionModel (elementaryWall (d + 1) g) G,
      Nonempty (WallGridAnchor M S') ∧ ∃ col' : BipartiteColoringOn G S'.vertexSet,
      ∃ B : Fin k → Erdos73Infrastructure.SimpleGraph.GraphPath G,
        (∀ i, IsParityBreakingPath col'.color S'.vertexSet (B i)) ∧
        Pairwise (fun i j => Disjoint (B i).vertexSet (B j).vertexSet) ∧
        (∀ i, ∃ v w : ElementaryWallVertex (d + 1) g,
          (B i).source = S'.branchVertex v ∧ (B i).target = S'.branchVertex w ∧
          (v.val.2.val ≤ 1 ∨ 2 * d ≤ v.val.2.val) ∧
          (w.val.2.val ≤ 1 ∨ 2 * d ≤ w.val.2.val)) := by
  have hg : 2 ≤ g := by omega
  have hm : 1 ≤ m := by omega
  have hcols : 6 * t < g - 1 := by
    have hh := (Nat.mul_le_mul_left (6 * t + 1) hd).trans hwidth
    simp only [Nat.mul_one] at hh
    omega
  obtain ⟨N, b, _, hcolor, hN, P, hP, hdis⟩ :=
    A.exists_monochromatic_odd_terminal_packing hM col m p u hm hu hug huq hodd hno
  obtain ⟨st⟩ := exists_brickStripSelectionState S col.color P N b hg hg hN hcolor hP hdis
    hrows hcols hsize
  obtain ⟨a, hs, B, hB, hBdis, _, _, hends⟩ :=
    st.exists_breaking_slice_handles col k d hg hd hwidth hnumber
  let S' := S.restrictCopy (brickColumnSliceCopy a d hs)
  let col' := col.mono_support (S.restrictCopy_vertexSet_subset_vertexSet (brickColumnSliceCopy a d hs))
  exact ⟨S', ⟨A.restrictOffsets 0 a (by omega) hs⟩, col', B, hB, hBdis, hends⟩

theorem BrambleHaven.exists_controlled_wall_with_breaking_handles
    {ell : ℕ} (h : BrambleHaven G (lowOrderOddSides G ell) q)
    (k d t m p g u : ℕ)
    (hd : 0 < d) (hnumber : 5 * (2 * k - 2) < t) (hsize : 72 * t * t + t < m)
    (hrows : 2 * t < g - 1) (hwidth : (6 * t + 1) * d ≤ g - 1)
    (hu : 2 * m + p ≤ u) (hug : 2 * u + 2 ≤ g) (huq : u ≤ q)
    (horder : controlledGridBrambleBound (2 * (p * g + g)) ≤ q)
    (hno : ¬ HasOddCyclePacking p G) :
    ∃ M : MinorModel (squareGrid (2 * (p * g + g))) G,
      NoGridRowInHavenSmallSide h M ∧
      ∃ S : GraphSubdivisionModel (elementaryWall (d + 1) g) G,
        Nonempty (WallGridAnchor M S) ∧ ∃ col : BipartiteColoringOn G S.vertexSet,
        ∃ B : Fin k → Erdos73Infrastructure.SimpleGraph.GraphPath G,
          (∀ i, IsParityBreakingPath col.color S.vertexSet (B i)) ∧
          Pairwise (fun i j => Disjoint (B i).vertexSet (B j).vertexSet) ∧
          (∀ i, ∃ v w : ElementaryWallVertex (d + 1) g,
            (B i).source = S.branchVertex v ∧ (B i).target = S.branchVertex w ∧
            (v.val.2.val ≤ 1 ∨ 2 * d ≤ v.val.2.val) ∧
            (w.val.2.val ≤ 1 ∨ 2 * d ≤ w.val.2.val)) := by
  obtain ⟨M, hM, S, ⟨A⟩, hS⟩ :=
    h.exists_bipartite_wallSubdivision_with_gridAnchor p g horder hno
  obtain ⟨S', hA', col, B, hB, hdis, hends⟩ :=
    A.exists_wall_with_breaking_handles hM (bipartiteColoringOnOfBipartite hS)
      k d t m p u hd hnumber hsize hrows hwidth hu hug huq h.odd_region_of_lowOrderOddSides hno
  exact ⟨M, hM, S', hA', col, B, hB, hdis, hends⟩

end
end Erdos73
