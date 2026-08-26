import ErdosProblems.Erdos73.BalancedSubwallSelection
import ErdosProblems.Erdos73.WallGridAnchors

/-! A controlled wall with bipartite induced support, unless disjoint odd cycles already exist. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem BrambleHaven.exists_bipartite_wallSubdivision_with_gridAnchor
    {β : Finset (Finset V)} {q : ℕ} (h : BrambleHaven G β q)
    (p g : ℕ)
    (horder : controlledGridBrambleBound (2 * (p * g + g)) ≤ q)
    (hno : ¬ HasOddCyclePacking p G) :
    ∃ M : MinorModel (squareGrid (2 * (p * g + g))) G,
      NoGridRowInHavenSmallSide h M ∧
      ∃ S : GraphSubdivisionModel (elementaryWall g g) G,
        Nonempty (WallGridAnchor M S) ∧ (G.induce (S.vertexSet : Set V)).IsBipartite := by
  let m := p * g + g
  obtain ⟨M, hM⟩ := h.exists_grid_with_row_control (2 * m) horder
  obtain ⟨S, ⟨A⟩⟩ := exists_wallSubdivision_with_gridAnchor M
  have hwidth : p * g ≤ m := by dsimp only [m]; omega
  have hheight : g ≤ m := by dsimp only [m]; omega
  obtain ⟨i, hbip⟩ := exists_bipartite_columnBlock_subdivision S hwidth hheight hno
  let f := columnBlockWallCopy g g hwidth hheight i
  have hsmallWidth : i.val * g + g ≤ m := by
    have hh := Nat.mul_le_mul_right g (show i.val + 1 ≤ p by omega)
    rw [Nat.add_mul, Nat.one_mul] at hh
    omega
  have A' : WallGridAnchor M (S.restrictCopy f) :=
    A.restrictOffsets 0 (i.val * g) (by omega) hsmallWidth
  exact ⟨M, hM, S.restrictCopy f, ⟨A'⟩, hbip⟩

theorem BrambleHaven.exists_bipartite_wallSubdivision_with_row_control
    {β : Finset (Finset V)} {q : ℕ} (h : BrambleHaven G β q)
    (p g : ℕ) (hg : 2 ≤ g)
    (horder : controlledGridBrambleBound (2 * (p * g + g)) ≤ q)
    (hno : ¬ HasOddCyclePacking p G) :
    ∃ S : GraphSubdivisionModel (elementaryWall g g) G,
      NoWallRowNailsInHavenSmallSide h S ∧ (G.induce (S.vertexSet : Set V)).IsBipartite := by
  obtain ⟨M, hM, S, ⟨A⟩, hbip⟩ := h.exists_bipartite_wallSubdivision_with_gridAnchor p g horder hno
  exact ⟨S, A.no_row_nails_in_smallSide hM hg, hbip⟩

end
end Erdos73
