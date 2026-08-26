import ErdosProblems.Erdos633b.AngleCoefficientIndependence
import ErdosProblems.Erdos633b.MinimumCornerEdges
import ErdosProblems.Erdos633b.BoundaryAngleImages

/-! The side opposite beta in case (7) cannot consist solely of a-edges:
its endpoint of angle 2 alpha contains only alpha tile corners. -/

namespace Erdos633b.Tiling

theorem cornerAngleCount_pos_of_piece {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) (e : d.CornerPiece i) : 0 < d.cornerAngleCount i e.val.2 := by
  classical
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

theorem groupOne_double_alpha_corner_counts {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (hirr : Irrational (d.tile.angle 0 / Real.pi)) (i : Fin 3)
    (hi : T.angle i = 2 * d.tile.angle 0) :
    d.cornerAngleCount i 0 = 2 ∧ d.cornerAngleCount i 1 = 0 ∧ d.cornerAngleCount i 2 = 0 := by
  have hg : d.tile.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1 := by
    linarith [d.tile.angle_sum]
  have hs := d.angle_eq_three_counts i
  rw [hi, hg] at hs
  have he : ((d.cornerAngleCount i 0 : ℤ) + 2 * d.cornerAngleCount i 2 - 2 : ℤ) *
        (d.tile.angle 0 : ℝ) +
      ((d.cornerAngleCount i 1 : ℤ) + d.cornerAngleCount i 2 : ℤ) * d.tile.angle 1 = 0 := by
    push_cast
    nlinarith [hs]
  obtain ⟨hu, hv⟩ := two_angle_integer_coefficients 3 2 (by decide) hrel hirr _ _ he
  omega

theorem groupOne_double_alpha_corner_index {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (hirr : Irrational (d.tile.angle 0 / Real.pi)) (i : Fin 3)
    (hi : T.angle i = 2 * d.tile.angle 0) (e : d.CornerPiece i) : e.val.2 = 0 := by
  obtain ⟨_, h1, h2⟩ := d.groupOne_double_alpha_corner_counts hrel hirr i hi
  have hp := d.cornerAngleCount_pos_of_piece i e
  have hn1 : e.val.2 ≠ 1 := by intro h; rw [h, h1] at hp; exact Nat.lt_irrefl 0 hp
  have hn2 : e.val.2 ≠ 2 := by intro h; rw [h, h2] at hp; exact Nat.lt_irrefl 0 hp
  omega

theorem caseSeven_boundary_non_a_pos {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (hirr : Irrational (d.tile.angle 0 / Real.pi)) (h0 : T.angle 0 = 2 * d.tile.angle 0) :
    0 < d.boundarySideCount 1 1 + d.boundarySideCount 1 2 := by
  have hp : T.points 0 ∈ T.edge 1 := T.edge_vertex_mem 1 0 (by decide)
  rw [d.edge_eq_boundaryEdges 1] at hp
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hp
  have hpPiece : T.points 0 ∈ d.place e.val.1 '' d.tile.support := by
    rw [← Triangle.support_move]
    exact he.1
  obtain ⟨j, hj⟩ := d.outer_vertex_of_mem_piece 0 e.val.1 hpPiece
  have hj0 : j = 0 := d.groupOne_double_alpha_corner_index hrel hirr 0 h0 ⟨(e.val.1, j), hj⟩
  have he0 : e.val.2 ≠ 0 := by
    intro h
    have hmem : T.points 0 ∈ (d.tile.move (d.place e.val.1)).edge 0 := by rwa [h] at he
    apply Triangle.ne_vertex_of_mem_edge (d.tile.move (d.place e.val.1)) 0 hmem
    change T.points 0 = d.place e.val.1 (d.tile.points 0)
    simpa only [hj0] using hj.symm
  have hc := d.boundarySideCount_pos_of_edge 1 e.val.2 e.val.1 e.property
  rcases (by decide : ∀ j : Fin 3, j ≠ 0 → j = 1 ∨ j = 2) e.val.2 he0 with h | h
  · rw [h] at hc
    omega
  · rw [h] at hc
    omega

end Erdos633b.Tiling
