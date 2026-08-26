import ErdosProblems.Erdos633b.ReptilingRightAngle
import ErdosProblems.Erdos633b.ReptilingRightTrace

/-! The exceptional matrix forces a commensurable smallest angle and is impossible.
This completes the zero-diagonal reduction for scalene ordered nonsquare reptilings. -/

namespace Erdos633b.Tiling

theorem smallest_corner_at_second_endpoint_on_edge {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ∀ i, d.tile.angle i = T.angle i) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (i : Fin 3) (hi : i ≠ 1)
    (h20 : d.boundaryMatrix i 0 = 0) (h22 : d.boundaryMatrix i 2 = 0) :
    ∃ a : Fin n, d.place a (d.tile.points 0) = T.points 1 := by
  have hc0 : d.boundarySideCount i 0 = 0 := by
    unfold boundaryMatrix at h20
    exact_mod_cast h20
  have hc2 : d.boundarySideCount i 2 = 0 := by
    unfold boundaryMatrix at h22
    exact_mod_cast h22
  have hp : T.points 1 ∈ T.edge i := T.edge_vertex_mem i 1 hi.symm
  rw [d.edge_eq_boundaryEdges i] at hp
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hp
  have heidx : e.val.2 = 1 := by
    have hc := d.boundarySideCount_pos_of_edge i e.val.2 e.val.1 e.property
    have hne0 : e.val.2 ≠ 0 := by intro he; rw [he, hc0] at hc; exact Nat.lt_irrefl 0 hc
    have hne2 : e.val.2 ≠ 2 := by intro he; rw [he, hc2] at hc; exact Nat.lt_irrefl 0 hc
    omega
  let S : Triangle := d.tile.move (d.place e.val.1)
  have hpS : T.points 1 ∈ S.support := he.1
  have hpPiece : T.points 1 ∈ d.place e.val.1 '' d.tile.support := by
    rwa [← Triangle.support_move]
  obtain ⟨j, hj⟩ := d.outer_vertex_of_mem_piece 1 e.val.1 hpPiece
  have hj1 : j ≠ 1 := by
    intro hj1
    have hmem : T.points 1 ∈ S.edge 1 := by rwa [heidx] at he
    have hn := S.ne_vertex_of_mem_edge 1 hmem
    have hv : S.points 1 = T.points 1 := by
      change d.place e.val.1 (d.tile.points 1) = T.points 1
      simpa only [hj1] using hj
    exact hn hv.symm
  have hj2 : j ≠ 2 := by
    intro hj2
    have hle := d.tile_angle_le_of_vertex 1 j e.val.1 hj
    rw [hj2, ← h 1] at hle
    exact (not_le_of_gt h12) hle
  have hj0 : j = 0 := by omega
  exact ⟨e.val.1, hj0 ▸ hj⟩

theorem smallest_corner_at_second_endpoint {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ∀ i, d.tile.angle i = T.angle i) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (h20 : d.boundaryMatrix 2 0 = 0) (h22 : d.boundaryMatrix 2 2 = 0) :
    ∃ a : Fin n, d.place a (d.tile.points 0) = T.points 1 :=
  d.smallest_corner_at_second_endpoint_on_edge h h12 2 (by decide) h20 h22

theorem second_angle_multiple_of_smallest_corner {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h1 : d.tile.angle 1 = T.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (a : Fin n) (ha : d.place a (d.tile.points 0) = T.points 1) :
    ∃ u : ℕ, d.tile.angle 1 = u * d.tile.angle 0 := by
  classical
  let e : d.CornerPiece 1 := ⟨(a, 0), ha⟩
  have hall (f : d.CornerPiece 1) : f.val.2 = 0 := by
    by_contra hn
    have hef : e ≠ f := by
      intro he
      have he' := congrArg (fun x : d.CornerPiece 1 => x.val.2) he
      exact hn he'.symm
    have hlarge : d.tile.angle 1 ≤ d.tile.angle f.val.2 := by
      rcases (by decide : ∀ j : Fin 3, j ≠ 0 → j = 1 ∨ j = 2) f.val.2 hn with hj | hj
      · rw [hj]
      · rw [hj]
        exact h12.le
    have hb : d.tile.angle e.val.2 + d.tile.angle f.val.2 ≤ T.angle 1 := by
      rw [d.angle_eq_sum_cornerPieces]
      exact Finset.add_le_sum (fun x _ => (d.tile.angle_pos x.val.2).le)
        (Finset.mem_univ e) (Finset.mem_univ f) hef
    change d.tile.angle 0 + d.tile.angle f.val.2 ≤ T.angle 1 at hb
    rw [← h1] at hb
    linarith [d.tile.angle_pos 0]
  have hs := d.angle_eq_sum_cornerPieces 1
  simp_rw [hall] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  exact ⟨Fintype.card (d.CornerPiece 1), h1.trans hs⟩

theorem exceptional_smallest_angle_rational {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ∀ i, d.tile.angle i = T.angle i) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hright : d.tile.angle 2 = Real.pi / 2)
    (h20 : d.boundaryMatrix 2 0 = 0) (h22 : d.boundaryMatrix 2 2 = 0) :
    IsRational (d.tile.angle 0 / Real.pi) := by
  obtain ⟨a, ha⟩ := d.smallest_corner_at_second_endpoint h h12 h20 h22
  obtain ⟨u, hu⟩ := d.second_angle_multiple_of_smallest_corner (h 1) h12 a ha
  have hs := d.tile.angle_sum
  rw [hright, hu] at hs
  refine ⟨1 / (2 * ((u : ℚ) + 1)), ?_⟩
  push_cast
  have hd : (2 : ℝ) * ((u : ℝ) + 1) ≠ 0 := by positivity
  apply (div_eq_div_iff hd Real.pi_ne_zero).mpr
  nlinarith

theorem reptiling_diagonal_zero {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2) :
    ∀ i, d.boundaryMatrix i i = 0 := by
  have hmin (j : Fin 3) (hj : j ≠ 0) : d.tile.angle 0 < d.tile.angle j := by
    fin_cases j
    · exact False.elim (hj rfl)
    · exact h01
    · exact h01.trans h12
  rcases d.boundaryMatrix_corner_alternative hn h hmin with hd | ⟨_, _, _, _, _, h20, h22⟩
  · exact hd
  have hright := d.reptiling_right_angle hn h h01 h12
  have hrat := d.exceptional_smallest_angle_rational h h12 hright h20 h22
  exact d.boundaryMatrix_diagonal_zero_of_right_rational hn h hmin hright hrat

end Erdos633b.Tiling
