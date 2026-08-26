import ErdosProblems.Erdos633b.CaseSevenBoundary

/-! The (alpha+2 beta) corner rules out two adjacent boundaries made only
of b-edges. Whole edges and their actual vertex incidences are used. -/

namespace Erdos633b
namespace Triangle

theorem edge_not_subset_two_outer_edges (T S : Triangle) :
    ¬ (S.edge 1 ⊆ T.edge 0 ∧ S.edge 1 ⊆ T.edge 1) := by
  rintro ⟨h0, h1⟩
  have hp (p : Plane) (he : p ∈ S.edge 1) : p = T.points 2 := by
    have ha := h0 he
    have hb := h1 he
    apply T.eq_vertex_of_coord_eq_one ha.1 2
    have hs := T.coord_sum p
    rw [ha.2, hb.2] at hs
    linarith
  have hA := hp (S.points 0) (S.edge_vertex_mem 1 0 (by decide))
  have hB := hp (S.points 2) (S.edge_vertex_mem 1 2 (by decide))
  exact S.independent.injective.ne (by decide : (0 : Fin 3) ≠ 2) (hA.trans hB.symm)

end Triangle
namespace Tiling

theorem cornerPiece_eq_of_count_one {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i j : Fin 3) (hc : d.cornerAngleCount i j = 1) (e f : d.CornerPiece i)
    (he : e.val.2 = j) (hf : f.val.2 = j) : e = f := by
  classical
  have hcard : (Finset.univ.filter (fun e : d.CornerPiece i => e.val.2 = j)).card ≤ 1 := by
    change d.cornerAngleCount i j ≤ 1
    omega
  apply Finset.card_le_one_iff.mp hcard
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩

theorem groupTwo_alpha_two_beta_corner_counts {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (hirr : Irrational (d.tile.angle 0 / Real.pi)) (i : Fin 3)
    (hi : T.angle i = d.tile.angle 0 + 2 * d.tile.angle 1) :
    d.cornerAngleCount i 0 = 1 ∧ d.cornerAngleCount i 1 = 2 ∧ d.cornerAngleCount i 2 = 0 := by
  have hrel : 3 * d.tile.angle 0 + 3 * d.tile.angle 1 = Real.pi := by
    linarith [d.tile.angle_sum]
  have hg' : d.tile.angle 2 = 2 * d.tile.angle 0 + 2 * d.tile.angle 1 := by
    linarith [d.tile.angle_sum]
  have hs := d.angle_eq_three_counts i
  rw [hi, hg'] at hs
  have he : ((d.cornerAngleCount i 0 : ℤ) + 2 * d.cornerAngleCount i 2 - 1 : ℤ) *
        (d.tile.angle 0 : ℝ) +
      ((d.cornerAngleCount i 1 : ℤ) + 2 * d.cornerAngleCount i 2 - 2 : ℤ) *
        d.tile.angle 1 = 0 := by
    push_cast
    nlinarith [hs]
  obtain ⟨hu, hv⟩ := two_angle_integer_coefficients 3 3 (by decide) hrel hirr _ _ he
  omega

theorem groupTwoSixty_not_two_pure_boundaries {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (hirr : Irrational (d.tile.angle 0 / Real.pi))
    (h2 : T.angle 2 = d.tile.angle 0 + 2 * d.tile.angle 1) :
    ¬ (d.boundarySideCount 0 0 = 0 ∧ d.boundarySideCount 0 2 = 0 ∧
      d.boundarySideCount 1 0 = 0 ∧ d.boundarySideCount 1 2 = 0) := by
  rintro ⟨hp0, hr0, hp1, hr1⟩
  obtain ⟨hc0, _, hc2⟩ := d.groupTwo_alpha_two_beta_corner_counts hg hirr 2 h2
  have incident (i : Fin 3) (hi : (2 : Fin 3) ≠ i)
      (hp : d.boundarySideCount i 0 = 0) (hr : d.boundarySideCount i 2 = 0) :
      ∃ e : d.BoundaryEdge i, e.val.2 = 1 ∧ d.place e.val.1 (d.tile.points 0) = T.points 2 := by
    have hm : T.points 2 ∈ T.edge i := T.edge_vertex_mem i 2 hi
    rw [d.edge_eq_boundaryEdges i] at hm
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hm
    have hed : e.val.2 = 1 := by
      have hc := d.boundarySideCount_pos_of_edge i e.val.2 e.val.1 e.property
      have hn0 : e.val.2 ≠ 0 := by intro hz; rw [hz, hp] at hc; omega
      have hn2 : e.val.2 ≠ 2 := by intro hz; rw [hz, hr] at hc; omega
      omega
    have hpiece : T.points 2 ∈ d.place e.val.1 '' d.tile.support := by
      rw [← Triangle.support_move]
      exact he.1
    obtain ⟨j, hj⟩ := d.outer_vertex_of_mem_piece 2 e.val.1 hpiece
    have hn1 : j ≠ 1 := by
      intro hz
      have he' : T.points 2 ∈ (d.tile.move (d.place e.val.1)).edge 1 := by rwa [hed] at he
      apply Triangle.ne_vertex_of_mem_edge (d.tile.move (d.place e.val.1)) 1 he'
      change T.points 2 = d.place e.val.1 (d.tile.points 1)
      simpa only [hz] using hj.symm
    have hn2 : j ≠ 2 := by
      have hc := d.cornerAngleCount_pos_of_piece 2 ⟨(e.val.1, j), hj⟩
      change 0 < d.cornerAngleCount 2 j at hc
      intro hz
      rw [hz, hc2] at hc
      omega
    have hj0 : j = 0 := by omega
    exact ⟨e, hed, by simpa only [hj0] using hj⟩
  obtain ⟨e, hei, he⟩ := incident 0 (by decide) hp0 hr0
  obtain ⟨f, hfi, hf⟩ := incident 1 (by decide) hp1 hr1
  have hcorner := d.cornerPiece_eq_of_count_one 2 0 hc0
    ⟨(e.val.1, 0), he⟩ ⟨(f.val.1, 0), hf⟩ rfl rfl
  have htile : e.val.1 = f.val.1 := congrArg (fun t : d.CornerPiece 2 => t.val.1) hcorner
  apply T.edge_not_subset_two_outer_edges (d.tile.move (d.place e.val.1))
  constructor
  · simpa only [hei] using e.property
  · rw [htile]
    simpa only [hfi] using f.property

end Tiling
end Erdos633b
