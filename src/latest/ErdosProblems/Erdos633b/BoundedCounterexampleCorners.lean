import ErdosProblems.Erdos633b.SixShapesUnconditional
import ErdosProblems.Erdos633b.SmallAngleCounterexamples
import ErdosProblems.Erdos633b.TwoPiThirdsCornerColumns
import ErdosProblems.Erdos633b.BoundedCornerShapes

/-! Uniform actual corner bounds and a nonzero corner/local determinant.
The 120-degree exception is removed using the proved six-shape necessity. -/

namespace Erdos633b.Tiling

theorem bounded_corner_columns_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hscalene : Function.Injective T.angle)
    (hR : d.cornerColumnCount 2 = 0)
    (hP : 0 < d.cornerColumnCount 0) (hPb : d.cornerColumnCount 0 ≤ 3)
    (hQ : 0 < d.cornerColumnCount 1) (hQb : d.cornerColumnCount 1 ≤ 3) : EightCases T := by
  rcases d.angle_shapes_of_bounded_columns hR hP hPb hQ hQb hscalene with hrep | hs
  · exact d.reptiling_necessary hn hrep
  · exact d.six_shapes_necessary_unconditional hn hs

theorem angle_lower_of_counterexample {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2) :
    Real.pi / 21 ≤ d.tile.angle 0 := by
  by_contra h
  have hsmall := lt_of_not_ge h
  have hg := d.small_angle_counterexample_forces_two_pi_thirds hn hnot h01 h12 hsmall
  obtain ⟨_, _, hscalene, hrep⟩ := d.rational_angles_of_counterexample hn hnot
  obtain ⟨hP, hQ, hR⟩ :=
    d.small_two_pi_thirds_corner_columns h01 h12 hscalene hrep hsmall hg
  exact hnot (d.bounded_corner_columns_necessary hn hscalene hR
    (by omega) (by omega) (by omega) (by omega))

theorem corner_local_determinant_ne_zero_unconditional {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (t : ℤ × ℤ × ℤ) (ht : t ∈ orderedNonrightRelationTriples)
    (he : (t.1 : ℝ) * d.tile.angle 0 + (t.2.1 : ℝ) * d.tile.angle 1 =
      (t.2.2 : ℝ) * Real.pi) :
    cornerLocalDeterminant (d.cornerColumnCount 0) (d.cornerColumnCount 1)
      (d.cornerColumnCount 2) t ≠ 0 := by
  intro hd
  obtain ⟨_, _, hscalene, hrep⟩ := d.rational_angles_of_counterexample hn hnot
  have hγ := d.tile_angle_le_two_pi_thirds_of_counterexample hn hnot 2
  have hP := d.ordered_smallest_column_pos h01 h12 hγ hscalene hrep
  have htotal := d.five_le_corner_total_of_not_reptiling hscalene hrep
  rw [Fin.sum_univ_three] at htotal
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three] at hc
  obtain ⟨ha, hb⟩ := corner_local_zero_numerators _ _ _ d.tile.angle_sum _ _ _ hc t he hd
  obtain ⟨hR, hR1⟩ := d.ordered_corner_columns h01 h12 hscalene hrep
  have hRv : d.cornerColumnCount 2 = 0 ∨ d.cornerColumnCount 2 = 1 := by omega
  rcases hRv with hR0 | hRone
  · rw [hR0] at hd ha hb htotal
    rcases corner_local_degenerate_zero _ _ (by omega) (by omega) t ht hd ha hb with h | h | h
    · exact hnot (d.bounded_corner_columns_necessary hn hscalene hR0
        (by omega) (by omega) (by omega) (by omega))
    · exact hnot (d.bounded_corner_columns_necessary hn hscalene hR0
        (by omega) (by omega) (by omega) (by omega))
    · exact hnot (d.bounded_corner_columns_necessary hn hscalene hR0
        (by omega) (by omega) (by omega) (by omega))
  · obtain ⟨hQ0, hP4⟩ := hR1 hRone
    rw [hRone, hQ0] at hd ha hb
    exact corner_local_degenerate_one_impossible _ hP4 t ht hd ha hb

theorem counterexample_ordered_corner_data {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2) :
    Real.pi / 21 ≤ d.tile.angle 0 ∧
      1 ≤ d.cornerColumnCount 0 ∧ d.cornerColumnCount 0 ≤ 21 ∧
      d.cornerColumnCount 1 ≤ 5 ∧ d.cornerColumnCount 2 ≤ 1 ∧
      5 ≤ d.cornerColumnCount 0 + d.cornerColumnCount 1 + d.cornerColumnCount 2 ∧
      (d.cornerColumnCount 2 = 1 →
        d.cornerColumnCount 1 = 0 ∧ 4 ≤ d.cornerColumnCount 0) ∧
      ∃ t ∈ orderedNonrightRelationTriples,
        (t.1 : ℝ) * d.tile.angle 0 + (t.2.1 : ℝ) * d.tile.angle 1 =
          (t.2.2 : ℝ) * Real.pi ∧
        cornerLocalDeterminant (d.cornerColumnCount 0) (d.cornerColumnCount 1)
          (d.cornerColumnCount 2) t ≠ 0 := by
  have hα := d.angle_lower_of_counterexample hn hnot h01 h12
  have hγ := d.tile_angle_le_two_pi_thirds_of_counterexample hn hnot 2
  obtain ⟨_, _, hscalene, hrep⟩ := d.rational_angles_of_counterexample hn hnot
  have hP := d.ordered_smallest_column_pos h01 h12 hγ hscalene hrep
  have hQ := d.ordered_middle_column_le_five h01 hγ
  obtain ⟨hR, hR1⟩ := d.ordered_corner_columns h01 h12 hscalene hrep
  have ht := d.five_le_corner_total_of_not_reptiling hscalene hrep
  rw [Fin.sum_univ_three] at ht
  obtain ⟨t, ht', he⟩ := nonright_relation_of_local_relation _ _ _ d.tile.angle_sum
    (d.tile_angle_ne_pi_half_of_counterexample hn hnot 2)
    (d.ordered_local_relation h01 h12 hγ hscalene hrep)
  exact ⟨hα, hP, d.corner_column_le_twenty_one_of_angle_lower 0 hα, hQ, hR, ht,
    hR1, t, ht', he, d.corner_local_determinant_ne_zero_unconditional hn hnot h01 h12 t ht' he⟩

end Erdos633b.Tiling
