import ErdosProblems.Erdos633b.CornerDeterminantDegeneracy
import ErdosProblems.Erdos633b.IntegerAngleWeights

/-! Outside seven explicit local-relation families, every hypothetical
counterexample has positive integer tile-angle weights with denominator at most 256.
This is a finite reduction, not an exclusion of those possible tilings. -/

namespace Erdos633b.Tiling

theorem bounded_denominator_of_relation_outside_seven {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (t : ℤ × ℤ × ℤ) (ht : t ∈ orderedNonrightRelationTriples)
    (hne : t ∉ smallAngleRelationTriples)
    (he : (t.1 : ℝ) * d.tile.angle 0 + (t.2.1 : ℝ) * d.tile.angle 1 =
      (t.2.2 : ℝ) * Real.pi) :
    ∃ N : ℕ, 3 ≤ N ∧ N ≤ 256 ∧ ∃ w : Fin 3 → ℕ,
      (∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ ∑ i, w i = N := by
  have hβ := d.middle_angle_le_two_pi_fifths_of_counterexample hn hnot h01 h12
  have hγ := d.tile_angle_le_two_pi_thirds_of_counterexample hn hnot 2
  have hα := angle_lower_of_relation_outside_seven _ _ _ d.tile.angle_sum hβ hγ t ht hne he
  have hP := d.corner_column_le_twenty_one_of_angle_lower 0 hα
  have hQ := d.ordered_middle_column_le_five h01 hγ
  obtain ⟨_, _, hscalene, hrep⟩ := d.rational_angles_of_counterexample hn hnot
  have hR := (d.ordered_corner_columns h01 h12 hscalene hrep).1
  let D := cornerLocalDeterminant (d.cornerColumnCount 0) (d.cornerColumnCount 1)
    (d.cornerColumnCount 2) t
  let a := cornerLocalAlphaNumerator (d.cornerColumnCount 0) (d.cornerColumnCount 1)
    (d.cornerColumnCount 2) t
  let b := cornerLocalBetaNumerator (d.cornerColumnCount 0) (d.cornerColumnCount 1)
    (d.cornerColumnCount 2) t
  have hD : D ≠ 0 := d.corner_local_determinant_ne_zero_of_counterexample hn hnot h01 h12
    t ht hne he
  have hDb : |D| ≤ 256 := corner_local_determinant_bound _ _ _ hP hQ hR t ht
  have hN : D.natAbs ≤ 256 := by
    have hh : (D.natAbs : ℤ) ≤ 256 := by simpa only [Int.natCast_natAbs] using hDb
    exact_mod_cast hh
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three] at hc
  obtain ⟨ha, hb⟩ := corner_local_elimination _ _ _ d.tile.angle_sum _ _ _ hc t he
  change (D : ℝ) * d.tile.angle 0 = (a : ℝ) * Real.pi at ha
  change (D : ℝ) * d.tile.angle 1 = (b : ℝ) * Real.pi at hb
  let v : Fin 3 → ℤ := ![a, b, D - a - b]
  have hv (i : Fin 3) : (D : ℝ) * d.tile.angle i = (v i : ℝ) * Real.pi := by
    fin_cases i
    · exact ha
    · exact hb
    · change (D : ℝ) * d.tile.angle 2 = ((D - a - b : ℤ) : ℝ) * Real.pi
      push_cast
      linear_combination (D : ℝ) * d.tile.angle_sum - ha - hb
  obtain ⟨hN3, w, hw, hwp, hws⟩ := d.tile.integer_angle_weights_of_scaled D hD v hv
  exact ⟨D.natAbs, hN3, hN, w, hw, hwp, hws⟩

theorem counterexample_small_relation_or_bounded_denominator {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2) :
    SmallAngleLocalRelation (d.tile.angle 0) (d.tile.angle 1) ∨
      ∃ N : ℕ, 3 ≤ N ∧ N ≤ 256 ∧ ∃ w : Fin 3 → ℕ,
        (∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N)) ∧
        (∀ i, 0 < w i ∧ w i < N) ∧ ∑ i, w i = N := by
  have hγ := d.tile_angle_le_two_pi_thirds_of_counterexample hn hnot 2
  have hne := d.tile_angle_ne_pi_half_of_counterexample hn hnot 2
  obtain ⟨_, _, hscalene, hrep⟩ := d.rational_angles_of_counterexample hn hnot
  obtain ⟨t, ht, he⟩ := nonright_relation_of_local_relation _ _ _ d.tile.angle_sum hne
    (d.ordered_local_relation h01 h12 hγ hscalene hrep)
  by_cases hm : t ∈ smallAngleRelationTriples
  · exact Or.inl ⟨t, hm, he⟩
  · exact Or.inr (d.bounded_denominator_of_relation_outside_seven hn hnot h01 h12 t ht hm he)

end Erdos633b.Tiling
