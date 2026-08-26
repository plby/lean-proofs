import ErdosProblems.Erdos633b.SmallAngleCounterexamples
import ErdosProblems.Erdos633b.BoundedCornerAngles

/-! Every remaining counterexample either uses a 120-degree reference
tile or has a common positive natural tile-angle denominator at most 256.
Neither remaining alternative is assumed to be impossible. -/

namespace Erdos633b.Tiling

theorem counterexample_bounded_denominator_of_not_two_pi_thirds {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hγne : d.tile.angle 2 ≠ 2 * Real.pi / 3) :
    ∃ N : ℕ, 3 ≤ N ∧ N ≤ 256 ∧ ∃ w : Fin 3 → ℕ,
      (∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ ∑ i, w i = N := by
  have hα := d.angle_lower_of_counterexample_not_two_pi_thirds hn hnot h01 h12 hγne
  have hP := d.corner_column_le_twenty_one_of_angle_lower 0 hα
  have hγ := d.tile_angle_le_two_pi_thirds_of_counterexample hn hnot 2
  have hQ := d.ordered_middle_column_le_five h01 hγ
  have hne := d.tile_angle_ne_pi_half_of_counterexample hn hnot 2
  obtain ⟨_, _, hscalene, hrep⟩ := d.rational_angles_of_counterexample hn hnot
  have hR := (d.ordered_corner_columns h01 h12 hscalene hrep).1
  obtain ⟨t, ht, he⟩ := nonright_relation_of_local_relation _ _ _ d.tile.angle_sum hne
    (d.ordered_local_relation h01 h12 hγ hscalene hrep)
  exact d.corner_angle_denominator_bound hP hQ hR t ht he
    (d.corner_local_determinant_ne_zero_of_not_two_pi_thirds hn hnot h01 h12 hγne t ht he)

theorem counterexample_ordered_finite_or_two_pi_thirds {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) :
    ∃ e : Equiv.Perm (Fin 3),
      let S : Triangle := d.tile.reindex e
      S.angle 0 < S.angle 1 ∧ S.angle 1 < S.angle 2 ∧
        S.angle 1 ≤ 2 * Real.pi / 5 ∧ S.angle 2 ≤ 2 * Real.pi / 3 ∧
        S.angle 2 ≠ Real.pi / 2 ∧ (∀ i, IsRational (S.angle i / Real.pi)) ∧
        (S.angle 2 = 2 * Real.pi / 3 ∨
          ∃ N : ℕ, 3 ≤ N ∧ N ≤ 256 ∧ ∃ w : Fin 3 → ℕ,
            (∀ i, S.angle i = (w i : ℝ) * (Real.pi / N)) ∧
            (∀ i, 0 < w i ∧ w i < N) ∧ ∑ i, w i = N) := by
  obtain ⟨e, h01, h12, hβ, hγ, hne, hrat, _⟩ := d.counterexample_ordered_small_middle hn hnot
  refine ⟨e, h01, h12, hβ, hγ, hne, hrat, ?_⟩
  by_cases h : Triangle.angle (d.tile.reindex e) 2 = 2 * Real.pi / 3
  · exact Or.inl h
  · exact Or.inr ((d.reindexTile e).counterexample_bounded_denominator_of_not_two_pi_thirds
      hn hnot h01 h12 h)

end Erdos633b.Tiling
