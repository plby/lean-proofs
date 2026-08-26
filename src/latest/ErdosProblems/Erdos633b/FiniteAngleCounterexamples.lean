import ErdosProblems.Erdos633b.FiniteOrTwoPiThirds
import ErdosProblems.Erdos633b.TwoPiThirdsBoundedWeights
import ErdosProblems.Erdos633b.CornerAngleWeights

/-! Every hypothetical nonsquare counterexample to the eight-case
classification lies in an explicitly bounded finite angle domain.
This theorem does not assert that the finite domain has no counterexamples. -/

namespace Erdos633b.Tiling

theorem counterexample_ordered_bounded_weights {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) :
    ∃ e : Equiv.Perm (Fin 3),
      let S : Triangle := d.tile.reindex e
      S.angle 0 < S.angle 1 ∧ S.angle 1 < S.angle 2 ∧
        S.angle 1 ≤ 2 * Real.pi / 5 ∧ S.angle 2 ≤ 2 * Real.pi / 3 ∧
        S.angle 2 ≠ Real.pi / 2 ∧ (∀ i, IsRational (S.angle i / Real.pi)) ∧
        ∃ N : ℕ, 3 ≤ N ∧ N ≤ 256 ∧ ∃ w : Fin 3 → ℕ,
          (∀ i, S.angle i = (w i : ℝ) * (Real.pi / N)) ∧
          (∀ i, 0 < w i ∧ w i < N) ∧ ∑ i, w i = N := by
  obtain ⟨e, h01, h12, hβ, hγ, hne, hrat, hh⟩ :=
    d.counterexample_ordered_finite_or_two_pi_thirds hn hnot
  refine ⟨e, h01, h12, hβ, hγ, hne, hrat, ?_⟩
  rcases hh with hg | hw
  · exact (d.reindexTile e).counterexample_two_pi_thirds_bounded_weights hn hnot h01 h12 hg
  · exact hw

theorem counterexample_bounded_angle_weights {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) :
    ∃ N : ℕ, 3 ≤ N ∧ N ≤ 256 ∧ ∃ w : Fin 3 → ℕ,
      (∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ ∑ i, w i = N := by
  obtain ⟨e, _, _, _, _, _, _, N, hN, hNb, w, hw, hwp, hws⟩ :=
    d.counterexample_ordered_bounded_weights hn hnot
  exact ⟨N, hN, hNb, d.tile.angle_weights_of_reindex e N w hw hwp hws⟩

theorem counterexample_common_bounded_angle_weights {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) :
    ∃ N : ℕ, 3 ≤ N ∧ N ≤ 256 ∧ ∃ w c : Fin 3 → ℕ,
      (∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, T.angle i = (c i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ (∀ i, 0 < c i ∧ c i < N) ∧
      ∑ i, w i = N ∧ ∑ i, c i = N := by
  obtain ⟨N, hN, hNb, w, hw, hwp, hws⟩ := d.counterexample_bounded_angle_weights hn hnot
  obtain ⟨c, hc, hcp, hcs⟩ := d.integer_corner_weights N (by omega) w hw
  refine ⟨N, hN, hNb, w, c, hw, hc, hwp, ?_, hws, hcs⟩
  intro i
  refine ⟨hcp i, ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ : 0 < Real.pi / N := div_pos Real.pi_pos hNr
  have hi := T.angle_lt_pi i
  rw [hc i] at hi
  have hπ : Real.pi = (N : ℝ) * (Real.pi / N) := by field_simp
  exact_mod_cast (mul_lt_mul_iff_left₀ hδ).mp (hi.trans_eq hπ)

end Erdos633b.Tiling
