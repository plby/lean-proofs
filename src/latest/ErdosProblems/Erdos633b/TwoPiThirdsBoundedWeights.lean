import ErdosProblems.Erdos633b.GroupTwoBoundedWeights
import ErdosProblems.Erdos633b.BoundedCornerShapes
import ErdosProblems.Erdos633b.TwoPiThirdsCornerColumns
import ErdosProblems.Erdos633b.AngleWeightReindex

/-! The entire 120-degree counterexample regime has bounded positive
natural angle weights. Reptilings and both group-1 shapes are discharged
by their proved unconditional necessity theorems. -/

namespace Erdos633b.Tiling

theorem counterexample_six_shapes_bounded_weights {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi)) (hs : SixAngleShapes d.tile T) :
    ∃ N : ℕ, 3 ≤ N ∧ N ≤ 252 ∧ ∃ w : Fin 3 → ℕ,
      (∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ ∑ i, w i = N := by
  obtain ⟨e, f, hs⟩ := hs
  rcases hs with h1 | h2
  · rcases h1.2 with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · exact False.elim (hnot (d.caseSix_necessary_unconditional_reindex hn e f h0 h1 h2))
    · exact False.elim (hnot (d.caseSeven_necessary_unconditional_reindex hn e f h0 h1 h2))
  · let U : Triangle := T.reindex f
    let d' : Tiling U n := (d.reindexTile e).reindexOuter f
    have hr : ∀ i, IsRational (d'.tile.angle i / Real.pi) := by
      intro i
      change IsRational (Triangle.angle (d.tile.reindex e) i / Real.pi)
      simpa only [Triangle.angle_reindex] using hrat (e.symm i)
    obtain ⟨N, hN, hNb, w, hw, hwp, hws⟩ := d'.groupTwo_bounded_angle_weights hr h2
    refine ⟨N, hN, hNb, ?_⟩
    exact d.tile.angle_weights_of_reindex e N w hw hwp hws

theorem counterexample_two_pi_thirds_bounded_weights {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3) :
    ∃ N : ℕ, 3 ≤ N ∧ N ≤ 256 ∧ ∃ w : Fin 3 → ℕ,
      (∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ ∑ i, w i = N := by
  obtain ⟨hrat, _, hscalene, hrep⟩ := d.rational_angles_of_counterexample hn hnot
  rcases d.two_pi_thirds_bounded_weights_or_columns h01 h12 hscalene hrep hg with hw | hc
  · exact hw
  obtain ⟨hP, hQ, hR⟩ := hc
  have hs := (d.angle_shapes_of_bounded_columns hR (by omega) (by omega)
    (by omega) (by omega) hscalene).resolve_left hrep
  obtain ⟨N, hN, hNb, hw⟩ := d.counterexample_six_shapes_bounded_weights hn hnot hrat hs
  exact ⟨N, hN, by omega, hw⟩

end Erdos633b.Tiling
