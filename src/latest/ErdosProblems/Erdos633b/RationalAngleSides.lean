import ErdosProblems.Erdos633b.GroupTwoNecessity
import ErdosProblems.Erdos633b.TileIncommensurableNecessity
import Mathlib.NumberTheory.Niven

/-! Rational side ratios and commensurable angles force an equilateral
triangle. Thus the rational-side part of the remaining angle branch is
already covered by the first case. -/

namespace Erdos633b
namespace Triangle

theorem equilateral_of_angles_ge_pi_third (T : Triangle)
    (h : ∀ i, Real.pi / 3 ≤ T.angle i) : ∀ i, T.angle i = Real.pi / 3 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hs := T.angle_sum
  intro i
  fin_cases i
  · change T.angle 0 = Real.pi / 3
    linarith
  · change T.angle 1 = Real.pi / 3
    linarith
  · change T.angle 2 = Real.pi / 3
    linarith

theorem equilateral_of_rational_angles_and_sides (T : Triangle)
    (hrat : ∀ i, IsRational (T.angle i / Real.pi)) (hs : T.RationalSides) :
    ∀ i, T.angle i = Real.pi / 3 := by
  apply T.equilateral_of_angles_ge_pi_third
  intro i
  obtain ⟨q, hq⟩ := hrat i
  obtain ⟨r, hr⟩ := T.rational_cos_of_rationalSides hs i
  have ha : T.angle i = (q : ℝ) * Real.pi :=
    ((eq_div_iff Real.pi_ne_zero).mp hq).symm
  have h := niven_angle_eq ⟨q, ha⟩ ⟨r, hr.symm⟩
    ⟨(T.angle_pos i).le, (T.angle_lt_pi i).le⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h <;> linarith [T.angle_pos i, T.angle_lt_pi i, Real.pi_pos]

end Triangle
namespace Tiling

theorem tile_angle_le_outer_of_corner_count_pos {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i j : Fin 3) (h : 0 < d.cornerAngleCount i j) : d.tile.angle j ≤ T.angle i := by
  have hc : (1 : ℝ) ≤ d.cornerAngleCount i j := by exact_mod_cast h
  calc
    d.tile.angle j ≤ (d.cornerAngleCount i j : ℝ) * d.tile.angle j := by
      nlinarith [d.tile.angle_pos j]
    _ ≤ ∑ k : Fin 3, (d.cornerAngleCount i k : ℝ) * d.tile.angle k :=
      Finset.single_le_sum (fun k _ => mul_nonneg (Nat.cast_nonneg _)
        (d.tile.angle_pos k).le) (Finset.mem_univ j)
    _ = T.angle i := (d.angle_eq_sum_counts i).symm

theorem equilateral_of_equilateral_tile {T : Triangle} {n : ℕ} (d : Tiling T n)
    (he : ∀ j, d.tile.angle j = Real.pi / 3) : ∀ i, T.angle i = Real.pi / 3 := by
  apply T.equilateral_of_angles_ge_pi_third
  intro i
  obtain ⟨j, hj⟩ := d.corner_row_positive i
  simpa only [he j] using d.tile_angle_le_outer_of_corner_count_pos i j hj

theorem equilateral_of_rational_tile_angles_and_sides {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi))
    (hs : d.tile.RationalSides) : ∀ i, T.angle i = Real.pi / 3 :=
  d.equilateral_of_equilateral_tile (d.tile.equilateral_of_rational_angles_and_sides hrat hs)

theorem rational_sides_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hs : d.tile.RationalSides) : EightCases T := by
  by_cases hrat : ∀ i, IsRational (d.tile.angle i / Real.pi)
  · have he := d.equilateral_of_rational_tile_angles_and_sides hrat hs
    apply eightCases_of_not_injective_angles T
    intro hi
    exact T.not_equilateral_of_injective_angles hi he
  · exact d.incommensurable_tile_necessary hn hrat

theorem not_rational_sides_of_counterexample {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) : ¬ d.tile.RationalSides :=
  fun hs => hnot (d.rational_sides_necessary hn hs)

end Tiling
end Erdos633b
