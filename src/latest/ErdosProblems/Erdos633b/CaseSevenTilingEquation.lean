import ErdosProblems.Erdos633b.CaseSevenColoring
import ErdosProblems.Erdos633b.CaseSevenMetric

/-! Coloring and actual area imply a rational square of the case-(7)
parameter before rationality of the parameter itself is known. -/

namespace Erdos633b.Tiling

theorem caseSeven_tiling_equation {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : Irrational (d.tile.angle 0 / Real.pi))
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    ∃ M : ℤ, 0 < M ∧
      (M : ℝ) = (T.side 1 / d.tile.side 1) * (2 * Real.sin (d.tile.angle 0 / 2)) ∧
      (2 * Real.sin (d.tile.angle 0 / 2)) ^ 2 =
        2 * (M : ℝ) ^ 2 / ((M : ℝ) ^ 2 + n) := by
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith
  let s := 2 * Real.sin (d.tile.angle 0 / 2)
  let μ := T.side 1 / d.tile.side 1
  obtain ⟨hs, hs1⟩ := d.tile.groupOne_parameter_bounds hrel
  change 0 < s at hs
  change s < 1 at hs1
  obtain ⟨M, hM, hc⟩ := d.caseSeven_coloring_equation hrel hirr h1 h2
  obtain ⟨hX, hZ⟩ := d.tile.caseSeven_side_scale T h0 h1 h2
  have hY : T.side 1 = μ * d.tile.side 1 := by
    dsimp only [μ]
    exact (div_mul_cancel₀ _ (d.tile.side_pos 1).ne').symm
  obtain ⟨ha, hb⟩ := d.tile.groupOne_side_ratios hrel
  have ha' : d.tile.side 0 = d.tile.side 2 * s := by
    have h := (div_eq_iff (d.tile.side_pos 2).ne').mp ha
    simpa only [mul_comm, s] using h
  have hb' : d.tile.side 1 = d.tile.side 2 * (1 - s ^ 2) := by
    have h := (div_eq_iff (d.tile.side_pos 2).ne').mp hb
    simpa only [mul_comm, s] using h
  change T.side 0 = μ * ((2 - s ^ 2) * d.tile.side 0) at hX
  change T.side 2 = μ * d.tile.side 2 at hZ
  rw [hX, hZ, hY, ha', hb'] at hc
  have hfac : ((M : ℝ) - μ * s) * (d.tile.side 2 * (2 + s - s ^ 2)) = 0 := by
    linear_combination hc
  have hden : 0 < 2 + s - s ^ 2 := by nlinarith
  have hmu : (M : ℝ) = μ * s := sub_eq_zero.mp
    ((mul_eq_zero.mp hfac).resolve_right (mul_ne_zero (d.tile.side_pos 2).ne' hden.ne'))
  have harea := d.caseSeven_area_scale h0 h1 h2
  change (n : ℝ) = μ ^ 2 * (2 - s ^ 2) at harea
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hden2 : (M : ℝ) ^ 2 + n ≠ 0 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  refine ⟨M, hM, hmu, ?_⟩
  change s ^ 2 = _
  apply (eq_div_iff hden2).mpr
  rw [hmu, harea]
  ring

theorem caseSeven_parameter_square_rational {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : Irrational (d.tile.angle 0 / Real.pi))
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    IsRational ((2 * Real.sin (d.tile.angle 0 / 2)) ^ 2) := by
  obtain ⟨M, _, _, hs⟩ := d.caseSeven_tiling_equation hirr h0 h1 h2
  refine ⟨2 * (M : ℚ) ^ 2 / ((M : ℚ) ^ 2 + n), ?_⟩
  push_cast
  exact hs.symm

end Erdos633b.Tiling
