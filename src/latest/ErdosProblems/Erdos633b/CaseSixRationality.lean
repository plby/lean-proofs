import ErdosProblems.Erdos633b.CaseSixColoring
import ErdosProblems.Erdos633b.CaseSixMetric
import ErdosProblems.Erdos633b.RemainingRationalityAlgebra
import ErdosProblems.Erdos633b.CaseSevenBranch
import ErdosProblems.Erdos633b.ShapeNecessity

/-! Direct case-(6) rationality from two genuine character equations and
area. The essential-segment source identity is not used. -/

namespace Erdos633b.Tiling

theorem caseSix_parameter_rational {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 2 * d.tile.angle 1) :
    IsRational (2 * Real.sin (d.tile.angle 0 / 2)) := by
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith
  let s := 2 * Real.sin (d.tile.angle 0 / 2)
  let k := T.side 0 / d.tile.side 2
  obtain ⟨hs, hs1⟩ := d.tile.groupOne_parameter_bounds hrel
  change 0 < s at hs
  change s < 1 at hs1
  have hk : 0 < k := div_pos (T.side_pos 0) (d.tile.side_pos 2)
  have hc := (d.tile.side_pos 2).ne'
  obtain ⟨ha, hb⟩ := d.tile.groupOne_side_ratios hrel
  change d.tile.side 0 / d.tile.side 2 = s at ha
  change d.tile.side 1 / d.tile.side 2 = 1 - s ^ 2 at hb
  have hNormPlus (J : ℤ) : ((J : ℝ) *
      (d.tile.side 0 + d.tile.side 1 + d.tile.side 2)) / d.tile.side 2 =
        (J : ℝ) * (2 + s - s ^ 2) := by
    calc
      _ = (J : ℝ) * (d.tile.side 0 / d.tile.side 2 + d.tile.side 1 / d.tile.side 2 + 1) := by
        field_simp [hc]
      _ = _ := by rw [ha, hb]; ring
  have hNormMinus (J : ℤ) : ((J : ℝ) *
      (-d.tile.side 0 + d.tile.side 1 + d.tile.side 2)) / d.tile.side 2 =
        (J : ℝ) * (2 - s - s ^ 2) := by
    calc
      _ = (J : ℝ) * (-(d.tile.side 0 / d.tile.side 2) + d.tile.side 1 / d.tile.side 2 + 1) := by
        field_simp [hc]
      _ = _ := by rw [ha, hb]; ring
  obtain ⟨M, L, hMp, hLp, hM, hL⟩ := d.caseSix_twin_equations hrel
    (d.groupOne_first_angle_irrational hrel hirr) h1 h2
  have htwin : (M : ℝ) * (2 + s - s ^ 2) = (L : ℝ) * (2 - s - s ^ 2) := by
    rw [← hNormPlus M, ← hNormMinus L, hM, hL]
  obtain ⟨hY, hZ⟩ := d.tile.caseSix_normalized_sides T hrel h0 h1 h2
  change T.side 1 / d.tile.side 2 = k * (2 - s ^ 2) at hY
  change T.side 2 / d.tile.side 2 = k * (1 - s ^ 2) * (3 - s ^ 2) at hZ
  have hPerim : (-T.side 0 + T.side 1 + T.side 2) / d.tile.side 2 =
      k * (2 + s - s ^ 2) * ((1 - s) * (2 + s)) := by
    calc
      _ = -k + T.side 1 / d.tile.side 2 + T.side 2 / d.tile.side 2 := by dsimp [k]; ring
      _ = -k + k * (2 - s ^ 2) + k * (1 - s ^ 2) * (3 - s ^ 2) := by rw [hY, hZ]
      _ = _ := by ring
  have hM' : (M : ℝ) = k * (1 - s) * (2 + s) := by
    have hp : 0 < 2 + s - s ^ 2 := by nlinarith
    apply mul_right_cancel₀ hp.ne'
    have he : (M : ℝ) * (2 + s - s ^ 2) =
        k * (2 + s - s ^ 2) * ((1 - s) * (2 + s)) := by
      rw [← hNormPlus M, hM, hPerim]
    linear_combination he
  have harea : (n : ℝ) = k ^ 2 * (2 - s ^ 2) * (3 - s ^ 2) :=
    d.caseSix_area_scale hrel h0 h1 h2
  exact caseSix_rational_parameter_of_perimeter_area hs hs1 hk M L hMp hLp htwin hM' n harea

theorem caseSix_rational_sides {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 2 * d.tile.angle 1) : d.tile.RationalSides := by
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith
  exact d.tile.rationalSides_of_groupOne_parameter hrel (d.caseSix_parameter_rational hirr h0 h1 h2)

theorem caseSix_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 2 * d.tile.angle 1) : EightCases T :=
  case_six_of_groupOne_shape d.tile T (d.caseSix_rational_sides hirr h0 h1 h2) h0 h1 h2

theorem caseSix_necessary_of_reindex {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) (e f : Equiv.Perm (Fin 3))
    (h0 : Triangle.angle (T.reindex f) 0 = Triangle.angle (d.tile.reindex e) 0)
    (h1 : Triangle.angle (T.reindex f) 1 = 2 * Triangle.angle (d.tile.reindex e) 0)
    (h2 : Triangle.angle (T.reindex f) 2 = 2 * Triangle.angle (d.tile.reindex e) 1) :
    EightCases T := by
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  have hirrU : ¬ ∀ i, IsRational (U.angle i / Real.pi) := by
    intro h
    apply hirr
    intro i
    simpa only [U, Triangle.angle_reindex, Equiv.symm_apply_apply] using h (f i)
  apply eightCases_of_reindex T f
  exact d'.caseSix_necessary hirrU h0 h1 h2

end Erdos633b.Tiling
