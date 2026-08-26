import ErdosProblems.Erdos633b.CaseFiveColoring
import ErdosProblems.Erdos633b.CaseFiveMetric
import ErdosProblems.Erdos633b.RemainingRationalityAlgebra
import ErdosProblems.Erdos633b.CaseSevenRationality
import ErdosProblems.Erdos633b.ShapeNecessity

/-! Case-(5) necessity from two direction characters and actual area.
All reference-side rationality is proved, and all initial labels are allowed. -/

namespace Erdos633b.Tiling

theorem caseFive_rational_sides {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) : d.tile.RationalSides := by
  have hg : d.tile.angle 2 = 2 * Real.pi / 3 := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith [d.tile.angle_sum]
  let x := d.tile.side 0 / d.tile.side 2
  let y := d.tile.side 1 / d.tile.side 2
  let k := T.side 0 / d.tile.side 2
  have hx : 0 < x := div_pos (d.tile.side_pos 0) (d.tile.side_pos 2)
  have hy : 0 < y := div_pos (d.tile.side_pos 1) (d.tile.side_pos 2)
  have hk : 0 < k := div_pos (T.side_pos 0) (d.tile.side_pos 2)
  have hc := (d.tile.side_pos 2).ne'
  have hconic : x ^ 2 + x * y + y ^ 2 = 1 := d.tile.groupTwo_normalized_conic hg
  obtain ⟨hY, hZ⟩ := d.tile.caseFive_normalized_sides T hg h0 h1 h2
  change T.side 1 / d.tile.side 2 = k * (x + 2 * y) at hY
  change T.side 2 / d.tile.side 2 = 3 * k * (1 - x ^ 2) at hZ
  have hPm : (T.side 0 + T.side 1 - T.side 2) / d.tile.side 2 =
      k * (3 * x ^ 2 + x + 2 * y - 2) := by
    calc
      _ = k + T.side 1 / d.tile.side 2 - T.side 2 / d.tile.side 2 := by dsimp [k]; ring
      _ = k + k * (x + 2 * y) - 3 * k * (1 - x ^ 2) := by rw [hY, hZ]
      _ = _ := by ring
  have hPl : (-T.side 0 + T.side 1 + T.side 2) / d.tile.side 2 =
      k * (-3 * x ^ 2 + x + 2 * y + 2) := by
    calc
      _ = -k + T.side 1 / d.tile.side 2 + T.side 2 / d.tile.side 2 := by dsimp [k]; ring
      _ = -k + k * (x + 2 * y) + 3 * k * (1 - x ^ 2) := by rw [hY, hZ]
      _ = _ := by ring
  obtain ⟨M, L, _, _, hM, hL⟩ := d.caseFive_twin_equations hg hirr h1 h2
  have hM' : (M : ℝ) * (1 + x - y) = k * (3 * x ^ 2 + x + 2 * y - 2) := by
    calc
      _ = ((M : ℝ) * (d.tile.side 0 - d.tile.side 1 + d.tile.side 2)) / d.tile.side 2 := by
        dsimp only [x, y]
        field_simp [hc]
        ring
      _ = (T.side 0 + T.side 1 - T.side 2) / d.tile.side 2 := by rw [hM]
      _ = _ := hPm
  have hL' : (L : ℝ) * (1 - x + y) = k * (-3 * x ^ 2 + x + 2 * y + 2) := by
    calc
      _ = ((L : ℝ) * (-d.tile.side 0 + d.tile.side 1 + d.tile.side 2)) / d.tile.side 2 := by
        dsimp only [x, y]
        field_simp [hc]
        ring
      _ = (-T.side 0 + T.side 1 + T.side 2) / d.tile.side 2 := by rw [hL]
      _ = _ := hPl
  have harea : (n : ℝ) = 3 * k ^ 2 * (x + 2 * y) * (x + y) := d.caseFive_area_scale hg h0 h1 h2
  obtain ⟨hxr, hyr⟩ := caseFive_rational_pair_of_perimeter_area hx hy hk hconic M L hM' hL' n harea
  apply d.tile.rationalSides_of_ratios_to 2
  intro i
  fin_cases i
  · exact hxr
  · exact hyr
  · refine ⟨1, ?_⟩
    change ((1 : ℚ) : ℝ) = d.tile.side 2 / d.tile.side 2
    rw [Rat.cast_one, div_self hc]

theorem caseFive_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) : EightCases T := by
  have hg : d.tile.angle 2 = 2 * Real.pi / 3 := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith [d.tile.angle_sum]
  exact case_five_of_groupTwo_shape d.tile T (d.caseFive_rational_sides hirr h0 h1 h2) hg h0 h1

theorem caseFive_necessary_of_reindex {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) (e f : Equiv.Perm (Fin 3))
    (h0 : Triangle.angle (T.reindex f) 0 = Triangle.angle (d.tile.reindex e) 0)
    (h1 : Triangle.angle (T.reindex f) 1 = 2 * Triangle.angle (d.tile.reindex e) 0)
    (h2 : Triangle.angle (T.reindex f) 2 =
      3 * Triangle.angle (d.tile.reindex e) 1) : EightCases T := by
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  have hirrU : ¬ ∀ i, IsRational (U.angle i / Real.pi) := by
    intro h
    apply hirr
    intro i
    simpa only [U, Triangle.angle_reindex, Equiv.symm_apply_apply] using h (f i)
  apply eightCases_of_reindex T f
  exact d'.caseFive_necessary hirrU h0 h1 h2

end Erdos633b.Tiling
