import ErdosProblems.Erdos633b.GroupTwoDoubleColoring
import ErdosProblems.Erdos633b.GroupTwoDoubleMetric
import ErdosProblems.Erdos633b.GroupTwoDoubleAlgebra
import ErdosProblems.Erdos633b.CaseSevenRationality
import ErdosProblems.Erdos633b.ShapeNecessity

/-! Rationality and case-(4) necessity for actual tilings of the doubled
120-degree shape. No graph, virtual kite, or rational-side hypothesis is used. -/

namespace Erdos633b.Tiling

theorem groupTwoDouble_rational_sides {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) : d.tile.RationalSides := by
  have hg : d.tile.angle 2 = 2 * Real.pi / 3 := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith [d.tile.angle_sum]
  let x := d.tile.side 0 / d.tile.side 2
  let y := d.tile.side 1 / d.tile.side 2
  let k := T.side 2 / d.tile.side 2
  have hx : 0 < x := div_pos (d.tile.side_pos 0) (d.tile.side_pos 2)
  have hy : 0 < y := div_pos (d.tile.side_pos 1) (d.tile.side_pos 2)
  have hk : 0 < k := div_pos (T.side_pos 2) (d.tile.side_pos 2)
  have hc := (d.tile.side_pos 2).ne'
  have hconic : x ^ 2 + x * y + y ^ 2 = 1 := d.tile.groupTwo_normalized_conic hg
  have hne : x ≠ y := by
    intro he
    exact d.tile.groupTwo_short_sides_ne hg (d.groupTwo_first_angle_irrational hg hirr)
      ((div_left_inj' hc).mp he)
  obtain ⟨hX, hY⟩ := d.tile.groupTwoDouble_normalized_sides T hg h0 h1 h2
  change T.side 0 / d.tile.side 2 = k * (x * (x + 2 * y)) at hX
  change T.side 1 / d.tile.side 2 = k * (y * (2 * x + y)) at hY
  have hperim : (T.side 0 + T.side 1 - T.side 2) / d.tile.side 2 = 3 * k * x * y := by
    calc
      _ = T.side 0 / d.tile.side 2 + T.side 1 / d.tile.side 2 - k := by dsimp [k]; ring
      _ = k * (x * (x + 2 * y)) + k * (y * (2 * x + y)) - k := by rw [hX, hY]
      _ = _ := by linear_combination k * hconic
  obtain ⟨M, L, hMp, hLp, hM, hL⟩ := d.groupTwoDouble_twin_equations hg hirr h0 h1 h2
  have hM' : (M : ℝ) * (1 + x - y) = 3 * k * x * y := by
    calc
      _ = ((M : ℝ) * (d.tile.side 0 - d.tile.side 1 + d.tile.side 2)) / d.tile.side 2 := by
        dsimp only [x, y]
        field_simp [hc]
        ring
      _ = (T.side 0 + T.side 1 - T.side 2) / d.tile.side 2 := by rw [hM]
      _ = _ := hperim
  have hL' : (L : ℝ) * (1 - x + y) = 3 * k * x * y := by
    calc
      _ = ((L : ℝ) * (-d.tile.side 0 + d.tile.side 1 + d.tile.side 2)) / d.tile.side 2 := by
        dsimp only [x, y]
        field_simp [hc]
        ring
      _ = (T.side 0 + T.side 1 - T.side 2) / d.tile.side 2 := by rw [hL]
      _ = _ := hperim
  obtain ⟨hd, hxy, hkr⟩ := groupTwoDouble_rational_parameters hx hy hconic M L hMp hLp hM' hL'
  have hb (i : Fin 3) : T.side i / d.tile.side 2 =
      (d.boundarySideCount i 0 : ℝ) * x + d.boundarySideCount i 1 * y +
        d.boundarySideCount i 2 := by
    rw [d.side_eq_three_counts i]
    dsimp only [x, y]
    field_simp [hc]
  obtain ⟨hxr, hyr⟩ := rational_pair_of_nonnegative_boundary_counts hconic hk.ne' hne hd hxy hkr
    (d.boundarySideCount 0 0) (d.boundarySideCount 0 1) (d.boundarySideCount 0 2)
    (d.boundarySideCount 1 0) (d.boundarySideCount 1 1) (d.boundarySideCount 1 2)
    (hX.symm.trans (hb 0)) (hY.symm.trans (hb 1))
  apply d.tile.rationalSides_of_ratios_to 2
  intro i
  fin_cases i
  · exact hxr
  · exact hyr
  · refine ⟨1, ?_⟩
    change ((1 : ℚ) : ℝ) = d.tile.side 2 / d.tile.side 2
    rw [Rat.cast_one, div_self hc]

theorem groupTwoDouble_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) : EightCases T := by
  have hg : d.tile.angle 2 = 2 * Real.pi / 3 := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith [d.tile.angle_sum]
  exact case_four_of_groupTwo_fourth_shape d.tile T
    (d.groupTwoDouble_rational_sides hirr h0 h1 h2) hg h0 h2

theorem groupTwoDouble_necessary_of_reindex {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) (e f : Equiv.Perm (Fin 3))
    (h0 : Triangle.angle (T.reindex f) 0 = 2 * Triangle.angle (d.tile.reindex e) 0)
    (h1 : Triangle.angle (T.reindex f) 1 = 2 * Triangle.angle (d.tile.reindex e) 1)
    (h2 : Triangle.angle (T.reindex f) 2 =
      Triangle.angle (d.tile.reindex e) 0 + Triangle.angle (d.tile.reindex e) 1) :
    EightCases T := by
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  have hirrU : ¬ ∀ i, IsRational (U.angle i / Real.pi) := by
    intro h
    apply hirr
    intro i
    simpa only [U, Triangle.angle_reindex, Equiv.symm_apply_apply] using h (f i)
  apply eightCases_of_reindex T f
  exact d'.groupTwoDouble_necessary hirrU h0 h1 h2

end Erdos633b.Tiling
