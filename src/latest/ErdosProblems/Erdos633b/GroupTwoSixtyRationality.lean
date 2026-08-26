import ErdosProblems.Erdos633b.GroupTwoSixtyColoring
import ErdosProblems.Erdos633b.GroupTwoSixtyMetric
import ErdosProblems.Erdos633b.GroupTwoSixtyAlgebra
import ErdosProblems.Erdos633b.GroupTwoSixtyBoundary
import ErdosProblems.Erdos633b.CaseSevenRationality
import ErdosProblems.Erdos633b.ShapeNecessity

/-! Rational tile sides and exact case-(4) necessity for the undoubled
sixty-degree group-2 shape, including arbitrary initial vertex orderings. -/

namespace Erdos633b.Tiling

theorem groupTwoSixty_rational_sides {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 0 + d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + 2 * d.tile.angle 1) : d.tile.RationalSides := by
  have hg : d.tile.angle 2 = 2 * Real.pi / 3 := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith [d.tile.angle_sum]
  have hirrA := d.groupTwo_first_angle_irrational hg hirr
  let x := d.tile.side 0 / d.tile.side 2
  let y := d.tile.side 1 / d.tile.side 2
  let k := T.side 1 / d.tile.side 2
  have hx : 0 < x := div_pos (d.tile.side_pos 0) (d.tile.side_pos 2)
  have hy : 0 < y := div_pos (d.tile.side_pos 1) (d.tile.side_pos 2)
  have hc := (d.tile.side_pos 2).ne'
  have hconic : x ^ 2 + x * y + y ^ 2 = 1 := d.tile.groupTwo_normalized_conic hg
  obtain ⟨hX, hZ⟩ := d.tile.groupTwoSixty_normalized_sides T hg h0 h1 h2
  change T.side 0 / d.tile.side 2 = k * x at hX
  change T.side 2 / d.tile.side 2 = k * (x + y) at hZ
  have hPm : (T.side 0 - T.side 1 + T.side 2) / d.tile.side 2 = k * (2 * x + y - 1) := by
    calc
      _ = T.side 0 / d.tile.side 2 - k + T.side 2 / d.tile.side 2 := by dsimp [k]; ring
      _ = k * x - k + k * (x + y) := by rw [hX, hZ]
      _ = _ := by ring
  have hPl : (T.side 0 + T.side 1 + T.side 2) / d.tile.side 2 = k * (2 * x + y + 1) := by
    calc
      _ = T.side 0 / d.tile.side 2 + k + T.side 2 / d.tile.side 2 := by dsimp [k]; ring
      _ = k * x + k + k * (x + y) := by rw [hX, hZ]
      _ = _ := by ring
  obtain ⟨M, L, hMp, hLp, hM, hL⟩ := d.groupTwoSixty_twin_equations hg hirr h1 h2
  have hM' : (M : ℝ) * (1 + x - y) = k * (2 * x + y - 1) := by
    calc
      _ = ((M : ℝ) * (d.tile.side 0 - d.tile.side 1 + d.tile.side 2)) / d.tile.side 2 := by
        dsimp only [x, y]
        field_simp [hc]
        ring
      _ = (T.side 0 - T.side 1 + T.side 2) / d.tile.side 2 := by rw [hM]
      _ = _ := hPm
  have hL' : (L : ℝ) * (1 - x + y) = k * (2 * x + y + 1) := by
    calc
      _ = ((L : ℝ) * (-d.tile.side 0 + d.tile.side 1 + d.tile.side 2)) / d.tile.side 2 := by
        dsimp only [x, y]
        field_simp [hc]
        ring
      _ = (T.side 0 + T.side 1 + T.side 2) / d.tile.side 2 := by rw [hL]
      _ = _ := hPl
  obtain ⟨hxr, K, hKr, hk⟩ := groupTwoSixty_rational_parameters hx hy hconic M L hMp hLp hM' hL'
  have hb (i : Fin 3) : T.side i / d.tile.side 2 =
      (d.boundarySideCount i 0 : ℝ) * x + d.boundarySideCount i 1 * y +
        d.boundarySideCount i 2 := by
    rw [d.side_eq_three_counts i]
    dsimp only [x, y]
    field_simp [hc]
  have hyr : IsRational y := by
    by_contra hn
    have he0 : (K * x) * y = (d.boundarySideCount 0 0 : ℝ) * x +
        d.boundarySideCount 0 1 * y + d.boundarySideCount 0 2 := by
      calc
        _ = k * x := by rw [hk]; ring
        _ = T.side 0 / d.tile.side 2 := hX.symm
        _ = _ := hb 0
    have he1 : K * y = (d.boundarySideCount 1 0 : ℝ) * x +
        d.boundarySideCount 1 1 * y + d.boundarySideCount 1 2 := by
      calc
        _ = k := hk.symm
        _ = _ := hb 1
    obtain ⟨hp0, hr0⟩ := pure_boundary_of_irrational_ratio hx hxr (hKr.mul hxr) hn
      (d.boundarySideCount 0 0) (d.boundarySideCount 0 1) (d.boundarySideCount 0 2) he0
    obtain ⟨hp1, hr1⟩ := pure_boundary_of_irrational_ratio hx hxr hKr hn
      (d.boundarySideCount 1 0) (d.boundarySideCount 1 1) (d.boundarySideCount 1 2) he1
    exact d.groupTwoSixty_not_two_pure_boundaries hg hirrA h2 ⟨hp0, hr0, hp1, hr1⟩
  apply d.tile.rationalSides_of_ratios_to 2
  intro i
  fin_cases i
  · exact hxr
  · exact hyr
  · refine ⟨1, ?_⟩
    change ((1 : ℚ) : ℝ) = d.tile.side 2 / d.tile.side 2
    rw [Rat.cast_one, div_self hc]

theorem groupTwoSixty_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 0 + d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + 2 * d.tile.angle 1) : EightCases T := by
  have hg : d.tile.angle 2 = 2 * Real.pi / 3 := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith [d.tile.angle_sum]
  exact case_four_of_groupTwo_third_shape d.tile T
    (d.groupTwoSixty_rational_sides hirr h0 h1 h2) hg h0 h1

theorem groupTwoSixty_necessary_of_reindex {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) (e f : Equiv.Perm (Fin 3))
    (h0 : Triangle.angle (T.reindex f) 0 = Triangle.angle (d.tile.reindex e) 0)
    (h1 : Triangle.angle (T.reindex f) 1 =
      Triangle.angle (d.tile.reindex e) 0 + Triangle.angle (d.tile.reindex e) 1)
    (h2 : Triangle.angle (T.reindex f) 2 =
      Triangle.angle (d.tile.reindex e) 0 + 2 * Triangle.angle (d.tile.reindex e) 1) :
    EightCases T := by
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  have hirrU : ¬ ∀ i, IsRational (U.angle i / Real.pi) := by
    intro h
    apply hirr
    intro i
    simpa only [U, Triangle.angle_reindex, Equiv.symm_apply_apply] using h (f i)
  apply eightCases_of_reindex T f
  exact d'.groupTwoSixty_necessary hirrU h0 h1 h2

end Erdos633b.Tiling
