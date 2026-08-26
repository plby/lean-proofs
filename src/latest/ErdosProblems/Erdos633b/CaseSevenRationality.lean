import ErdosProblems.Erdos633b.CaseSevenTilingEquation
import ErdosProblems.Erdos633b.CaseSevenBoundary
import ErdosProblems.Erdos633b.CaseSevenNecessity

/-! The case-(7) tile has rational sides. The proof uses coloring, area,
and a genuine boundary corner, with no essential-segment theorem assumed. -/

namespace Erdos633b
namespace Triangle

theorem rationalSides_of_ratios_to (S : Triangle) (k : Fin 3)
    (h : ∀ i, IsRational (S.side i / S.side k)) : S.RationalSides := by
  intro i j
  have he : S.side i / S.side j = (S.side i / S.side k) / (S.side j / S.side k) := by
    field_simp [(S.side_pos j).ne', (S.side_pos k).ne']
  rw [he]
  exact (h i).div (h j)

theorem rationalSides_of_groupOne_parameter (S : Triangle)
    (hrel : 3 * S.angle 0 + 2 * S.angle 1 = Real.pi)
    (hs : IsRational (2 * Real.sin (S.angle 0 / 2))) : S.RationalSides := by
  obtain ⟨q, hq⟩ := hs
  obtain ⟨ha, hb⟩ := S.groupOne_side_ratios hrel
  apply S.rationalSides_of_ratios_to 2
  intro i
  fin_cases i
  · exact ⟨q, hq.trans ha.symm⟩
  · refine ⟨1 - q ^ 2, ?_⟩
    push_cast
    rw [hq, hb]
  · refine ⟨1, ?_⟩
    change ((1 : ℚ) : ℝ) = S.side 2 / S.side 2
    rw [Rat.cast_one, div_self (S.side_pos 2).ne']

end Triangle
namespace Tiling

theorem caseSeven_parameter_rational {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : Irrational (d.tile.angle 0 / Real.pi))
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    IsRational (2 * Real.sin (d.tile.angle 0 / 2)) := by
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith
  let s := 2 * Real.sin (d.tile.angle 0 / 2)
  let μ := T.side 1 / d.tile.side 1
  obtain ⟨M, _, hM, _⟩ := d.caseSeven_tiling_equation hirr h0 h1 h2
  change (M : ℝ) = μ * s at hM
  obtain ⟨r, hr⟩ := d.caseSeven_parameter_square_rational hirr h0 h1 h2
  change (r : ℝ) = s ^ 2 at hr
  obtain ⟨ha, hb⟩ := d.tile.groupOne_side_ratios hrel
  change d.tile.side 0 / d.tile.side 2 = s at ha
  change d.tile.side 1 / d.tile.side 2 = 1 - s ^ 2 at hb
  have hbound : μ * (1 - s ^ 2) =
      (d.boundarySideCount 1 0 : ℝ) * s +
      (d.boundarySideCount 1 1 : ℝ) * (1 - s ^ 2) + d.boundarySideCount 1 2 := by
    rw [← hb, ← ha]
    dsimp only [μ]
    rw [d.side_eq_three_counts 1]
    field_simp [(d.tile.side_pos 1).ne', (d.tile.side_pos 2).ne']
  have hpos := d.caseSeven_boundary_non_a_pos hrel hirr h0
  have hbr : 0 < 1 - (r : ℝ) := by
    rw [hr, ← hb]
    exact div_pos (d.tile.side_pos 1) (d.tile.side_pos 2)
  have hden : 0 < (d.boundarySideCount 1 1 : ℝ) * (1 - (r : ℝ)) +
      d.boundarySideCount 1 2 := by
    have hq : (0 : ℝ) ≤ d.boundarySideCount 1 1 := Nat.cast_nonneg _
    have ht : (0 : ℝ) ≤ d.boundarySideCount 1 2 := Nat.cast_nonneg _
    have hqt : (0 : ℝ) < d.boundarySideCount 1 1 + d.boundarySideCount 1 2 := by
      exact_mod_cast hpos
    nlinarith
  refine ⟨((M : ℚ) * (1 - r) - (d.boundarySideCount 1 0 : ℚ) * r) /
    ((d.boundarySideCount 1 1 : ℚ) * (1 - r) + d.boundarySideCount 1 2), ?_⟩
  push_cast
  change _ = s
  apply (div_eq_iff hden.ne').mpr
  rw [hr, hM]
  linear_combination s * hbound

theorem caseSeven_rational_sides {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : Irrational (d.tile.angle 0 / Real.pi))
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) : d.tile.RationalSides := by
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith
  exact d.tile.rationalSides_of_groupOne_parameter hrel
    (d.caseSeven_parameter_rational hirr h0 h1 h2)

theorem caseSeven_necessary {T : Triangle} {n : ℕ} (d : Tiling T n) (hn : ¬ IsSquare n)
    (hirr : Irrational (d.tile.angle 0 / Real.pi))
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) : EightCases T :=
  d.case_seven_necessary_of_groupOne hn (d.caseSeven_rational_sides hirr h0 h1 h2) h0 h1 h2

end Tiling
end Erdos633b
