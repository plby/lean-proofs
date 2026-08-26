import ErdosProblems.Erdos633b.GroupTwoStacking
import ErdosProblems.Erdos633b.SixtyRotations

/-! A complete equilateral tiling for every integral 120-degree tile. -/

namespace Erdos633b.Sixty

open GroupTwoDimensions

noncomputable def equilateralOuter (d : ℝ) (hd : 0 < d) (q : ℝ) (hq : 0 < q) : Triangle :=
  (frame d hd).homothetic ((frame d hd).points 0) (3 * q) (mul_pos (by norm_num) hq).ne'

theorem frame_side (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (i : Fin 3) :
    (frame d hd).side i = 1 := by
  have hsq : (frame d hd).side i ^ 2 = 1 := by
    rw [side_sq_of_points d he (frame d hd) 0 0 1 0 0 1 rfl]
    fin_cases i
    · change (1 - 0 : ℝ) ^ 2 + (1 - 0) * (0 - 1) + (0 - 1) ^ 2 = 1
      norm_num
    · change (0 - 0 : ℝ) ^ 2 + (0 - 0) * (1 - 0) + (1 - 0) ^ 2 = 1
      norm_num
    · change (0 - 1 : ℝ) ^ 2 + (0 - 1) * (0 - 0) + (0 - 0) ^ 2 = 1
      norm_num
  nlinarith [(frame d hd).side_pos i]

theorem equilateralOuter_side (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (q : ℝ) (hq : 0 < q) (i : Fin 3) : (equilateralOuter d hd q hq).side i = 3 * q := by
  change Triangle.side (((frame d hd).dilate (3 * q) _).move _) i = _
  rw [Triangle.side_move, Triangle.side_dilate, abs_of_pos (mul_pos (by norm_num) hq),
    frame_side d hd he, mul_one]

noncomputable def trapezoidSize (a b : ℕ) : ℝ := (scale a b : ℝ) * ((a : ℝ) * b)

theorem trapezoidSize_pos (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : 0 < trapezoidSize a b := by
  exact mul_pos (by exact_mod_cast scale_pos a b)
    (mul_pos (by exact_mod_cast ha) (by exact_mod_cast hb))

/-- All pieces are rigid copies of the explicitly constructed integral 120-degree reference tile. -/
noncomputable def group_two_equilateral_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      (equilateralOuter d hd (trapezoidSize a b) (trapezoidSize_pos a b ha hb)).support
      (9 * scale a b ^ 2 * (a * b)) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  let R := groupTwoReference d hd a b har hbr
  let F := frame d hd
  let q := trapezoidSize a b
  let n := 3 * scale a b ^ 2 * (a * b)
  have hq : 0 < q := trapezoidSize_pos a b ha hb
  have first : Patch R (EquilateralPartition.region F q .first) n := by
    rw [EquilateralPartition.first_eq_trapezoid]
    exact large_trapezoid_patch d hd he a b c ha hb hc hrel
  have second := first.move (turn d he q)
  rw [turn_image_first d hd he q] at second
  have third := second.move (turn d he q)
  rw [turn_image_second d hd he q] at third
  have patches : ∀ k, Patch R (EquilateralPartition.region F q k) n := by
    intro k
    cases k
    · exact first
    · exact second
    · exact third
  have result := EquilateralPartition.assemble_patch F R q hq n patches
  have hcount : 3 * n = 9 * scale a b ^ 2 * (a * b) := by dsimp only [n]; ring
  rwa [hcount] at result

noncomputable def group_two_equilateral_tiling (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Tiling (equilateralOuter d hd (trapezoidSize a b) (trapezoidSize_pos a b ha hb))
      (9 * scale a b ^ 2 * (a * b)) :=
  (group_two_equilateral_patch d hd he a b c ha hb hc hrel).toTiling

end Erdos633b.Sixty
