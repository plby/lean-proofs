import ErdosProblems.Erdos633b.TilingSquareClass
import ErdosProblems.Erdos633b.TriquadraticComparison

/-! The nonsquare restriction for an arbitrary tiling of the second group-1
shape, once rationality of the tile sides is known. No coloring equation or
integral auxiliary scale is assumed. -/

namespace Erdos633b.Tiling

open TriquadraticCoordinates

theorem case_seven_conditions_of_groupOne {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hsides : d.tile.RationalSides)
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) :
    T.angle 2 = T.angle 0 / 2 + T.angle 1 ∧
      ∃ M K : ℕ, 0 < M ∧ 0 < K ∧
        2 * Real.sin (T.angle 0 / 4) = (M : ℝ) / K ∧
        ¬ IsSquare (2 * (K : ℤ) ^ 2 - (M : ℤ) ^ 2) := by
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith
  let s := 2 * Real.sin (d.tile.angle 0 / 2)
  have ha3 : d.tile.angle 0 < Real.pi / 3 := by linarith [d.tile.angle_pos 1]
  have hs : 0 < s := by
    dsimp [s]
    apply mul_pos (by norm_num)
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [d.tile.angle_pos 0])
      (by linarith [Real.pi_pos])
  have hs1 : s < 1 := by
    have hh := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [Real.pi_pos, d.tile.angle_pos 0] : -(Real.pi / 2) ≤ d.tile.angle 0 / 2)
      (by linarith [Real.pi_pos] : Real.pi / 6 ≤ Real.pi / 2)
      (by linarith : d.tile.angle 0 / 2 < Real.pi / 6)
    rw [Real.sin_pi_div_six] at hh
    dsimp [s]
    linarith
  obtain ⟨a, b, c, j, ha, hb, hc, hj, hac, hbj, hcj, hparam⟩ :=
    group_one_integer_data s hs hs1 (d.tile.groupOne_parameter_rational hrel hsides)
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hav : (a : ℝ) = (c : ℝ) * s := by
    have hh := (div_eq_iff hcR.ne').mp hparam
    linarith
  have hjv : (j : ℝ) = (c : ℝ) * s ^ 2 := by
    have hh : (j : ℝ) * c = (a : ℝ) ^ 2 := by exact_mod_cast hcj
    apply mul_right_cancel₀ hcR.ne'
    rw [hav] at hh
    nlinarith [hh]
  have hbv : (b : ℝ) = (c : ℝ) * (1 - s ^ 2) := by
    have hh : (b : ℝ) + (j : ℝ) = c := by exact_mod_cast hbj
    rw [hjv] at hh
    linarith
  have hrad : 0 < 4 - s ^ 2 := by nlinarith
  let v := Real.sqrt (4 - s ^ 2)
  have hv : 0 < v := Real.sqrt_pos.mpr hrad
  have hv2 : v ^ 2 = 4 - s ^ 2 := Real.sq_sqrt hrad.le
  let U := outer c s v hcR hs hs1 hv
  let R := reference c s v hcR hs hs1 hv
  let e : Tiling U (b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b) :=
    triquadratic_tiling c s v hcR hs hs1 hv hv2 a b j ha hb hj hav hbv hjv
  have hetile : e.tile = R := rfl
  have hU : ∀ i, U.angle i = T.angle i :=
    outer_angles_of_groupOne d.tile T h0 h1 h2 c s v hcR hs hs1 hv hv2 rfl
  have hR : ∀ i, e.tile.angle i = d.tile.angle i := by
    rw [hetile]
    exact reference_angles_of_groupOne d.tile hrel c s v hcR hs hs1 hv hv2 rfl
  have hUside : U.side 1 = (c : ℝ) * e.tile.side 1 := by
    rw [hetile, outer_side_one c s v hcR hs hs1 hv,
      reference_sides c s v hcR hs hs1 hv hv2]
    change (c : ℝ) ^ 2 * (1 - s ^ 2) = (c : ℝ) * (c * (1 - s ^ 2))
    ring
  have hscale : (T.side 1 / U.side 1) / (d.tile.side 1 / e.tile.side 1) =
      (T.side 1 / d.tile.side 1) / c := by
    rw [hUside]
    field_simp [hcR.ne', (d.tile.side_pos 1).ne', (e.tile.side_pos 1).ne']
  have hq : IsRational ((T.side 1 / U.side 1) / (d.tile.side 1 / e.tile.side 1)) := by
    rw [hscale]
    exact (d.rational_outer_side_ratio hsides 1 1).div ⟨c, by push_cast; rfl⟩
  have hns : ¬ IsSquare (2 * (c : ℤ) ^ 2 - (a : ℤ) ^ 2) := by
    intro hbad
    have hm : IsSquare (b ^ 2 + b ^ 2 + a ^ 2 + 2 * j * b) := by
      rw [triquadratic_nat_count a b c j hbj hcj]
      apply Int.isSquare_natCast_iff.mp
      have hle : a ^ 2 ≤ 2 * c ^ 2 := by nlinarith
      rw [Nat.cast_sub hle]
      exact_mod_cast hbad
    exact hn (d.square_count_of_comparison e hU hR 1 hq hm)
  refine ⟨by rw [h0, h1, h2]; ring, a, c, ha, hc, ?_, hns⟩
  rw [h0, show 2 * d.tile.angle 0 / 4 = d.tile.angle 0 / 2 by ring]
  exact hparam.symm

theorem case_seven_necessary_of_groupOne {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hsides : d.tile.RationalSides)
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) : EightCases T := by
  refine ⟨Equiv.refl _, ?_⟩
  right; right; right; right; right; right; left
  exact d.case_seven_conditions_of_groupOne hn hsides h0 h1 h2

end Erdos633b.Tiling
