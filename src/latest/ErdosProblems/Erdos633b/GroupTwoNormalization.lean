import ErdosProblems.Erdos633b.SixtyAngles
import ErdosProblems.Erdos633b.GroupTwoParameters

/-! Rational half-angle parameters produce the actual integer reference triangles. -/

namespace Erdos633b.Sixty

theorem reference_sides (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (i : Fin 3) :
    (groupTwoReference d hd a b ha hb).side i = ![c, a, b] i := by
  let R := groupTwoReference d hd a b ha hb
  have hsq := groupTwoReference_side_sq d hd he a b c ha hb hrel i
  have hpos := R.side_pos i
  fin_cases i
  · change R.side 0 ^ 2 = c ^ 2 at hsq
    change 0 < R.side 0 at hpos
    change R.side 0 = c
    nlinarith
  · change R.side 1 ^ 2 = a ^ 2 at hsq
    change 0 < R.side 1 at hpos
    change R.side 1 = a
    nlinarith
  · change R.side 2 ^ 2 = b ^ 2 at hsq
    change 0 < R.side 2 at hpos
    change R.side 2 = b
    nlinarith

theorem reference_cos_one (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Real.cos ((groupTwoReference d hd a b ha hb).angle 1) = (a + 2 * b) / (2 * c) := by
  let R := groupTwoReference d hd a b ha hb
  have h0 : R.side 0 = c := reference_sides d hd he a b c ha hb hc hrel 0
  have h1 : R.side 1 = a := reference_sides d hd he a b c ha hb hc hrel 1
  have h2 : R.side 2 = b := reference_sides d hd he a b c ha hb hc hrel 2
  have hlaw := R.cosine_law 1
  change R.side 1 ^ 2 = R.side 2 ^ 2 + R.side 0 ^ 2 -
    2 * R.side 2 * R.side 0 * Real.cos (R.angle 1) at hlaw
  rw [h0, h1, h2] at hlaw
  have hp : b * (2 * c * Real.cos (R.angle 1) - (a + 2 * b)) = 0 := by nlinarith
  have hz := (mul_eq_zero.mp hp).resolve_left hb.ne'
  apply (eq_div_iff (mul_pos (by norm_num) hc).ne').mpr
  linarith

theorem reference_angle_zero (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (groupTwoReference d hd a b ha hb).angle 0 = 2 * Real.pi / 3 := by
  let R := groupTwoReference d hd a b ha hb
  have h0 : R.side 0 = c := reference_sides d hd he a b c ha hb hc hrel 0
  have h1 : R.side 1 = a := reference_sides d hd he a b c ha hb hc hrel 1
  have h2 : R.side 2 = b := reference_sides d hd he a b c ha hb hc hrel 2
  have hlaw := R.cosine_law 0
  change R.side 0 ^ 2 = R.side 1 ^ 2 + R.side 2 ^ 2 -
    2 * R.side 1 * R.side 2 * Real.cos (R.angle 0) at hlaw
  rw [h0, h1, h2] at hlaw
  have hcos : Real.cos (R.angle 0) = -(1 / 2) := by nlinarith [mul_pos ha hb]
  have hc3 : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  exact Real.injOn_cos ⟨(R.angle_pos 0).le, (R.angle_lt_pi 0).le⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩ (hcos.trans hc3.symm)

theorem integral_reference_of_rational_parameter (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (α : ℝ) (hα : 0 < α) (hα3 : α < Real.pi / 3)
    (hrat : IsRational (Real.sqrt 3 * Real.tan (α / 2))) :
    ∃ a b c : ℕ, ∃ ha : 0 < a, ∃ hb : 0 < b, 0 < c ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧
      (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb)).angle 1 = α := by
  obtain ⟨q, hq⟩ := hrat
  have hbounds := GroupTwoParameters.half_parameter_bounds α hα hα3
  rw [← hq] at hbounds
  obtain ⟨u, v, hu, hv, hqv⟩ := GroupTwoParameters.positive_parts q hbounds.1 hbounds.2
  let a := GroupTwoParameters.a u v
  let b := GroupTwoParameters.b u v
  let c := GroupTwoParameters.c u v
  have ha : 0 < a := GroupTwoParameters.a_pos u v hu hv
  have hb : 0 < b := GroupTwoParameters.b_pos u v hu hv
  have hc : 0 < c := GroupTwoParameters.c_pos u v hu hv
  have hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2 := GroupTwoParameters.relation u v
  refine ⟨a, b, c, ha, hb, hc, hrel, ?_⟩
  let R := groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hαπ : α < Real.pi := by linarith [Real.pi_pos]
  have hcos := groupTwo_cos_coordinate α q (cos_ne_neg_one_of_triangle_angle α hα hαπ) hq
  rw [hqv] at hcos
  have hr := reference_cos_one d hd he a b c (by exact_mod_cast ha)
    (by exact_mod_cast hb) (by exact_mod_cast hc) (by exact_mod_cast hrel)
  have heq : Real.cos (R.angle 1) = Real.cos α :=
    hr.trans ((GroupTwoParameters.cosine_ratio u v hu hv).trans hcos.symm)
  exact Real.injOn_cos ⟨(R.angle_pos 1).le, (R.angle_lt_pi 1).le⟩ ⟨hα.le, hαπ.le⟩ heq

end Erdos633b.Sixty
