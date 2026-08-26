import ErdosProblems.Erdos633b.DoubledOuterMetric
import ErdosProblems.Erdos633b.GroupTwoNormalization

/-! The outer coordinate triangle has exactly twice the two acute reference angles. -/

namespace Erdos633b

theorem Triangle.cos_eq_of_law (T : Triangle) (i : Fin 3) (z : ℝ)
    (h : T.side i ^ 2 = T.side (i + 1) ^ 2 + T.side (i + 2) ^ 2 -
      2 * T.side (i + 1) * T.side (i + 2) * z) : Real.cos (T.angle i) = z := by
  have hl := T.cosine_law i
  have hp : 0 < 2 * T.side (i + 1) * T.side (i + 2) := by
    exact mul_pos (mul_pos (by norm_num) (T.side_pos _)) (T.side_pos _)
  nlinarith

namespace DoubledCoordinates

open Sixty

theorem outer_angle_two (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (outer d hd a b c m ha hb hc hm).angle 2 = Real.pi / 3 := by
  let T := outer d hd a b c m ha hb hc hm
  have h0 : T.side 0 = m * b * (2 * a + b) := outer_sides d hd he a b c m ha hb hc hm hrel 0
  have h1 : T.side 1 = m * a * (a + 2 * b) := outer_sides d hd he a b c m ha hb hc hm hrel 1
  have h2 : T.side 2 = m * c ^ 2 := outer_sides d hd he a b c m ha hb hc hm hrel 2
  have hcos : Real.cos (T.angle 2) = 1 / 2 := by
    apply T.cos_eq_of_law 2
    change T.side 2 ^ 2 = T.side 0 ^ 2 + T.side 1 ^ 2 - 2 * T.side 0 * T.side 1 * (1 / 2)
    rw [h0, h1, h2, hrel]
    ring
  exact Real.injOn_cos ⟨(T.angle_pos 2).le, (T.angle_lt_pi 2).le⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩ (hcos.trans Real.cos_pi_div_three.symm)

theorem outer_angle_one (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (outer d hd a b c m ha hb hc hm).angle 1 =
      2 * (groupTwoReference d hd a b ha hb).angle 1 := by
  let T := outer d hd a b c m ha hb hc hm
  let R := groupTwoReference d hd a b ha hb
  have h0 : T.side 0 = m * b * (2 * a + b) := outer_sides d hd he a b c m ha hb hc hm hrel 0
  have h1 : T.side 1 = m * a * (a + 2 * b) := outer_sides d hd he a b c m ha hb hc hm hrel 1
  have h2 : T.side 2 = m * c ^ 2 := outer_sides d hd he a b c m ha hb hc hm hrel 2
  have hC : a ^ 2 + a * b + b ^ 2 ≠ 0 := by rw [← hrel]; exact (sq_pos_of_pos hc).ne'
  have hcos : Real.cos (T.angle 1) = 2 * ((a + 2 * b) / (2 * c)) ^ 2 - 1 := by
    apply T.cos_eq_of_law 1
    change T.side 1 ^ 2 = T.side 2 ^ 2 + T.side 0 ^ 2 -
      2 * T.side 2 * T.side 0 * (2 * ((a + 2 * b) / (2 * c)) ^ 2 - 1)
    rw [h0, h1, h2]
    simp only [div_pow, mul_pow]
    rw [hrel]
    field_simp
    ring
  have hR0 : R.angle 0 = 2 * Real.pi / 3 := reference_angle_zero d hd he a b c ha hb hc hrel
  apply Real.injOn_cos ⟨(T.angle_pos 1).le, (T.angle_lt_pi 1).le⟩
    ⟨by linarith [R.angle_pos 1], by linarith [R.angle_sum, R.angle_pos 2, Real.pi_pos]⟩
  rw [Real.cos_two_mul, reference_cos_one d hd he a b c ha hb hc hrel]
  exact hcos

theorem outer_angles (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let T := outer d hd a b c m ha hb hc hm
    let R := groupTwoReference d hd a b ha hb
    T.angle 0 = 2 * R.angle 2 ∧ T.angle 1 = 2 * R.angle 1 ∧ T.angle 2 = Real.pi / 3 := by
  let T := outer d hd a b c m ha hb hc hm
  let R := groupTwoReference d hd a b ha hb
  have h1 := outer_angle_one d hd he a b c m ha hb hc hm hrel
  have h2 := outer_angle_two d hd he a b c m ha hb hc hm hrel
  have hR0 := reference_angle_zero d hd he a b c ha hb hc hrel
  refine ⟨?_, h1, h2⟩
  change T.angle 0 = 2 * R.angle 2
  linarith [T.angle_sum, R.angle_sum]

end DoubledCoordinates
end Erdos633b
