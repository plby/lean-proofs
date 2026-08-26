import ErdosProblems.Erdos633b.Descent
import ErdosProblems.Erdos633b.EulerTools

/-! Exclude negative rational points on the auxiliary cubic using an integral square-class proof. -/

namespace Erdos633b

theorem negative_cover_no_rational (r w : ℚ) :
    w ^ 2 ≠ -r ^ 4 + 10 * r ^ 2 - 1 := by
  intro he
  let u := r.num
  let v : ℤ := r.den
  have hv : v ≠ 0 := by dsimp [v]; exact_mod_cast r.den_nz
  have hvQ : (v : ℚ) ≠ 0 := by exact_mod_cast hv
  have he' : w ^ 2 = -((u : ℚ) / v) ^ 4 + 10 * ((u : ℚ) / v) ^ 2 - 1 := by
    simpa only [u, v, Int.cast_natCast, r.num_div_den] using he
  field_simp [hvQ] at he'
  have hS : IsSquare (-u ^ 4 + 10 * u ^ 2 * v ^ 2 - v ^ 4) := by
    apply Rat.isSquare_intCast_iff.mp
    refine ⟨w * (v : ℚ) ^ 2, ?_⟩
    push_cast
    nlinarith [he']
  obtain ⟨z, hz⟩ := hS
  exact negative_cover_no_primitive u v z r.isCoprime_num_den (by simpa [sq] using hz.symm)

theorem cubic_denominator_coprime (a b : ℤ) (hc : IsCoprime a b) :
    IsCoprime (a * b) (a ^ 2 + 10 * a * b + b ^ 2) := by
  have ha : IsCoprime a (a ^ 2 + 10 * a * b + b ^ 2) := by
    rw [show a ^ 2 + 10 * a * b + b ^ 2 = b ^ 2 + a * (a + 10 * b) by ring]
    exact (hc.pow_right (n := 2)).add_mul_left_right (a + 10 * b)
  have hb : IsCoprime b (a ^ 2 + 10 * a * b + b ^ 2) := by
    rw [show a ^ 2 + 10 * a * b + b ^ 2 = a ^ 2 + b * (10 * a + b) by ring]
    exact (hc.symm.pow_right (n := 2)).add_mul_left_right (10 * a + b)
  exact ha.mul_left hb

theorem negative_cubic_square_class (x y : ℚ) (hx : x < 0)
    (he : y ^ 2 = x ^ 3 + 10 * x ^ 2 + x) : IsSquare (-x) := by
  let a := x.num
  let b : ℤ := x.den
  let P : ℤ := a ^ 2 + 10 * a * b + b ^ 2
  have ha : a < 0 := Rat.num_neg.mpr hx
  have hb : 0 < b := by dsimp [b]; exact_mod_cast x.pos
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  have hc : IsCoprime a b := x.isCoprime_num_den
  have he' : y ^ 2 = ((a : ℚ) / b) ^ 3 + 10 * ((a : ℚ) / b) ^ 2 + (a : ℚ) / b := by
    simpa only [a, b, Int.cast_natCast, x.num_div_den] using he
  field_simp [hbQ] at he'
  have hS : IsSquare (a * b * P) := by
    apply Rat.isSquare_intCast_iff.mp
    refine ⟨y * (b : ℚ) ^ 2, ?_⟩
    dsimp [P]
    push_cast
    linear_combination -(b : ℚ) * he'
  have hpos : 0 < -(a * b) := neg_pos.mpr (mul_neg_of_neg_of_pos ha hb)
  have hcp : IsCoprime (-(a * b)) (-P) := (cubic_denominator_coprime a b hc).neg_left.neg_right
  have hneg : IsSquare (-(a * b)) := EulerDescent.square_factor hpos hcp
    (by simpa only [neg_mul_neg] using hS)
  have hnegQ : IsSquare (-(a * b : ℚ)) := by
    simpa only [Int.cast_neg, Int.cast_mul] using Rat.isSquare_intCast_iff.mpr hneg
  have heq : -x = -(a * b : ℚ) / (b : ℚ) ^ 2 := by
    have hx' : x = (a : ℚ) / b := by simpa only [a, b, Int.cast_natCast] using x.num_div_den.symm
    rw [hx']
    field_simp
  rw [heq]
  exact hnegQ.div (IsSquare.sq (b : ℚ))

theorem cubic_no_negative_x (x y : ℚ) (hx : x < 0) :
    y ^ 2 ≠ x ^ 3 + 10 * x ^ 2 + x := by
  intro he
  obtain ⟨r, hr⟩ := negative_cubic_square_class x y hx he
  have hr0 : r ≠ 0 := by intro hh; simp [hh] at hr; linarith
  have hx' : x = -r ^ 2 := by nlinarith [hr]
  apply negative_cover_no_rational r (y / r)
  rw [hx'] at he
  field_simp
  nlinarith [he]

/-- This interval includes every group-1 parameter in the triangle classification. -/
theorem case_six_parameter_nonsquare (s : ℚ) (hs : s ^ 2 < 2) :
    ¬ IsSquare ((2 - s ^ 2) * (3 - s ^ 2)) := by
  rintro ⟨z, hz⟩
  have he : z ^ 2 = (s ^ 2 - 2) * (s ^ 2 - 3) := by nlinarith [hz]
  let x := quarticX s z (-5)
  let x' := 2 * s ^ 2 + 2 * z - 5
  have hsum : x + x' < 0 := by dsimp [x, x', quarticX]; linarith
  have hprod : x * x' = 1 := by dsimp [x, x', quarticX]; nlinarith [he]
  have hx : x < 0 := by
    by_contra hh
    have hx0 : 0 ≤ x := le_of_not_gt hh
    have hx' : x' < 0 := by linarith
    have hh' := mul_nonpos_of_nonneg_of_nonpos hx0 hx'.le
    linarith
  exact cubic_no_negative_x x (quarticY s z (-5)) hx (caseSix_to_cubic s z he)

end Erdos633b
