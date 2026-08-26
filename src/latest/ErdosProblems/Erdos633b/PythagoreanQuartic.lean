import ErdosProblems.Erdos633b.PythagoreanDescent

/-! The quartic and count exclusions D4, obtained from the doubled-leg descent. -/

namespace Erdos633b.PythagoreanDescent

theorem no_coprime_pair (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : IsCoprime a b)
    (hs1 : IsSquare (a ^ 2 + b ^ 2)) (hs2 : IsSquare (a ^ 2 + 4 * b ^ 2)) : False := by
  rcases Int.emod_two_eq_zero_or_one a with heven | hodd
  · have hbodd : b % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one b with hb0 | hb1
      · have hunit : IsUnit (2 : ℤ) := hc.isUnit_of_dvd'
          (Int.dvd_of_emod_eq_zero heven) (Int.dvd_of_emod_eq_zero hb0)
        norm_num [Int.isUnit_iff] at hunit
      · exact hb1
    obtain ⟨t, hat⟩ := Int.dvd_of_emod_eq_zero heven
    have ht : 0 < t := by omega
    have hbt : IsCoprime b t := hc.symm.of_isCoprime_of_dvd_right
      ⟨2, by simpa [mul_comm] using hat⟩
    have hfirst : IsSquare (b ^ 2 + t ^ 2) := by
      have hh : IsSquare (a ^ 2 + 4 * b ^ 2 : ℚ) := by
        simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using
          Rat.isSquare_intCast_iff.mpr hs2
      have he : (a ^ 2 + 4 * b ^ 2 : ℚ) = (2 : ℚ) ^ 2 * ((b : ℚ) ^ 2 + (t : ℚ) ^ 2) := by
        have hat' : (a : ℚ) = 2 * t := by exact_mod_cast hat
        rw [hat']; ring
      rw [he] at hh
      have hh' := (isSquare_sq_mul_iff (2 : ℚ) _ (by norm_num)).mp hh
      apply Rat.isSquare_intCast_iff.mp
      simpa only [Int.cast_add, Int.cast_pow] using hh'
    have hsecond : IsSquare (b ^ 2 + 4 * t ^ 2) := by
      rw [hat] at hs1
      convert hs1 using 1; ring
    exact no_primitive_pair b t ⟨hbodd, ht, hbt, hfirst, hsecond⟩
  · exact no_primitive_pair a b ⟨hodd, hb, hc, hs1, hs2⟩

theorem diff_squares_product_coprime (p q : ℤ) (hc : IsCoprime p q) :
    IsCoprime (q ^ 2 - p ^ 2) (p * q) := by
  have hp : IsCoprime (q ^ 2 - p ^ 2) p := by
    rw [show q ^ 2 - p ^ 2 = q ^ 2 + (-p) * p by ring]
    exact (hc.symm.pow_left (m := 2)).add_mul_right_left (-p)
  have hq : IsCoprime (q ^ 2 - p ^ 2) q := by
    rw [show q ^ 2 - p ^ 2 = -(p ^ 2) + q * q by ring]
    exact (hc.pow_left (m := 2)).neg_left.add_mul_right_left q
  exact hp.mul_right hq

theorem quartic_no_strict (p q z : ℤ) (hp : 0 < p) (hpq : p < q)
    (hc : IsCoprime p q) (he : z ^ 2 = p ^ 4 - p ^ 2 * q ^ 2 + q ^ 4) : False := by
  apply no_coprime_pair (q ^ 2 - p ^ 2) (p * q) (by nlinarith) (mul_pos hp (hp.trans hpq))
    (diff_squares_product_coprime p q hc)
  · exact ⟨z, by nlinarith [he]⟩
  · exact ⟨p ^ 2 + q ^ 2, by ring⟩

theorem rational_quartic_obstruction (r : ℚ) (hr : 0 < r) (hr1 : r < 1)
    (hs : IsSquare r) (hQ : IsSquare (r ^ 2 - r + 1)) : False := by
  let u := r.num
  let v : ℤ := r.den
  have hu : 0 < u := Rat.num_pos.mpr hr
  have hv : 0 < v := by dsimp [v]; exact_mod_cast r.pos
  have hc : IsCoprime u v := r.isCoprime_num_den
  have hm : r * (v : ℚ) = (u : ℚ) :=
    (eq_div_iff (by exact_mod_cast ne_of_gt hv)).mp r.num_div_den.symm
  have huv : u < v := by
    have hh := mul_lt_mul_of_pos_right hr1 (show (0 : ℚ) < v by exact_mod_cast hv)
    rw [hm, one_mul] at hh
    exact_mod_cast hh
  have hs' := Rat.isSquare_iff.mp hs
  obtain ⟨p, hp, hpE⟩ := positive_square_root u hu hs'.1
  obtain ⟨q, hq, hqE⟩ := positive_square_root v hv (Int.isSquare_natCast_iff.mpr hs'.2)
  have he : ((u ^ 2 - u * v + v ^ 2 : ℤ) : ℚ) =
      (r ^ 2 - r + 1) * (v : ℚ) ^ 2 := by
    push_cast
    linear_combination -((u : ℚ) + r * v - v) * hm
  have hQS : IsSquare (u ^ 2 - u * v + v ^ 2) := Rat.isSquare_intCast_iff.mp
    (he.symm ▸ hQ.mul (IsSquare.sq (v : ℚ)))
  obtain ⟨z, hz⟩ := hQS
  rw [hpE, hqE] at hc huv hz
  have hcp : IsCoprime p q := by
    simp only [sq] at hc
    exact hc.of_mul_left_left.of_mul_right_left
  have hpq : p < q := by nlinarith
  apply quartic_no_strict p q z hp hpq hcp
  nlinarith [hz]

end Erdos633b.PythagoreanDescent

namespace Erdos633b

theorem case_four_rational_nonsquare (a b c : ℚ) (ha : 0 < a) (hb : 0 < b)
    (he : c ^ 2 = a ^ 2 + a * b + b ^ 2) : ¬ IsSquare (b * (a + b)) := by
  intro hs
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  let r := b / (a + b)
  have hr : 0 < r := div_pos hb (add_pos ha hb)
  have hr1 : r < 1 := (div_lt_one (add_pos ha hb)).mpr (by linarith)
  have hrs : IsSquare r := by
    have hid : r = (b * (a + b)) / (a + b) ^ 2 := by dsimp [r]; field_simp
    rw [hid]
    exact hs.div (IsSquare.sq (a + b))
  have hQ : IsSquare (r ^ 2 - r + 1) := by
    refine ⟨c / (a + b), ?_⟩
    dsimp [r]
    field_simp
    nlinarith [he]
  exact PythagoreanDescent.rational_quartic_obstruction r hr hr1 hrs hQ

theorem case_four_integer_nonsquare (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (he : c ^ 2 = a ^ 2 + a * b + b ^ 2) : ¬ IsSquare (b * (a + b)) := by
  intro hs
  apply case_four_rational_nonsquare a b c (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast he)
  have hh := Rat.isSquare_natCast_iff.mpr hs
  simpa only [Nat.cast_mul, Nat.cast_add] using hh

end Erdos633b
