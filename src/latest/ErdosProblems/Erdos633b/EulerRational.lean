import ErdosProblems.Erdos633b.EulerDescent

/-! Clearing denominators in the primitive Euler descent. -/

namespace Erdos633b.EulerDescent

theorem coprime_three_of_Q_square (u v : ℤ) (hc : IsCoprime u v)
    (hs : IsSquare (Q u v)) : IsCoprime u 3 := by
  apply (coprime_three_iff u).mpr
  rintro ⟨k, rfl⟩
  obtain ⟨w, hw⟩ := hs
  have he : w ^ 2 = 9 * k ^ 2 - 9 * k * v + 3 * v ^ 2 := by
    dsimp [Q] at hw
    nlinarith [hw]
  have h3w : (3 : ℤ) ∣ w := Int.prime_three.dvd_of_dvd_pow (n := 2) (by
    rw [he]
    exact ⟨3 * k ^ 2 - 3 * k * v + v ^ 2, by ring⟩)
  obtain ⟨l, hl⟩ := h3w
  have hv : v ^ 2 = 3 * (l ^ 2 - k ^ 2 + k * v) := by
    rw [hl] at he
    nlinarith [he]
  have h3v : (3 : ℤ) ∣ v := Int.prime_three.dvd_of_dvd_pow (n := 2) ⟨_, hv⟩
  have hunit : IsUnit (3 : ℤ) := hc.isUnit_of_dvd' (dvd_mul_right 3 k) h3v
  norm_num [Int.isUnit_iff] at hunit

/-- The rational form of the Euler square-pair lemma. -/
theorem rational_square_pair (r : ℚ) (hr : 0 < r) (hs : IsSquare r)
    (hQ : IsSquare (r ^ 2 - 3 * r + 3)) : r = 1 := by
  let u := r.num
  let v : ℤ := r.den
  have hu : 0 < u := Rat.num_pos.mpr hr
  have hv : 0 < v := by dsimp [v]; exact_mod_cast r.pos
  have hc : IsCoprime u v := r.isCoprime_num_den
  have hsq := Rat.isSquare_iff.mp hs
  have huS : IsSquare u := hsq.1
  have hvS : IsSquare v := Int.isSquare_natCast_iff.mpr hsq.2
  have hm : r * (v : ℚ) = (u : ℚ) := by
    exact (eq_div_iff (by exact_mod_cast ne_of_gt hv)).mp r.num_div_den.symm
  have he : (Q u v : ℚ) = (r ^ 2 - 3 * r + 3) * (v : ℚ) ^ 2 := by
    dsimp [Q]
    push_cast
    linear_combination -((u : ℚ) + r * v - 3 * v) * hm
  have hQS : IsSquare (Q u v) := Rat.isSquare_intCast_iff.mp
    (he.symm ▸ hQ.mul (IsSquare.sq (v : ℚ)))
  have h3 := coprime_three_of_Q_square u v hc hQS
  obtain ⟨hu1, hv1⟩ := solution_eq_one u v ⟨⟨hu, hv, hc, h3, huS, hQS⟩, hvS⟩
  simpa [hu1, hv1] using hm

end Erdos633b.EulerDescent

namespace Erdos633b

/-- The case-(8) count's square class is never a square for positive Eisenstein side data. -/
theorem case_eight_rational_nonsquare (a b c : ℚ) (ha : 0 < a) (hb : 0 < b)
    (he : c ^ 2 = a ^ 2 + a * b + b ^ 2) : ¬ IsSquare ((a + b) * (2 * a + b)) := by
  intro hs
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  let r := (2 * a + b) / (a + b)
  have hr : 1 < r := (lt_div_iff₀ (add_pos ha hb)).mpr (by linarith)
  have hrs : IsSquare r := by
    have hid : r = ((a + b) * (2 * a + b)) / (a + b) ^ 2 := by
      dsimp [r]; field_simp
    rw [hid]
    exact hs.div (IsSquare.sq (a + b))
  have hQ : IsSquare (r ^ 2 - 3 * r + 3) := by
    refine ⟨c / (a + b), ?_⟩
    dsimp [r]
    field_simp
    nlinarith [he]
  have := EulerDescent.rational_square_pair r (by linarith) hrs hQ
  linarith

theorem case_eight_integer_nonsquare (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (he : c ^ 2 = a ^ 2 + a * b + b ^ 2) : ¬ IsSquare ((a + b) * (2 * a + b)) := by
  intro hs
  apply case_eight_rational_nonsquare a b c (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast he)
  have hh := Rat.isSquare_natCast_iff.mpr hs
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hh

end Erdos633b
