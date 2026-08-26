import ErdosProblems.Erdos633b.EulerRational

/-! The same terminating conic descent with `3 * v` square. -/

namespace Erdos633b.EulerDescent

structure TwistedSolution (u v : ℤ) : Prop extends CoreSolution u v where
  v_square : IsSquare (3 * v)

theorem Q_coprime_three (p q : ℤ) (h3 : IsCoprime p 3) : IsCoprime (Q p q) 3 := by
  apply (coprime_three_iff _).mpr
  intro hd
  have hd' : (3 : ℤ) ∣ p ^ 2 := by
    have he : p ^ 2 = Q p q + 3 * (p * q - q ^ 2) := by dsimp [Q]; ring
    rw [he]
    exact dvd_add hd (dvd_mul_right _ _)
  exact (coprime_three_iff _).mp h3 (Int.prime_three.dvd_of_dvd_pow hd')

theorem twisted_square_factors (p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (hc : IsCoprime p q) (h3 : IsCoprime p 3)
    (hs : IsSquare (3 * p * q * Q p q)) :
    IsSquare p ∧ IsSquare (3 * q) ∧ IsSquare (Q p q) := by
  have hpQ := coprime_Q_left p q hc h3
  have hqQ := coprime_Q_right p q hc
  have hQ3 := Q_coprime_three p q h3
  refine ⟨square_factor hp ((h3.mul_right hc).mul_right hpQ) ?_,
    square_factor (by omega : 0 < 3 * q)
      ((h3.symm.mul_right hQ3.symm).mul_left (hc.symm.mul_right hqQ)) ?_,
    square_factor (Q_pos p q hq) ((hQ3.mul_right hpQ.symm).mul_right hqQ.symm) ?_⟩
  all_goals convert hs using 1; ring

theorem three_not_square : ¬ IsSquare (3 : ℤ) := by
  rintro ⟨k, hk⟩
  have hf : ∀ k : ZMod 4, k * k ≠ 3 := by decide
  have he := congrArg (Int.castRingHom (ZMod 4)) hk
  exact hf k (by simpa using he.symm)

theorem twisted_step (u v : ℤ) (h : TwistedSolution u v) :
    ∃ p q : ℤ, TwistedSolution p q ∧ q < v := by
  obtain ⟨m, n, hn, hmn, hm3, hnv, hu, hv⟩ := first_parameter u v h.toCoreSolution
  obtain ⟨p, q, hq, hpq, hp3, hqn, hid, hpqn, _⟩ :=
    second_parameter u v m n h.toCoreSolution hn hmn hm3 hu hv
  have hQ := Q_pos p q hq
  have hpqpos : 0 < p * q := by
    have hh : 0 < v * (p * q) := by
      rw [← mul_assoc, hid]
      exact mul_pos (sq_pos_of_pos hn) hQ
    exact pos_of_mul_pos_right hh (le_of_lt h.v_pos)
  have hp : 0 < p := pos_of_mul_pos_left hpqpos (le_of_lt hq)
  have hnp : p * q ≤ n := Int.le_of_dvd hn hpqn
  have hnv' : n ≤ v := Int.le_of_dvd h.v_pos hnv
  have hqn' : q ≤ n := Int.le_of_dvd hn hqn
  have hqv : q ≤ v := hqn'.trans hnv'
  have hs : IsSquare (3 * p * q * Q p q) := by
    have he : (3 * (p : ℚ) * q * Q p q) * (n : ℚ) ^ 2 =
        (3 * (v : ℚ)) * ((p : ℚ) * q) ^ 2 := by
      have hh : (v : ℚ) * p * q = (n : ℚ) ^ 2 * Q p q := by exact_mod_cast hid
      linear_combination -(3 * (p : ℚ) * q) * hh
    have hvS : IsSquare (3 * (v : ℚ)) := by
      simpa only [Int.cast_mul, Int.cast_ofNat] using Rat.isSquare_intCast_iff.mpr h.v_square
    have hh : IsSquare (3 * (p : ℚ) * q * Q p q) :=
      (isSquare_mul_sq_iff _ (n : ℚ) (by exact_mod_cast ne_of_gt hn)).mp
        (he.symm ▸ hvS.mul (IsSquare.sq ((p : ℚ) * q)))
    apply Rat.isSquare_intCast_iff.mp
    simpa only [Int.cast_mul, Int.cast_ofNat] using hh
  have hs' := twisted_square_factors p q hp hq hpq hp3 hs
  have hlt : q < v := by
    by_contra hh
    have heq : q = v := by omega
    have hne : n = v := by omega
    have hp1 : p = 1 := by nlinarith [hnp]
    have hv1 : v = 1 := by
      rw [hp1, hne, heq] at hid
      dsimp [Q] at hid
      have hc : 1 = 1 - 3 * v + 3 * v ^ 2 := by
        apply mul_left_cancel₀ (ne_of_gt (sq_pos_of_pos h.v_pos))
        linear_combination hid
      nlinarith [h.v_pos]
    exact three_not_square (by simpa [hv1] using h.v_square)
  exact ⟨p, q, ⟨⟨hp, hq, hpq, hp3, hs'.1, hs'.2.2⟩, hs'.2.1⟩, hlt⟩

theorem no_twisted_solution (u v : ℤ) (h : TwistedSolution u v) : False := by
  have aux : ∀ N : ℕ, ∀ u v : ℤ, v.toNat = N → TwistedSolution u v → False := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro u v hv h
      obtain ⟨p, q, hpq, hqv⟩ := twisted_step u v h
      have hlt : q.toNat < N := by
        rw [← hv]
        exact (Int.toNat_lt_toNat h.v_pos).mpr hqv
      exact ih q.toNat hlt p q rfl hpq
  exact aux v.toNat u v rfl h

theorem rational_twisted_pair (r : ℚ) (hr : 0 < r) (hs : IsSquare (3 * r))
    (hQ : IsSquare (r ^ 2 - 3 * r + 3)) : False := by
  let u := r.num
  let v : ℤ := r.den
  have hu : 0 < u := Rat.num_pos.mpr hr
  have hv : 0 < v := by dsimp [v]; exact_mod_cast r.pos
  have hc : IsCoprime u v := r.isCoprime_num_den
  have hm : r * (v : ℚ) = (u : ℚ) := by
    exact (eq_div_iff (by exact_mod_cast ne_of_gt hv)).mp r.num_div_den.symm
  have he : (Q u v : ℚ) = (r ^ 2 - 3 * r + 3) * (v : ℚ) ^ 2 := by
    dsimp [Q]
    push_cast
    linear_combination -((u : ℚ) + r * v - 3 * v) * hm
  have hQS : IsSquare (Q u v) := Rat.isSquare_intCast_iff.mp
    (he.symm ▸ hQ.mul (IsSquare.sq (v : ℚ)))
  have h3 := coprime_three_of_Q_square u v hc hQS
  have he' : ((u * (3 * v) : ℤ) : ℚ) = (3 * r) * (v : ℚ) ^ 2 := by
    push_cast
    linear_combination -3 * (v : ℚ) * hm
  have hsuv : IsSquare (u * (3 * v)) := Rat.isSquare_intCast_iff.mp
    (he'.symm ▸ hs.mul (IsSquare.sq (v : ℚ)))
  have huS : IsSquare u := square_factor hu (h3.mul_right hc) hsuv
  have hvS : IsSquare (3 * v) := square_factor (by omega) (h3.mul_right hc).symm
    (by simpa only [mul_comm] using hsuv)
  exact no_twisted_solution u v ⟨⟨hu, hv, hc, h3, huS, hQS⟩, hvS⟩

end Erdos633b.EulerDescent

namespace Erdos633b

theorem case_five_rational_nonsquare (a b c : ℚ) (ha : 0 < a) (hb : 0 < b)
    (he : c ^ 2 = a ^ 2 + a * b + b ^ 2) : ¬ IsSquare (3 * (a + 2 * b) * (a + b)) := by
  intro hs
  let r := (a + 2 * b) / (a + b)
  have hr : 0 < r := div_pos (by linarith) (add_pos ha hb)
  have hrs : IsSquare (3 * r) := by
    have hid : 3 * r = (3 * (a + 2 * b) * (a + b)) / (a + b) ^ 2 := by
      dsimp [r]; field_simp
    rw [hid]
    exact hs.div (IsSquare.sq (a + b))
  have hQ : IsSquare (r ^ 2 - 3 * r + 3) := by
    refine ⟨c / (a + b), ?_⟩
    dsimp [r]
    field_simp
    nlinarith [he]
  exact EulerDescent.rational_twisted_pair r hr hrs hQ

theorem case_five_integer_nonsquare (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (he : c ^ 2 = a ^ 2 + a * b + b ^ 2) : ¬ IsSquare (3 * (a + 2 * b) * (a + b)) := by
  intro hs
  apply case_five_rational_nonsquare a b c (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast he)
  have hh := Rat.isSquare_natCast_iff.mpr hs
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hh

end Erdos633b
