import ErdosProblems.Erdos633b.EulerTools

/-! The two conic parametrizations in the integer Euler descent. -/

namespace Erdos633b.EulerDescent

structure CoreSolution (u v : ℤ) : Prop where
  u_pos : 0 < u
  v_pos : 0 < v
  coprime : IsCoprime u v
  prime_three : IsCoprime u 3
  u_square : IsSquare u
  Q_square : IsSquare (Q u v)

structure Solution (u v : ℤ) : Prop extends CoreSolution u v where
  v_square : IsSquare v

theorem first_parameter (u v : ℤ) (h : CoreSolution u v) :
    ∃ m n : ℤ, 0 < n ∧ IsCoprime m n ∧ IsCoprime m 3 ∧ n ∣ v ∧
      u = m ^ 2 - 3 * n ^ 2 ∧ v = -n * (2 * m + 3 * n) := by
  obtain ⟨w₀, hw₀⟩ := h.Q_square
  have he₀ : w₀ ^ 2 = Q u v := by simpa [sq] using hw₀.symm
  have hm₀ : (w₀ : ZMod 3) ^ 2 = (u : ZMod 3) ^ 2 := by
    have hz := congrArg (Int.castRingHom (ZMod 3)) he₀
    simp [Q] at hz
    simpa only [show (3 : ZMod 3) = 0 by decide, zero_mul, sub_zero, add_zero] using hz
  obtain ⟨w, hw, _, hw3⟩ := sign_mod_three u w₀
    ((coprime_three_iff u).mp h.prime_three) hm₀
  have he : w ^ 2 = Q u v := hw.trans he₀
  obtain ⟨m, n, hn, hmn, hmd, hnd, hcross⟩ :=
    reduced_ratio (w - u) v (ne_of_gt h.v_pos)
  have hm3 : IsCoprime m 3 := (coprime_three_iff m).mpr fun hd => hw3 (hd.trans hmd)
  have hcross' : u * (n * (2 * m + 3 * n)) = (3 * n ^ 2 - m ^ 2) * v := by
    apply mul_left_cancel₀ (ne_of_gt h.v_pos)
    dsimp [Q] at he
    linear_combination n ^ 2 * he - (w * n + u * n + m * v) * hcross
  have hsign := reduced_cross_sign u v (3 * n ^ 2 - m ^ 2)
    (n * (2 * m + 3 * n)) h.coprime (conic_fraction_coprime m n hmn hm3) hcross'
  rcases hsign with ⟨hu, _⟩ | ⟨hu, hv⟩
  · obtain ⟨k, hk⟩ := h.u_square
    have hf : ∀ k m : ZMod 3, m ≠ 0 → k ^ 2 ≠ -m ^ 2 := by decide
    have hm0 : (m : ZMod 3) ≠ 0 := fun hh =>
      (coprime_three_iff m).mp hm3 ((ZMod.intCast_zmod_eq_zero_iff_dvd m 3).mp hh)
    have hz := congrArg (Int.castRingHom (ZMod 3)) (hk.symm.trans hu)
    exact False.elim (hf k m hm0 (by
      simpa [sq, show (3 : ZMod 3) = 0 by decide] using hz))
  · refine ⟨m, n, hn, hmn, hm3, hnd, ?_, ?_⟩ <;> linarith

/-- The second reduced fraction, with the equation and both divisibility certificates. -/
theorem second_parameter (u v m n : ℤ) (h : CoreSolution u v)
    (hn : 0 < n) (hmn : IsCoprime m n) (hm3 : IsCoprime m 3)
    (hu : u = m ^ 2 - 3 * n ^ 2) (hv : v = -n * (2 * m + 3 * n)) :
    ∃ p q : ℤ, 0 < q ∧ IsCoprime p q ∧ IsCoprime p 3 ∧ q ∣ n ∧
      v * p * q = n ^ 2 * Q p q ∧ p * q ∣ n ∧
      (p = 1 → q = 1 → u = 1 ∧ v = 1) := by
  obtain ⟨k₀, hk₀⟩ := h.u_square
  have hkm₀ : k₀ ^ 2 = m ^ 2 - 3 * n ^ 2 := by simpa [sq] using hk₀.symm.trans hu
  have hz₀ := congrArg (Int.castRingHom (ZMod 3)) hkm₀
  obtain ⟨k, hk, _, hk3⟩ := sign_mod_three m k₀ ((coprime_three_iff m).mp hm3)
    (by simpa [show (3 : ZMod 3) = 0 by decide] using hz₀)
  have hkm : k ^ 2 = m ^ 2 - 3 * n ^ 2 := hk.trans hkm₀
  obtain ⟨p, q, hq, hpq, hpd, hqd, hcross⟩ := reduced_ratio (k - m) n (ne_of_gt hn)
  have hp3 : IsCoprime p 3 := (coprime_three_iff p).mpr fun hd => hk3 (hd.trans hpd)
  have hid : v * p * q = n ^ 2 * Q p q := by
    have he : 2 * m * p * q + (3 * q ^ 2 + p ^ 2) * n = 0 := by
      apply mul_left_cancel₀ (ne_of_gt hn)
      linear_combination q ^ 2 * hkm - (k * q + m * q + p * n) * hcross
    dsimp [Q]
    linear_combination p * q * hv - n * he
  have hcop : IsCoprime (p * q) (Q p q) :=
    (coprime_Q_left p q hpq hp3).mul_left (coprime_Q_right p q hpq)
  have hdiv : p * q ∣ n := by
    have hstep : p * q ∣ (- (2 * m + 3 * n)) * p * q := by
      simp [mul_assoc]
    have he : (-(2 * m + 3 * n)) * p * q = n * Q p q := by
      apply mul_left_cancel₀ (ne_of_gt hn)
      linear_combination hid - p * q * hv
    rw [he] at hstep
    exact hcop.dvd_of_dvd_mul_right hstep
  refine ⟨p, q, hq, hpq, hp3, hqd, hid, hdiv, ?_⟩
  intro hp hq'
  subst p; subst q
  have hkn : k = m + n := by linarith [hcross]
  rw [hkn] at hkm
  have hmn' : m = -2 * n := by
    have he : n * (m + 2 * n) = 0 := by nlinarith [hkm]
    have := (mul_eq_zero.mp he).resolve_left (ne_of_gt hn)
    linarith
  have hnunit : IsUnit n := hmn.isUnit_of_dvd' ⟨-2, by linarith [hmn']⟩ (dvd_refl n)
  have hn1 : n = 1 := by rcases Int.isUnit_iff.mp hnunit with hh | hh <;> omega
  constructor <;> nlinarith [hu, hv]

end Erdos633b.EulerDescent
