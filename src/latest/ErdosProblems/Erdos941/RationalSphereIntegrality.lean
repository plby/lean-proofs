import ErdosProblems.Erdos941.SpherePairGroup
import ErdosProblems.Erdos941.Shadowing

/-!
# Rational norm-one vectors are integral if they are integral at every odd prime

The missing prime is handled by descent modulo four, rather than a local
orthogonal-group classification at two.
-/

namespace Erdos941

private theorem three_squares_zero_mod_four (x y z : ZMod 4)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 0) : 2 * x = 0 ∧ 2 * y = 0 ∧ 2 * z = 0 := by
  revert x y z
  decide

theorem even_coordinates_of_four_dvd_norm {a b c : ℤ} (h : (4 : ℤ) ∣ a ^ 2 + b ^ 2 + c ^ 2) :
    (2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b ∧ (2 : ℤ) ∣ c := by
  have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 + b ^ 2 + c ^ 2) 4).mpr h
  push_cast at hh
  obtain ⟨ha, hb, hc⟩ := three_squares_zero_mod_four (a : ZMod 4) b c hh
  have hdiv (x : ℤ) (hx : (2 : ZMod 4) * x = 0) : (2 : ℤ) ∣ x := by
    have hz : ((2 * x : ℤ) : ZMod 4) = 0 := by push_cast; exact hx
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * x) 4).mp hz
    omega
  exact ⟨hdiv a ha, hdiv b hb, hdiv c hc⟩

theorem two_pow_dvd_coordinates_of_norm (k : ℕ) {a b c : ℤ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 = ((2 : ℤ) ^ k) ^ 2) :
    (2 : ℤ) ^ k ∣ a ∧ (2 : ℤ) ^ k ∣ b ∧ (2 : ℤ) ^ k ∣ c := by
  induction k generalizing a b c with
  | zero => simp
  | succ k ih =>
    have h4 : (4 : ℤ) ∣ a ^ 2 + b ^ 2 + c ^ 2 := by
      refine ⟨((2 : ℤ) ^ k) ^ 2, ?_⟩
      rw [h, pow_succ]
      ring
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩ := even_coordinates_of_four_dvd_norm h4
    have hsmall : a ^ 2 + b ^ 2 + c ^ 2 = ((2 : ℤ) ^ k) ^ 2 := by
      rw [pow_succ (2 : ℤ) k] at h
      nlinarith
    obtain ⟨ha, hb, hc⟩ := ih hsmall
    simpa only [pow_succ, mul_comm ((2 : ℤ) ^ k) 2] using
      And.intro (mul_dvd_mul_left 2 ha) (And.intro (mul_dvd_mul_left 2 hb) (mul_dvd_mul_left 2 hc))

theorem exists_two_pow_mul_int_of_odd_padic_integral (q : ℚ)
    (h : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∃ z : PadicInt p, (z : Padic p) = (q : Padic p)) :
    ∃ k : ℕ, ∃ a : ℤ, (2 : ℚ) ^ k * q = a := by
  have hden : q.den = 2 ^ q.den.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (by
      intro p hp hpdvd
      by_contra hp2
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨z, hz⟩ := h p hp2
      have hnorm : ‖(q : Padic p)‖ ≤ 1 := by rw [← hz]; exact z.2
      have hunit := PadicInt.isUnit_den (p := p) q hnorm
      have heq := PadicInt.isUnit_iff.mp hunit
      have hlt : ‖(q.den : PadicInt p)‖ < 1 := PadicInt.norm_natCast_lt_one_iff.mpr hpdvd
      rw [heq] at hlt
      exact (lt_irrefl (1 : ℝ)) hlt)
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  have h := q.den_mul_eq_num
  rw [hden, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

theorem extend_two_pow_integrality {q : ℚ} {k K : ℕ} (hk : k ≤ K)
    (h : ∃ a : ℤ, (2 : ℚ) ^ k * q = a) :
    ∃ a : ℤ, (2 : ℚ) ^ K * q = a := by
  obtain ⟨a, ha⟩ := h
  refine ⟨(2 : ℤ) ^ (K - k) * a, ?_⟩
  rw [show K = (K - k) + k by omega, pow_add, mul_assoc, ha]
  push_cast
  simp only [Nat.add_sub_cancel]

theorem rational_norm_one_integral_of_odd_local (v : ℚ × ℚ × ℚ)
    (hv : normThree v = 1)
    (h1 : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∃ z : PadicInt p, (z : Padic p) = (v.1 : Padic p))
    (h2 : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∃ z : PadicInt p, (z : Padic p) = (v.2.1 : Padic p))
    (h3 : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∃ z : PadicInt p, (z : Padic p) = (v.2.2 : Padic p)) :
    ∃ a b c : ℤ, (a : ℚ) = v.1 ∧ (b : ℚ) = v.2.1 ∧ (c : ℚ) = v.2.2 := by
  obtain ⟨k1, hk1⟩ := exists_two_pow_mul_int_of_odd_padic_integral v.1 h1
  obtain ⟨k2, hk2⟩ := exists_two_pow_mul_int_of_odd_padic_integral v.2.1 h2
  obtain ⟨k3, hk3⟩ := exists_two_pow_mul_int_of_odd_padic_integral v.2.2 h3
  let K := k1 + k2 + k3
  obtain ⟨a, ha⟩ := extend_two_pow_integrality (K := K) (by dsimp [K]; omega) hk1
  obtain ⟨b, hb⟩ := extend_two_pow_integrality (K := K) (by dsimp [K]; omega) hk2
  obtain ⟨c, hc⟩ := extend_two_pow_integrality (K := K) (by dsimp [K]; omega) hk3
  have hnorm : a ^ 2 + b ^ 2 + c ^ 2 = ((2 : ℤ) ^ K) ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [← ha, ← hb, ← hc]
    change _ = ((2 : ℚ) ^ K) ^ 2
    dsimp [normThree] at hv
    linear_combination ((2 : ℚ) ^ K) ^ 2 * hv
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩⟩ := two_pow_dvd_coordinates_of_norm K hnorm
  have hcancel {x : ℚ} {z Z : ℤ} (hx : (2 : ℚ) ^ K * x = z)
      (hz : z = (2 : ℤ) ^ K * Z) : (Z : ℚ) = x := by
    apply mul_left_cancel₀ (pow_ne_zero K (by norm_num : (2 : ℚ) ≠ 0))
    rw [hx, hz]
    push_cast
    rfl
  exact ⟨A, B, C, hcancel ha hA, hcancel hb hB, hcancel hc hC⟩

end Erdos941
