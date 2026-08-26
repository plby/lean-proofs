import ErdosProblems.Erdos633.Arithmetic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The quadratic forms in Euler's cubic descent

The two signs are treated together. These lemmas keep all coprimality and
sign conditions explicit; no rational-point classification is assumed.
-/

namespace Erdos633

def eulerQuadratic (ε u v : ℤ) : ℤ := u ^ 2 + 3 * ε * u * v + 3 * v ^ 2

theorem int_coprime_three_of_not_dvd (u : ℤ) (hu : ¬ (3 : ℤ) ∣ u) :
    IsCoprime u 3 := by
  have hp : Prime (3 : ℤ) := by norm_num
  exact (hp.irreducible.coprime_iff_not_dvd.mpr hu).symm

theorem eulerQuadratic_pos (ε u v : ℤ) (hε : ε ^ 2 = 1) (hv : 0 < v) :
    0 < eulerQuadratic ε u v := by
  have heq : 4 * eulerQuadratic ε u v = (2 * u + 3 * ε * v) ^ 2 + 3 * v ^ 2 := by
    dsimp [eulerQuadratic]
    linear_combination -9 * v ^ 2 * hε
  nlinarith only [heq, sq_nonneg (2 * u + 3 * ε * v), sq_pos_of_pos hv]

theorem eulerQuadratic_coprime (ε u v : ℤ) (huv : IsCoprime u v)
    (hu3 : ¬ (3 : ℤ) ∣ u) :
    IsCoprime u (eulerQuadratic ε u v) ∧ IsCoprime v (eulerQuadratic ε u v) := by
  have h3 := int_coprime_three_of_not_dvd u hu3
  constructor
  · have h := (h3.mul_right (huv.pow_right (n := 2))).add_mul_right_right (u + 3 * ε * v)
    rw [show 3 * v ^ 2 + (u + 3 * ε * v) * u = eulerQuadratic ε u v by
      dsimp [eulerQuadratic]; ring] at h
    exact h
  · have h := (huv.pow_left (m := 2)).add_mul_right_left (3 * ε * u + 3 * v)
    rw [show u ^ 2 + (3 * ε * u + 3 * v) * v = eulerQuadratic ε u v by
      dsimp [eulerQuadratic]; ring] at h
    exact h.symm

theorem euler_parameter_fraction_coprime (ε m n : ℤ) (hε : ε ^ 2 = 1)
    (hmn : IsCoprime m n) (hm3 : ¬ (3 : ℤ) ∣ m) :
    IsCoprime (m ^ 2 - 3 * n ^ 2) (n * (3 * ε * n - 2 * m)) := by
  let A := m ^ 2 - 3 * n ^ 2
  let B := 3 * ε * n - 2 * m
  have hAn : IsCoprime A n := by
    have h := (hmn.pow_left (m := 2)).add_mul_right_left (-3 * n)
    rw [show m ^ 2 + (-3 * n) * n = A by dsimp [A]; ring] at h
    exact h
  have hA3 : IsCoprime A 3 := by
    have h := ((int_coprime_three_of_not_dvd m hm3).pow_left (m := 2)).add_mul_right_left
      (-n ^ 2)
    rw [show m ^ 2 + (-n ^ 2) * 3 = A by dsimp [A]; ring] at h
    exact h
  have hAB : IsCoprime A B := by
    apply isRelPrime_iff_isCoprime.mp
    intro d hdA hdB
    apply (hA3.mul_right (hAn.pow_right (n := 2))).isUnit_of_dvd' hdA
    have heq : 3 * n ^ 2 = -4 * A - (3 * ε * n + 2 * m) * B := by
      dsimp [A, B]
      linear_combination 9 * n ^ 2 * hε
    rw [heq]
    exact dvd_sub (dvd_mul_of_dvd_right hdA _) (dvd_mul_of_dvd_right hdB _)
  exact hAn.mul_right hAB

theorem int_three_dvd_of_sum_sq (k m n : ℤ)
    (h : k ^ 2 + m ^ 2 = 3 * n ^ 2) : (3 : ℤ) ∣ m := by
  have hz := congrArg (fun z : ℤ => (z : ZMod 3)) h
  push_cast at hz
  have hmod : ∀ x y z : ZMod 3, x ^ 2 + y ^ 2 = 3 * z ^ 2 → y = 0 := by decide
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd m 3).mp (hmod _ _ _ hz)

/-- Primitive equal fractions agree up to an integer unit. -/
theorem primitive_fraction_unit (u v A B : ℤ) (hu : u ≠ 0)
    (huv : IsCoprime u v) (hAB : IsCoprime A B) (hcross : u * B = v * A) :
    ∃ d : ℤ, IsUnit d ∧ u = A * d ∧ v = B * d := by
  have hAu : A ∣ u := hAB.dvd_of_dvd_mul_right ⟨v, by rw [hcross]; ring⟩
  obtain ⟨d, hud⟩ := hAu
  have hA : A ≠ 0 := by
    intro h
    simp only [h, zero_mul] at hud
    exact hu hud
  have hvd : v = B * d := by
    apply mul_right_cancel₀ hA
    calc
      v * A = u * B := hcross.symm
      _ = (B * d) * A := by rw [hud]; ring
  refine ⟨d, huv.isUnit_of_dvd' ?_ ?_, hud, hvd⟩
  · exact ⟨A, by rw [hud]; ring⟩
  · exact ⟨B, by rw [hvd]; ring⟩

/-- The square condition selects the positive unit in the first parametrization. -/
theorem euler_parameter_fraction_eq (ε u v m n : ℤ) (hε : ε ^ 2 = 1)
    (hu : 0 < u) (huv : IsCoprime u v) (husq : IsSquare u)
    (hmn : IsCoprime m n) (hm3 : ¬ (3 : ℤ) ∣ m)
    (hcross : u * (n * (3 * ε * n - 2 * m)) = v * (m ^ 2 - 3 * n ^ 2)) :
    u = m ^ 2 - 3 * n ^ 2 ∧ v = n * (3 * ε * n - 2 * m) := by
  obtain ⟨d, hd, hu', hv'⟩ := primitive_fraction_unit u v _ _ (ne_of_gt hu) huv
    (euler_parameter_fraction_coprime ε m n hε hmn hm3) hcross
  rcases Int.isUnit_iff.mp hd with hd | hd
  · simpa [hd] using And.intro hu' hv'
  · obtain ⟨k, hk⟩ := husq
    apply False.elim
    apply hm3
    apply int_three_dvd_of_sum_sq k m n
    rw [hd] at hu'
    nlinarith only [hu', hk]

theorem nat_coprime_square_factor (u v : ℕ) (huv : u.Coprime v)
    (hsq : IsSquare (u * v)) : IsSquare u := by
  obtain ⟨w, hw⟩ := hsq
  have hunit : IsUnit (gcd u v) := by
    rw [gcd_eq_nat_gcd, huv.gcd_eq_one]
    exact isUnit_one
  obtain ⟨x, hx⟩ := exists_eq_pow_of_mul_eq_pow hunit
    (show u * v = w ^ 2 by simpa only [pow_two] using hw)
  exact ⟨x, by simpa only [pow_two] using hx⟩

theorem int_coprime_square_factors (u v : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : IsCoprime u v) (hsq : IsSquare (u * v)) : IsSquare u ∧ IsSquare v := by
  lift u to ℕ using hu
  lift v to ℕ using hv
  have hsqN : IsSquare (u * v) := Int.isSquare_natCast_iff.mp (by
    simpa only [Nat.cast_mul] using hsq)
  exact ⟨Int.isSquare_natCast_iff.mpr (nat_coprime_square_factor u v huv.natCoprime hsqN),
    Int.isSquare_natCast_iff.mpr (nat_coprime_square_factor v u huv.symm.natCoprime
      (by simpa only [mul_comm] using hsqN))⟩

theorem int_isSquare_of_sq_mul (n z : ℤ) (hn : n ≠ 0)
    (hsq : IsSquare (n ^ 2 * z)) : IsSquare z := by
  apply Rat.isSquare_intCast_iff.mp
  apply (isSquare_sq_mul_iff (n : ℚ) (z : ℚ) (by exact_mod_cast hn)).mp
  have h := Rat.isSquare_intCast_iff.mpr hsq
  simpa only [Int.cast_mul, Int.cast_pow] using h

end Erdos633
