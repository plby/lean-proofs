import ErdosProblems.Erdos633b.Specification
import ErdosProblems.Erdos633b.ReptilingAlgebra
import Mathlib.NumberTheory.Niven

/-! Exact rational-angle restrictions for the right-triangle exception.
Niven's theorem is imported with its Mathlib proof, not postulated. -/

namespace Erdos633b

theorem angle_eq_pi_six_of_rational_cos_sq {a : ℝ} (ha : 0 < a)
    (ha4 : a < Real.pi / 4) (hr : IsRational (a / Real.pi))
    (hc : IsRational (Real.cos a ^ 2)) : a = Real.pi / 6 := by
  obtain ⟨r, hr⟩ := hr
  obtain ⟨q, hq⟩ := hc
  have hangle : ∃ r : ℚ, 2 * a = r * Real.pi := by
    refine ⟨2 * r, ?_⟩
    push_cast
    have he : a = (r : ℝ) * Real.pi := (div_eq_iff Real.pi_ne_zero).mp hr.symm
    rw [he]
    ring
  have hcos : ∃ q : ℚ, Real.cos (2 * a) = q := by
    refine ⟨2 * q - 1, ?_⟩
    push_cast
    rw [Real.cos_two_mul, hq]
  have hb : 2 * a ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith [Real.pi_pos]⟩
  have he := niven_angle_eq hangle hcos hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with he | he | he | he | he <;> linarith [Real.pi_pos]

theorem no_exceptional_rational_right {a : ℝ} (ha : 0 < a)
    (ha4 : a < Real.pi / 4) (hr : IsRational (a / Real.pi))
    (n : ℕ) (hn : 0 < n) (p d e f : ℤ) (hp : 0 < p) (he : 0 ≤ e)
    (hfirst : Real.sqrt n * Real.cos a = f)
    (hsecond : Real.sqrt n * Real.sin a =
      p * Real.sin a + d * Real.cos a + e) : False := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hnR.le
  have hcos : IsRational (Real.cos a ^ 2) := by
    refine ⟨(f : ℚ) ^ 2 / n, ?_⟩
    push_cast
    apply (div_eq_iff hnR.ne').mpr
    have hpow := congrArg (fun x : ℝ => x ^ 2) hfirst
    linear_combination -hpow + Real.cos a ^ 2 * hs
  have ha6 := angle_eq_pi_six_of_rational_cos_sq ha ha4 hr hcos
  rw [ha6, Real.cos_pi_div_six] at hfirst
  rw [ha6, Real.sin_pi_div_six, Real.cos_pi_div_six] at hsecond
  have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hirr : Irrational (Real.sqrt 3) := by
    simpa only [Nat.cast_ofNat] using
      (irrational_sqrt_natCast_iff.mpr Nat.prime_three.not_isSquare)
  have hc : ((p + 2 * e : ℤ) : ℝ) * Real.sqrt 3 = (2 * f - 3 * d : ℤ) := by
    push_cast
    linear_combination 2 * hfirst - 2 * Real.sqrt 3 * hsecond - (d : ℝ) * h3
  have hz := (int_coefficients_of_irrational hirr _ _ hc).1
  omega

end Erdos633b
