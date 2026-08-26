/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Real affine lines on the sextic surface, using its three highest coefficients.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.PowerValues

namespace Erdos477.Geometry

open Polynomial

lemma sixth_affine_coeff (a b : ℝ) (k : ℕ) :
    ((C a * X + C b) ^ 6).coeff k = b ^ (6 - k) * (Nat.choose 6 k : ℝ) * a ^ k := by
  have h : (C a * X + C b) ^ 6 = ((X + C b) ^ 6).comp (C a * X) := by simp
  rw [h, comp_C_mul_X_coeff, coeff_X_add_C_pow]

lemma sixth_two_coefficients (a b d e : ℝ) (hd : d ≠ 0)
    (h6 : a ^ 6 = d ^ 6) (h5 : a ^ 5 * b = d ^ 5 * e) : b ^ 6 = e ^ 6 := by
  have h30 : a ^ 30 = d ^ 30 := by
    simpa only [← pow_mul] using congrArg (fun x : ℝ => x ^ (5 : ℕ)) h6
  have hpow : a ^ 30 * b ^ 6 = d ^ 30 * e ^ 6 := by
    simpa only [mul_pow, ← pow_mul] using congrArg (fun x : ℝ => x ^ (6 : ℕ)) h5
  rw [h30] at hpow
  exact mul_left_cancel₀ (pow_ne_zero _ hd) hpow

/-- The top three coefficients force either a constant parametrization,
a constant positive-sign coordinate, or the zero-level surface. -/
theorem real_sextic_line_coefficients (a b : Fin 3 → ℝ) (c : ℝ)
    (h6 : a 0 ^ 6 + a 1 ^ 6 = a 2 ^ 6)
    (h5 : a 0 ^ 5 * b 0 + a 1 ^ 5 * b 1 = a 2 ^ 5 * b 2)
    (h4 : a 0 ^ 4 * b 0 ^ 2 + a 1 ^ 4 * b 1 ^ 2 = a 2 ^ 4 * b 2 ^ 2)
    (h0 : b 0 ^ 6 + b 1 ^ 6 - b 2 ^ 6 = c) :
    a = 0 ∨ c = b 0 ^ 6 ∨ c = b 1 ^ 6 ∨ c = 0 := by
  by_cases ha2 : a 2 = 0
  · have hzeros : a 0 = 0 ∧ a 1 = 0 := by
      rw [ha2, zero_pow (by decide)] at h6
      have hp0 : 0 ≤ a 0 ^ 6 := by positivity
      have hp1 : 0 ≤ a 1 ^ 6 := by positivity
      have hz0 : a 0 ^ 6 = 0 := by linarith
      have hz1 : a 1 ^ 6 = 0 := by linarith
      exact ⟨(pow_eq_zero_iff (by decide)).mp hz0, (pow_eq_zero_iff (by decide)).mp hz1⟩
    left
    ext k
    fin_cases k
    · exact hzeros.1
    · exact hzeros.2
    · exact ha2
  by_cases ha0 : a 0 = 0
  · have hb := sixth_two_coefficients (a 1) (b 1) (a 2) (b 2) ha2
      (by simpa [ha0] using h6) (by simpa [ha0] using h5)
    exact Or.inr (Or.inl (by linarith))
  by_cases ha1 : a 1 = 0
  · have hb := sixth_two_coefficients (a 0) (b 0) (a 2) (b 2) ha2
      (by simpa [ha1] using h6) (by simpa [ha1] using h5)
    exact Or.inr (Or.inr (Or.inl (by linarith)))
  have hcross : a 0 ^ 4 * a 1 ^ 4 * (a 0 * b 1 - a 1 * b 0) ^ 2 = 0 := by
    calc
      _ = (a 0 ^ 6 + a 1 ^ 6) * (a 0 ^ 4 * b 0 ^ 2 + a 1 ^ 4 * b 1 ^ 2) -
          (a 0 ^ 5 * b 0 + a 1 ^ 5 * b 1) ^ 2 := by ring
      _ = 0 := by rw [h6, h5, h4]; ring
  have h01 : a 0 * b 1 = a 1 * b 0 := by
    have hs := (mul_eq_zero.mp hcross).resolve_left
      (mul_ne_zero (pow_ne_zero _ ha0) (pow_ne_zero _ ha1))
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by decide)).mp hs)
  have h02 : a 0 * b 2 = a 2 * b 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 5 ha2)
    calc
      _ = (a 0 ^ 5 * b 0 + a 1 ^ 5 * b 1) * a 0 := by rw [h5]; ring
      _ = (a 0 ^ 6 + a 1 ^ 6) * b 0 := by
        nlinarith only [congrArg (fun x : ℝ => a 1 ^ 5 * x) h01]
      _ = _ := by rw [h6]; ring
  have hp01 := congrArg (fun x : ℝ => x ^ (6 : ℕ)) h01
  have hp02 := congrArg (fun x : ℝ => x ^ (6 : ℕ)) h02
  simp only [mul_pow] at hp01 hp02
  have hczero : a 0 ^ 6 * c = 0 := by
    calc
      _ = a 0 ^ 6 * (b 0 ^ 6 + b 1 ^ 6 - b 2 ^ 6) := by rw [h0]
      _ = (a 0 ^ 6 + a 1 ^ 6 - a 2 ^ 6) * b 0 ^ 6 := by
        nlinarith only [hp01, hp02]
      _ = 0 := by rw [h6, sub_self, zero_mul]
  exact Or.inr (Or.inr (Or.inr ((mul_eq_zero.mp hczero).resolve_left (pow_ne_zero _ ha0))))

/-- Every real affine line on a nonzero sextic level has a constant
positive-sign coordinate whose sixth power is that level. -/
theorem real_sextic_line (a b : Fin 3 → ℝ) (c : ℝ)
    (h : ∀ t : ℝ, (a 0 * t + b 0) ^ 6 + (a 1 * t + b 1) ^ 6 -
      (a 2 * t + b 2) ^ 6 = c) :
    a = 0 ∨ c = b 0 ^ 6 ∨ c = b 1 ^ 6 ∨ c = 0 := by
  have hpoly : (C (a 0) * X + C (b 0)) ^ 6 + (C (a 1) * X + C (b 1)) ^ 6 -
      (C (a 2) * X + C (b 2)) ^ 6 = C c := by
    apply Polynomial.funext
    intro t
    simpa using h t
  have h6 := congrArg (fun P : ℝ[X] => P.coeff 6) hpoly
  have h5 := congrArg (fun P : ℝ[X] => P.coeff 5) hpoly
  have h4 := congrArg (fun P : ℝ[X] => P.coeff 4) hpoly
  norm_num [coeff_add, coeff_sub, sixth_affine_coeff, Nat.choose] at h6 h5 h4
  apply real_sextic_line_coefficients a b c
  · linarith only [h6]
  · nlinarith only [h5]
  · nlinarith only [h4]
  · simpa using h 0

/-- A real affine line contained in a non-sixth-power level of the sextic
cannot pass through an integer point unless its direction is zero. -/
theorem no_real_sextic_line_through_integer_point (c : ℤ) (hc : c ∉ PowerValues 6)
    (a : Fin 3 → ℝ) (b : Fin 3 → ℤ)
    (h : ∀ t : ℝ, (a 0 * t + b 0) ^ 6 + (a 1 * t + b 1) ^ 6 -
      (a 2 * t + b 2) ^ 6 = c) : a = 0 := by
  have hnot (n : ℤ) : (c : ℝ) ≠ (n : ℝ) ^ 6 := by
    intro heq
    have heq' : c = n ^ 6 := by exact_mod_cast heq
    apply hc
    rw [← even_power_range 6 (by decide)]
    exact ⟨n, heq'.symm⟩
  rcases real_sextic_line a (fun k => (b k : ℝ)) c h with ha | h0 | h1 | hc0
  · exact ha
  · exact (hnot (b 0) h0).elim
  · exact (hnot (b 1) h1).elim
  · exact (hnot 0 (by simpa using hc0)).elim

#print axioms real_sextic_line_coefficients
-- 'Erdos477.Geometry.real_sextic_line_coefficients' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms no_real_sextic_line_through_integer_point
-- 'Erdos477.Geometry.no_real_sextic_line_through_integer_point' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
