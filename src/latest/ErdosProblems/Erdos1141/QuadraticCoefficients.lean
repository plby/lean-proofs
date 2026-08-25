import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

/-!
# Nonnegative divisor coefficients of quadratic characters

For a quadratic character `χ`, the coefficients of `ζ(s) L(s, χ)` are
nonnegative.  This module records their local factors in a real-valued form
suited to finite Euler products and Rankin's inequality.
-/

namespace Pollack17

open scoped BigOperators ComplexOrder
open ArithmeticFunction

variable {m : ℕ}

/-- The divisor coefficient `∑ d ∣ n, χ(d)`, regarded as a real number. -/
noncomputable def divisorCoefficient (χ : DirichletCharacter ℂ m) (n : ℕ) : ℝ :=
  (χ.zetaMul n).re

theorem divisorCoefficient_nonneg (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) (n : ℕ) :
    0 ≤ divisorCoefficient χ n :=
  (Complex.nonneg_iff.mp (χ.zetaMul_nonneg hχ.sq_eq_one n)).1

theorem ofReal_divisorCoefficient (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) (n : ℕ) :
    (divisorCoefficient χ n : ℂ) = χ.zetaMul n := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (χ.zetaMul_nonneg hχ.sq_eq_one n)).2

@[simp] theorem divisorCoefficient_zero (χ : DirichletCharacter ℂ m) :
    divisorCoefficient χ 0 = 0 := by
  simp [divisorCoefficient]

@[simp] theorem divisorCoefficient_one (χ : DirichletCharacter ℂ m) :
    divisorCoefficient χ 1 = 1 := by
  simp [divisorCoefficient, χ.isMultiplicative_zetaMul.map_one]

theorem divisorCoefficient_mul (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) {a b : ℕ} (hab : a.Coprime b) :
    divisorCoefficient χ (a * b) = divisorCoefficient χ a * divisorCoefficient χ b := by
  apply Complex.ofReal_injective
  push_cast
  rw [ofReal_divisorCoefficient χ hχ, ofReal_divisorCoefficient χ hχ,
    ofReal_divisorCoefficient χ hχ]
  exact χ.isMultiplicative_zetaMul.map_mul_of_coprime hab

theorem zetaMul_prime_pow_eq_sum (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (e : ℕ) :
    χ.zetaMul (p ^ e) = ∑ i ∈ Finset.range (e + 1), χ (p : ZMod m) ^ i := by
  calc
    χ.zetaMul (p ^ e) =
        ∑ d ∈ (p ^ e).divisors, toArithmeticFunction (χ ·) d :=
      coe_zeta_mul_apply (f := toArithmeticFunction (χ ·))
    _ = _ := by
      simp only [toArithmeticFunction, coe_mk, Nat.sum_divisors_prime_pow hp,
    pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]

theorem divisorCoefficient_prime_pow_of_eq_one (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (h : χ (p : ZMod m) = 1) (e : ℕ) :
    divisorCoefficient χ (p ^ e) = e + 1 := by
  simp [divisorCoefficient, zetaMul_prime_pow_eq_sum χ hp, h]

theorem divisorCoefficient_prime_pow_of_eq_zero (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (h : χ (p : ZMod m) = 0) (e : ℕ) :
    divisorCoefficient χ (p ^ e) = 1 := by
  simp [divisorCoefficient, zetaMul_prime_pow_eq_sum χ hp, h]

theorem divisorCoefficient_prime_pow_of_eq_neg_one (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (h : χ (p : ZMod m) = -1) (e : ℕ) :
    divisorCoefficient χ (p ^ e) = if Even e then 1 else 0 := by
  rw [divisorCoefficient, zetaMul_prime_pow_eq_sum χ hp, h, neg_one_geom_sum]
  by_cases he : Even e
  · simp [he, Nat.even_add_one]
  · simp [he, Nat.even_add_one]

theorem divisorCoefficient_prime_pow_le (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    divisorCoefficient χ (p ^ e) ≤ e + 1 := by
  rcases hχ (p : ZMod m) with h | h | h
  · rw [divisorCoefficient_prime_pow_of_eq_zero χ hp h]
    linarith [Nat.cast_nonneg (α := ℝ) e]
  · exact (divisorCoefficient_prime_pow_of_eq_one χ hp h e).le
  · rw [divisorCoefficient_prime_pow_of_eq_neg_one χ hp h]
    split_ifs <;> linarith [Nat.cast_nonneg (α := ℝ) e]

theorem hasSum_succ_mul_geometric {u : ℝ} (hu : ‖u‖ < 1) :
    HasSum (fun e : ℕ => (e + 1 : ℝ) * u ^ e) ((1 - u)⁻¹ ^ 2) := by
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one,
    one_div, inv_pow] using hasSum_choose_mul_geometric_of_norm_lt_one 1 hu

theorem summable_divisorCoefficient_prime_pow (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) {p : ℕ} (hp : p.Prime)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (fun e : ℕ => divisorCoefficient χ (p ^ e) * u ^ e) := by
  have hu : ‖u‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hu0]
  exact Summable.of_nonneg_of_le
    (fun e => mul_nonneg (divisorCoefficient_nonneg χ hχ _) (pow_nonneg hu0 _))
    (fun e => mul_le_mul_of_nonneg_right
      (divisorCoefficient_prime_pow_le χ hχ hp e) (pow_nonneg hu0 _))
    (hasSum_succ_mul_geometric hu).summable

theorem local_divisorCoefficient_sum_le (χ : DirichletCharacter ℂ m)
    (hχ : MulChar.IsQuadratic χ) {p : ℕ} (hp : p.Prime)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (∑' e : ℕ, divisorCoefficient χ (p ^ e) * u ^ e) ≤ (1 - u)⁻¹ ^ 2 := by
  have hu : ‖u‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hu0]
  exact (Summable.tsum_le_tsum
    (fun e => mul_le_mul_of_nonneg_right
      (divisorCoefficient_prime_pow_le χ hχ hp e) (pow_nonneg hu0 _))
    (summable_divisorCoefficient_prime_pow χ hχ hp hu0 hu1)
    (hasSum_succ_mul_geometric hu).summable).trans_eq
      (hasSum_succ_mul_geometric hu).tsum_eq

theorem hasSum_divisorCoefficient_of_neg_one (χ : DirichletCharacter ℂ m)
    {p : ℕ} (hp : p.Prime) (h : χ (p : ZMod m) = -1)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    HasSum (fun e : ℕ => divisorCoefficient χ (p ^ e) * u ^ e)
      (1 - u ^ 2)⁻¹ := by
  have hu : ‖u‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hu0]
  have hnu : ‖-u‖ < 1 := by simpa only [norm_neg] using hu
  have hs := ((hasSum_geometric_of_norm_lt_one hu).add
    (hasSum_geometric_of_norm_lt_one hnu)).div_const 2
  have hterm (e : ℕ) :
      divisorCoefficient χ (p ^ e) * u ^ e = (u ^ e + (-u) ^ e) / 2 := by
    rw [divisorCoefficient_prime_pow_of_eq_neg_one χ hp h, neg_pow,
      neg_one_pow_eq_ite]
    split_ifs <;> ring
  have hvalue : ((1 - u)⁻¹ + (1 - -u)⁻¹) / 2 = (1 - u ^ 2)⁻¹ := by
    have hminus : 1 - u ≠ 0 := ne_of_gt (sub_pos.mpr hu1)
    have hplus : 1 + u ≠ 0 := ne_of_gt (by linarith)
    have hsquare : 1 - u ^ 2 ≠ 0 := by
      have : 0 < (1 - u) * (1 + u) := mul_pos (sub_pos.mpr hu1) (by linarith)
      nlinarith
    rw [sub_neg_eq_add]
    field_simp [hminus, hplus, hsquare]
    ring
  simpa only [← hterm, hvalue] using hs

end Pollack17
