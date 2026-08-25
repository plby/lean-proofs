import ErdosProblems.Erdos67.Pretentious

/-!
# Complex powers in the Halász Euler deficit

This file records the exact factorization of the smoothed complex prime
weight on the line `s = σ + it`.  It also gives the elementary lower bound
which compares the smoothing factor at `σ = 1 + 1 / log X` with the
unsmoothed pretentious prime weight.
-/

open Complex
open scoped ComplexConjugate

namespace Erdos67.HalaszCpowDeficit

noncomputable section

/-- The norm of the prime weight `p^(-(σ+it))` depends only on `σ`. -/
theorem norm_nat_cpow_neg_sigma_add_I_mul
    {p : ℕ} (hp : 0 < p) (sigma t : ℝ) :
    ‖(p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ =
      (p : ℝ) ^ (-sigma) := by
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hp)]
  simp

/-- Exact separation of the real damping and the Archimedean phase. -/
theorem nat_cpow_neg_sigma_add_I_mul
    {p : ℕ} (hp : 0 < p) (sigma t : ℝ) :
    (p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ))) =
      (((p : ℝ) ^ (-sigma) : ℝ) : ℂ) * conj (archimedeanTwist t p) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [show -((sigma : ℂ) + Complex.I * (t : ℂ)) =
      ((-sigma : ℝ) : ℂ) + (-(Complex.I * (t : ℂ))) by
        push_cast
        ring]
  rw [Complex.cpow_add _ _ hpC, ← conj_archimedeanTwist]
  congr 1
  rw [← Complex.ofReal_natCast]
  exact (Complex.ofReal_cpow hpR (-sigma)).symm

/-- The real part of a smoothed Euler prime term is precisely the real
damping times the pretentious correlation at that prime. -/
theorem mul_nat_cpow_neg_sigma_add_I_mul_re
    {p : ℕ} (hp : 0 < p) (z : ℂ) (sigma t : ℝ) :
    (z * (p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))).re =
      (p : ℝ) ^ (-sigma) * (z * conj (archimedeanTwist t p)).re := by
  rw [nat_cpow_neg_sigma_add_I_mul hp]
  rw [show z * ((((p : ℝ) ^ (-sigma) : ℝ) : ℂ) *
        conj (archimedeanTwist t p)) =
      (((p : ℝ) ^ (-sigma) : ℝ) : ℂ) *
        (z * conj (archimedeanTwist t p)) by ring]
  simp

/-- Combined norm-minus-real-part form: the Halász Euler deficit is the
smoothed pretentious deficit. -/
theorem nat_cpow_deficit_eq_rpow_mul_pretentious_deficit
    {p : ℕ} (hp : 0 < p) (z : ℂ) (sigma t : ℝ) :
    ‖(p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ -
        (z * (p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))).re =
      (p : ℝ) ^ (-sigma) *
        (1 - (z * conj (archimedeanTwist t p)).re) := by
  rw [norm_nat_cpow_neg_sigma_add_I_mul hp,
    mul_nat_cpow_neg_sigma_add_I_mul_re hp]
  ring

/-- Prime-specialized norm identity. -/
theorem norm_prime_cpow_neg_sigma_add_I_mul
    (p : Nat.Primes) (sigma t : ℝ) :
    ‖(p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ =
      (p : ℝ) ^ (-sigma) :=
  norm_nat_cpow_neg_sigma_add_I_mul p.prop.pos sigma t

/-- Prime-specialized real-part identity. -/
theorem mul_prime_cpow_neg_sigma_add_I_mul_re
    (p : Nat.Primes) (z : ℂ) (sigma t : ℝ) :
    (z * (p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))).re =
      (p : ℝ) ^ (-sigma) * (z * conj (archimedeanTwist t p)).re :=
  mul_nat_cpow_neg_sigma_add_I_mul_re p.prop.pos z sigma t

/-- Prime-specialized exact deficit identity. -/
theorem prime_cpow_deficit_eq_rpow_mul_pretentious_deficit
    (p : Nat.Primes) (z : ℂ) (sigma t : ℝ) :
    ‖(p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ -
        (z * (p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))).re =
      (p : ℝ) ^ (-sigma) *
        (1 - (z * conj (archimedeanTwist t p)).re) :=
  nat_cpow_deficit_eq_rpow_mul_pretentious_deficit
    p.prop.pos z sigma t

/-- If `p ≤ X` and `X > 1`, the extra damping at
`σ = 1 + 1 / log X` costs at most the absolute factor `exp (-1)`. -/
theorem exp_neg_one_div_natCast_le_rpow_neg_one_add_inv_log
    {p X : ℕ} (hp : 0 < p) (hX : 1 < X) (hpX : p ≤ X) :
    Real.exp (-1) / (p : ℝ) ≤
      (p : ℝ) ^ (-(1 + 1 / Real.log (X : ℝ))) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hXRone : (1 : ℝ) < X := by exact_mod_cast hX
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hXRone
  have hpXR : (p : ℝ) ≤ X := by exact_mod_cast hpX
  have hlogpX : Real.log (p : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hpR hpXR
  have hphase :
      Real.exp (-1) ≤ (p : ℝ) ^ (-(1 / Real.log (X : ℝ))) := by
    rw [Real.rpow_def_of_pos hpR]
    rw [Real.exp_le_exp]
    have hdiv : Real.log (p : ℝ) / Real.log (X : ℝ) ≤ 1 :=
      (div_le_one hlogX).2 hlogpX
    calc
      (-1 : ℝ) ≤ -(Real.log (p : ℝ) / Real.log (X : ℝ)) := by linarith
      _ = Real.log (p : ℝ) * (-(1 / Real.log (X : ℝ))) := by ring
  rw [show -(1 + 1 / Real.log (X : ℝ)) =
      (-1 : ℝ) + (-(1 / Real.log (X : ℝ))) by ring]
  rw [Real.rpow_add hpR, Real.rpow_neg_one]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hphase (inv_nonneg.mpr hpR.le)

/-- Prime-specialized form of the smoothing lower bound. -/
theorem exp_neg_one_div_prime_le_rpow_neg_one_add_inv_log
    (p : Nat.Primes) {X : ℕ} (hX : 1 < X) (hpX : p ≤ X) :
    Real.exp (-1) / (p : ℝ) ≤
      (p : ℝ) ^ (-(1 + 1 / Real.log (X : ℝ))) :=
  exp_neg_one_div_natCast_le_rpow_neg_one_add_inv_log
    p.prop.pos hX hpX

/-- At the smoothed point `σ = 1 + 1 / log X`, the exact Euler deficit
dominates `exp (-1)` times the usual pretentious summand. -/
theorem exp_neg_one_mul_pretentiousTerm_le_prime_cpow_deficit
    (p : Nat.Primes) {X : ℕ} (hX : 1 < X) (hpX : p ≤ X)
    (z : ℂ) (t : ℝ)
    (hz : (z * conj (archimedeanTwist t p)).re ≤ 1) :
    Real.exp (-1) *
        ((1 - (z * conj (archimedeanTwist t p)).re) / (p : ℝ)) ≤
      ‖(p : ℂ) ^
          (-(((1 + 1 / Real.log (X : ℝ) : ℝ) : ℂ) +
            Complex.I * (t : ℂ)))‖ -
        (z * (p : ℂ) ^
          (-(((1 + 1 / Real.log (X : ℝ) : ℝ) : ℂ) +
            Complex.I * (t : ℂ)))).re := by
  rw [prime_cpow_deficit_eq_rpow_mul_pretentious_deficit]
  have hfactor : 0 ≤ 1 - (z * conj (archimedeanTwist t p)).re := by linarith
  calc
    Real.exp (-1) *
        ((1 - (z * conj (archimedeanTwist t p)).re) / (p : ℝ)) =
        (Real.exp (-1) / (p : ℝ)) *
          (1 - (z * conj (archimedeanTwist t p)).re) := by ring
    _ ≤ (p : ℝ) ^ (-(1 + 1 / Real.log (X : ℝ))) *
          (1 - (z * conj (archimedeanTwist t p)).re) :=
      mul_le_mul_of_nonneg_right
        (exp_neg_one_div_prime_le_rpow_neg_one_add_inv_log p hX hpX) hfactor

end

end Erdos67.HalaszCpowDeficit
