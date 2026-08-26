import ErdosProblems.Erdos67b.MRGSA9AlternatingEuler

/-!
# The outside Euler-product bound in GS A.11

This controls the factors outside the two deleted blocks, keeping their
linear real parts and charging only the absolutely summable prime-square
error.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b.MRMultiplicativeEuler

/-- On any line `Re s ≥ 1`, every prime Euler variable has norm at most
one half. -/
theorem norm_prime_cpow_neg_sigma_add_I_mul_le_half
    {p : ℕ} (hp : p.Prime) {sigma : ℝ} (hsigma : 1 ≤ sigma) (t : ℝ) :
    ‖(p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      (1 / 2 : ℝ) := by
  rw [Erdos67b.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul
    hp.pos sigma t]
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpow : (p : ℝ) ^ (-sigma) ≤ (p : ℝ) ^ (-1 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hpOne
    linarith
  rw [Real.rpow_neg_one] at hpow
  calc
    (p : ℝ) ^ (-sigma) ≤ (p : ℝ)⁻¹ := hpow
    _ ≤ (2 : ℝ)⁻¹ := by
      apply inv_anti₀ (by norm_num)
      exact_mod_cast hp.two_le
    _ = 1 / 2 := by norm_num

/-- Finite-product majorant for an arbitrary set of prime local factors. -/
theorem norm_prod_gsA9LocalEulerFactor_le_exp_linear_add_square
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    {sigma : ℝ} (hsigma : 1 ≤ sigma) (t : ℝ) :
    ‖∏ p ∈ S,
        gsA9LocalEulerFactor f
          ((sigma : ℂ) + Complex.I * (t : ℂ)) p‖ ≤
      Real.exp
        ((∑ p ∈ S,
            (f p * (p : ℂ) ^
              (-((sigma : ℂ) + Complex.I * (t : ℂ)))).re) +
          3 * ∑ p ∈ S,
            ‖(p : ℂ) ^
              (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2) := by
  rw [norm_prod]
  calc
    (∏ p ∈ S,
        ‖gsA9LocalEulerFactor f
          ((sigma : ℂ) + Complex.I * (t : ℂ)) p‖) ≤
      ∏ p ∈ S,
        Real.exp
          ((f p * (p : ℂ) ^
              (-((sigma : ℂ) + Complex.I * (t : ℂ)))).re +
            3 * ‖(p : ℂ) ^
              (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact norm_nonneg _
      · intro p hp
        unfold gsA9LocalEulerFactor
        simpa only [pow_one] using
          norm_localEulerFactor_le_exp
            (fun e ↦ f (p ^ e))
            (by simpa using hmul.1)
            (fun e ↦ hbound (p ^ e) (pow_pos (hprime p hp).pos e))
            ((p : ℂ) ^
              (-((sigma : ℂ) + Complex.I * (t : ℂ))))
            (norm_prime_cpow_neg_sigma_add_I_mul_le_half
              (hprime p hp) hsigma t)
    _ = Real.exp
        (∑ p ∈ S,
          ((f p * (p : ℂ) ^
              (-((sigma : ℂ) + Complex.I * (t : ℂ)))).re +
            3 * ‖(p : ℂ) ^
              (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2)) := by
      rw [Real.exp_sum]
    _ = Real.exp
        ((∑ p ∈ S,
            (f p * (p : ℂ) ^
              (-((sigma : ℂ) + Complex.I * (t : ℂ)))).re) +
          3 * ∑ p ∈ S,
            ‖(p : ℂ) ^
              (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2) := by
      congr 1
      rw [Finset.sum_add_distrib, Finset.mul_sum]

end

end Erdos67b.MRHalaszBands
