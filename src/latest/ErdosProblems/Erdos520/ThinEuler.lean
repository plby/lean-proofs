import ErdosProblems.Erdos520.FreshExpansion
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset
open scoped BigOperators

namespace Erdos
namespace Problem520

/-- Reciprocal-prime mass of the thin block `(a,b]`. -/
noncomputable def freshReciprocalSum (a b : ℕ) : ℝ :=
  ∑ p ∈ freshPrimes a b, (p : ℝ)⁻¹

/-- The coefficient weight produced by the `L^(2r)` Bonami inequality. -/
noncomputable def freshBonamiWeight (t : ℝ) (S : Finset ℕ) : ℝ :=
  t ^ #S / (freshProduct S : ℝ)

theorem prod_div_cast_freshProduct (t : ℝ) (S : Finset ℕ) :
    (∏ p ∈ S, t / (p : ℝ)) = freshBonamiWeight t S := by
  simp [freshBonamiWeight, freshProduct, Finset.prod_div_distrib]

/-- The subset sum in equation (22) is exactly the corresponding finite
Euler product. -/
theorem sum_freshBonamiWeight_eq_eulerProduct (t : ℝ) (a b : ℕ) :
    (∑ S ∈ (freshPrimes a b).powerset, freshBonamiWeight t S) =
      ∏ p ∈ freshPrimes a b, (1 + t / (p : ℝ)) := by
  classical
  rw [show (∏ p ∈ freshPrimes a b, (1 + t / (p : ℝ))) =
      ∏ p ∈ freshPrimes a b, (t / (p : ℝ) + 1) by
    apply Finset.prod_congr rfl
    intro p _hp
    ring]
  rw [Finset.prod_add (fun p : ℕ => t / (p : ℝ)) (fun _ => 1)]
  simp only [Finset.prod_const_one, mul_one]
  exact Finset.sum_congr rfl fun S _hS =>
    (prod_div_cast_freshProduct t S).symm

/-- Elementary exponential majorant for the thin-block Euler product. -/
theorem eulerProduct_le_exp_freshReciprocalSum
    {t : ℝ} (ht : 0 ≤ t) (a b : ℕ) :
    (∏ p ∈ freshPrimes a b, (1 + t / (p : ℝ))) ≤
      Real.exp (t * freshReciprocalSum a b) := by
  classical
  calc
    (∏ p ∈ freshPrimes a b, (1 + t / (p : ℝ)))
        ≤ ∏ p ∈ freshPrimes a b, Real.exp (t / (p : ℝ)) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hp0 : (0 : ℝ) < p := by
              exact_mod_cast (mem_freshPrimes.mp hp).1.pos
            exact add_nonneg zero_le_one (div_nonneg ht hp0.le)
          · intro p hp
            simpa [add_comm] using! Real.add_one_le_exp (t / (p : ℝ))
    _ = Real.exp (∑ p ∈ freshPrimes a b, t / (p : ℝ)) := by
      rw [Real.exp_sum]
    _ = Real.exp (t * freshReciprocalSum a b) := by
      congr 1
      simp [freshReciprocalSum, div_eq_mul_inv, Finset.mul_sum]

/-- If a schedule has reciprocal-prime mass `O(1/ell)`, the exact Euler
factor in (22) has the required `exp(O(t/ell))` bound. -/
theorem sum_freshBonamiWeight_le_exp
    {t C : ℝ} (ht : 0 ≤ t) {ell a b : ℕ} (_hell : 0 < ell)
    (hrecip : freshReciprocalSum a b ≤ C / ell) :
    (∑ S ∈ (freshPrimes a b).powerset, freshBonamiWeight t S) ≤
      Real.exp (C * t / ell) := by
  rw [sum_freshBonamiWeight_eq_eulerProduct]
  refine (eulerProduct_le_exp_freshReciprocalSum ht a b).trans ?_
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left hrecip ht
  calc
    t * freshReciprocalSum a b ≤ t * (C / ell) := this
    _ = C * t / ell := by ring

end Problem520
end Erdos
