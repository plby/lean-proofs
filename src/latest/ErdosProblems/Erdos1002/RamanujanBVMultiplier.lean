import ErdosProblems.Erdos1002.IntegerDiscreteAbel
import ErdosProblems.Erdos1002.RamanujanIncompleteOrthogonality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Integer BV multipliers for products of Ramanujan sums

This is the exact Hermitian Abel estimate used in the fixed-away
square-function calculation.  It combines the all-integer incomplete
orthogonality theorem with integer discrete summation by parts, so the
complex conjugate, right endpoint, and every variation term are explicit.
-/

open Finset
open scoped ArithmeticFunction.sigma BigOperators ComplexConjugate

namespace Erdos1002

noncomputable section

/-- Finite all-integer BV multiplier estimate for distinct Ramanujan
moduli. -/
theorem norm_weighted_ramanujan_product_int_le
    (w : ℤ → ℂ) {u v : ℤ} (huv : u ≤ v) {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖∑ n ∈ Icc u v,
      (ramanujanSum p n * conj (ramanujanSum p' n)) * w n‖ ≤
      (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) *
        (‖w v‖ + ∑ n ∈ Ico u v, ‖w n - w (n + 1)‖) := by
  apply norm_sum_Icc_int_mul_le_intervalBound'
    (fun n : ℤ ↦ ramanujanSum p n * conj (ramanujanSum p' n))
    w huv
  intro i j _hij
  exact ramanujan_incomplete_orthogonality_Icc_conj i j hp hp' hpp'

/-- Supremum-plus-total-variation form. -/
theorem norm_weighted_ramanujan_product_int_le_sup_add_variation
    (w : ℤ → ℂ) {u v : ℤ} (huv : u ≤ v) {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p')
    {B V : ℝ} (hSup : ‖w v‖ ≤ B)
    (hVar : (∑ n ∈ Ico u v, ‖w n - w (n + 1)‖) ≤ V) :
    ‖∑ n ∈ Icc u v,
      (ramanujanSum p n * conj (ramanujanSum p' n)) * w n‖ ≤
      (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) * (B + V) := by
  apply norm_sum_Icc_int_mul_le_sup_add_variation
    (fun n : ℤ ↦ ramanujanSum p n * conj (ramanujanSum p' n))
    w huv
  · positivity
  · intro i j _hij
    exact ramanujan_incomplete_orthogonality_Icc_conj i j hp hp' hpp'
  · exact hSup
  · exact hVar

end

end Erdos1002
