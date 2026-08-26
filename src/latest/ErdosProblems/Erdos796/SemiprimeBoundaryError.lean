import ErdosProblems.Erdos796.SemiprimeSummatory
import ErdosProblems.Erdos796.ElementaryPruningErrors

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The small-prime boundary in the semiprime summatory formula

The unrestricted quotient sum differs from the semiprime count only by the
triangular collection of partners smaller than the chosen first prime.  A
square prime-count bound is enough on the second-order scale.
-/

namespace Erdos796

open Filter Topology
open scoped BigOperators Nat.Prime

/-- The prime-counting sum before imposing the order on the two prime
factors. -/
def primeQuotientSum (n : ℕ) : ℕ :=
  ∑ p ∈ Nat.primesLE n.sqrt, Nat.primeCounting (n / p)

/-- Exact decomposition into the semiprime count and the smaller-partner
boundary. -/
theorem primeQuotientSum_eq_semiprime_add_boundary (n : ℕ) :
    primeQuotientSum n = semiprimeCount n +
      ∑ p ∈ Nat.primesLE n.sqrt, Nat.primeCounting (p - 1) := by
  rw [primeQuotientSum, semiprimeCount_eq_sum_primeCounting_sub,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Nat.mem_primesLE.mp hp
  have hppos : 0 < p := hp'.2.pos
  have hpdiv : p ≤ n / p :=
    (Nat.le_div_iff_mul_le hppos).2 (Nat.le_sqrt.mp hp'.1)
  have hpred : Nat.primeCounting (p - 1) ≤
      Nat.primeCounting (n / p) :=
    Nat.monotone_primeCounting (by omega)
  omega

/-- The boundary has at most `pi(sqrt n)^2` elements. -/
theorem semiprime_boundary_le_primeCounting_sqrt_sq (n : ℕ) :
    (∑ p ∈ Nat.primesLE n.sqrt, Nat.primeCounting (p - 1)) ≤
      Nat.primeCounting n.sqrt ^ 2 := by
  calc
    (∑ p ∈ Nat.primesLE n.sqrt, Nat.primeCounting (p - 1)) ≤
        ∑ _p ∈ Nat.primesLE n.sqrt,
          Nat.primeCounting n.sqrt := by
      apply Finset.sum_le_sum
      intro p hp
      exact Nat.monotone_primeCounting (by
        have hp' := (Nat.mem_primesLE.mp hp).1
        omega)
    _ = Nat.primeCounting n.sqrt ^ 2 := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul,
        Nat.primesLE_card_eq_primeCounting]
      simp [pow_two]

theorem semiprimeCount_le_primeQuotientSum (n : ℕ) :
    semiprimeCount n ≤ primeQuotientSum n := by
  rw [primeQuotientSum_eq_semiprime_add_boundary]
  omega

theorem primeQuotientSum_le_semiprime_add_square (n : ℕ) :
    primeQuotientSum n ≤
      semiprimeCount n + Nat.primeCounting n.sqrt ^ 2 := by
  rw [primeQuotientSum_eq_semiprime_add_boundary]
  exact Nat.add_le_add_left
    (semiprime_boundary_le_primeCounting_sqrt_sq n) _

/-- The quotient-sum ordering boundary is negligible on the second-order
scale. -/
theorem normalized_primeQuotientSum_sub_semiprime_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        ((primeQuotientSum n : ℝ) - (semiprimeCount n : ℝ)) /
          secondOrderScale n)
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_
    ElementaryPruningErrors.primeCounting_sqrt_sq_negligible
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      exact div_pos (by positivity)
        (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
    exact div_nonneg (sub_nonneg.mpr (by
      exact_mod_cast semiprimeCount_le_primeQuotientSum n)) hscale.le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      exact div_pos (by positivity)
        (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
    rw [div_le_div_iff_of_pos_right hscale]
    have hupper := primeQuotientSum_le_semiprime_add_square n
    have hupperReal : (primeQuotientSum n : ℝ) ≤
        (semiprimeCount n : ℝ) +
          (Nat.primeCounting n.sqrt ^ 2 : ℕ) := by
      exact_mod_cast hupper
    linarith

end Erdos796
