import ErdosProblems.Erdos520.ThinEuler
import Mathlib.NumberTheory.Chebyshev

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Reciprocal-prime mass of a thin schedule block

Mathlib currently contains Chebyshev's upper bound for the prime-counting
function, but not the Mertens estimate for the sum of reciprocal primes.  This
file isolates exactly that missing analytic input and proves the schedule-side
consequence used in equation (23).
-/

/-- The sum of `1 / p` over primes at most `x`. -/
noncomputable def primeReciprocalPrefix (x : ℕ) : ℝ :=
  ∑ p ∈ (x + 1).primesBelow, (p : ℝ)⁻¹

/-- The real-valued `log log` scale at a natural endpoint. -/
noncomputable def logLogNat (x : ℕ) : ℝ :=
  Real.log (Real.log (x : ℝ))

/-- A standard effective Mertens hypothesis for reciprocal primes.  The
constant `B` cancels between the endpoints of a thin block, while the
`D / log x` remainder is much smaller than the block width on Caich's
schedule.

This is the precise analytic number-theory input absent from Mathlib: its
existing `Chebyshev.eventually_primeCounting_le` does not itself expose the
required partial-summation corollary. -/
def ReciprocalPrimeMertensBound (B D : ℝ) (N : ℕ) : Prop :=
  ∀ x : ℕ, N ≤ x →
    |primeReciprocalPrefix x - (logLogNat x + B)| ≤ D / Real.log (x : ℝ)

/-- A fresh block is exactly the difference of its two reciprocal-prime
prefix sums. -/
theorem freshReciprocalSum_eq_prefix_sub {a b : ℕ} (hab : a ≤ b) :
    freshReciprocalSum a b = primeReciprocalPrefix b - primeReciprocalPrefix a := by
  classical
  have hdisj := primesBelow_succ_disjoint_freshPrimes a b
  have hunion := primesBelow_succ_eq_union_freshPrimes hab
  rw [primeReciprocalPrefix, primeReciprocalPrefix, freshReciprocalSum]
  rw [hunion, sum_union hdisj]
  ring

/-- Endpoint form of the reciprocal-prime Mertens estimate.  This lemma keeps
the exact two error terms, before specializing to a schedule. -/
theorem freshReciprocalSum_le_logLog_sub_add_errors
    {B D : ℝ} {N a b : ℕ}
    (hM : ReciprocalPrimeMertensBound B D N)
    (hNa : N ≤ a) (hab : a ≤ b) :
    freshReciprocalSum a b ≤
      logLogNat b - logLogNat a +
        D / Real.log (b : ℝ) + D / Real.log (a : ℝ) := by
  have hea := hM a hNa
  have heb := hM b (hNa.trans hab)
  rw [freshReciprocalSum_eq_prefix_sub hab]
  have hea' :
      -(D / Real.log (a : ℝ)) ≤
        primeReciprocalPrefix a - (logLogNat a + B) :=
    (neg_le_of_abs_le hea)
  have heb' :
      primeReciprocalPrefix b - (logLogNat b + B) ≤
        D / Real.log (b : ℝ) :=
    (le_of_abs_le heb)
  linarith

/-- If the two endpoint errors are each at most `A / ell`, a block of
`log log` width at most `1 / ell` has reciprocal-prime mass at most
`(1 + 2 A) / ell`. -/
theorem freshReciprocalSum_le_of_mertens_and_endpoint_errors
    {B D A : ℝ} {N a b ell : ℕ}
    (hM : ReciprocalPrimeMertensBound B D N)
    (hNa : N ≤ a) (hab : a ≤ b) (_hell : 0 < ell)
    (hwidth : logLogNat b - logLogNat a ≤ 1 / (ell : ℝ))
    (herrA : D / Real.log (a : ℝ) ≤ A / (ell : ℝ))
    (herrB : D / Real.log (b : ℝ) ≤ A / (ell : ℝ)) :
    freshReciprocalSum a b ≤ (1 + 2 * A) / (ell : ℝ) := by
  calc
    freshReciprocalSum a b ≤
        logLogNat b - logLogNat a +
          D / Real.log (b : ℝ) + D / Real.log (a : ℝ) :=
      freshReciprocalSum_le_logLog_sub_add_errors hM hNa hab
    _ ≤ 1 / (ell : ℝ) + A / (ell : ℝ) + A / (ell : ℝ) := by
      gcongr
    _ = (1 + 2 * A) / (ell : ℝ) := by ring

/-- The concrete `O(1 / ell)` schedule consequence.  The condition
`D * ell ≤ log a` is automatic eventually on Caich's schedule (where the
lower endpoint is doubly exponential in a power of `ell`). -/
theorem freshReciprocalSum_le_three_div
    {B D : ℝ} {N a b ell : ℕ}
    (hM : ReciprocalPrimeMertensBound B D N)
    (hNa : N ≤ a) (ha : 2 ≤ a) (hab : a ≤ b)
    (hell : 0 < ell)
    (hwidth : logLogNat b - logLogNat a ≤ 1 / (ell : ℝ))
    (hlarge : D * (ell : ℝ) ≤ Real.log (a : ℝ)) :
    freshReciprocalSum a b ≤ 3 / (ell : ℝ) := by
  have hlogapos : 0 < Real.log (a : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < a by omega)
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hlogab : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log (by positivity) habR
  have hlogbpos : 0 < Real.log (b : ℝ) := hlogapos.trans_le hlogab
  have hellR : 0 < (ell : ℝ) := by exact_mod_cast hell
  have herrA : D / Real.log (a : ℝ) ≤ 1 / (ell : ℝ) := by
    rw [div_le_div_iff₀ hlogapos hellR]
    simpa [mul_comm] using! hlarge
  have herrB : D / Real.log (b : ℝ) ≤ 1 / (ell : ℝ) := by
    rw [div_le_div_iff₀ hlogbpos hellR]
    calc
      D * (ell : ℝ) ≤ Real.log (a : ℝ) := hlarge
      _ ≤ Real.log (b : ℝ) := hlogab
      _ = 1 * Real.log (b : ℝ) := by ring
  have h := freshReciprocalSum_le_of_mertens_and_endpoint_errors
    (A := (1 : ℝ)) hM hNa hab hell hwidth herrA herrB
  norm_num at h
  exact h

end Problem520
end Erdos
