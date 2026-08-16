import Wikipedia.GreenTao.Sieve.ComplexLocalFactorControl
import Mathlib.Analysis.Normed.Ring.InfiniteProd

/-!
# Uniform tails of complex Euler products

The local estimates used in the smooth sieve are uniform in the Fourier
variables but the local-factor family itself changes with all asymptotic
parameters.  Ordinary convergence of one fixed Euler product is therefore
not enough.

This file packages the required dominated-convergence statement.  If a
varying family has the common bound

`‖L_n(p) - 1‖ ≤ C / p²`

and each fixed prime factor tends to one, then the full unordered products
also tend to one.  A second theorem specializes this to the standard
large-prime mask: all factors at `p ≤ w_n` are replaced by one, and
`w_n → ∞`.  No bound on the Fourier variables is needed because the local
square-error estimate is already uniform in them.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

namespace HasComplexPrimeSquareError

/-- Dominated convergence for a varying family of complex Euler products
with one common prime-square error majorant. -/
theorem tendsto_tprod_one
    {α : Type*} {𝓕 : Filter α}
    {C : ℝ} {localFactor : α → Nat.Primes → ℂ}
    (herror :
      ∀ᶠ n in 𝓕,
        HasComplexPrimeSquareError C (localFactor n))
    (hpoint :
      ∀ p : Nat.Primes,
        Tendsto (fun n => localFactor n p)
          𝓕 (𝓝 1)) :
    Tendsto
      (fun n => ∏' p : Nat.Primes, localFactor n p)
      𝓕 (𝓝 1) := by
  have hsum :
      Summable
        (fun p : Nat.Primes =>
          C / (p : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using
      summable_prime_inv_sq.mul_left C
  have hpointError :
      ∀ p : Nat.Primes,
        Tendsto
          (fun n => localFactor n p - 1)
          𝓕 (𝓝 0) := by
    intro p
    simpa using
      (hpoint p).sub
        (tendsto_const_nhds :
          Tendsto (fun _n : α => (1 : ℂ)) 𝓕 (𝓝 1))
  have hbound :
      ∀ᶠ n in 𝓕, ∀ p : Nat.Primes,
        ‖localFactor n p - 1‖ ≤
          C / (p : ℝ) ^ 2 :=
    herror.mono fun _n hn p => hn.error_le p
  simpa using
    (tendsto_tprod_one_add_of_dominated_convergence
      (R := ℂ)
      (g := fun _p : Nat.Primes => 0)
      hsum hpointError hbound)

end HasComplexPrimeSquareError

/-- Once a numerical cutoff tends to infinity, the factor at each fixed
prime in the corresponding bounded mask is eventually exactly one. -/
theorem tendsto_boundedMaskedComplexPrimeLocalFactor_one
    {α : Type*} {𝓕 : Filter α}
    (w : α → ℕ)
    (localFactor : α → Nat.Primes → ℂ)
    (hw : Tendsto w 𝓕 atTop)
    (p : Nat.Primes) :
    Tendsto
      (fun n =>
        boundedMaskedComplexPrimeLocalFactor
          (w n) (localFactor n) p)
  𝓕 (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [hw (eventually_ge_atTop (p : ℕ))]
    with n hn
  exact
    (boundedMaskedComplexPrimeLocalFactor_of_le hn).symm

/-- **Uniform large-prime Euler-tail theorem.**  The unmasked local family
may vary arbitrarily with `n`.  It is enough to have one common
`O(p⁻²)` estimate beyond the varying cutoff `w n`. -/
theorem tendsto_tprod_boundedMaskedComplexPrimeLocalFactor_one
    {α : Type*} {𝓕 : Filter α}
    {C : ℝ} (hC : 0 ≤ C)
    (w : α → ℕ)
    (localFactor : α → Nat.Primes → ℂ)
    (hw : Tendsto w 𝓕 atTop)
    (herror :
      ∀ᶠ n in 𝓕, ∀ p : Nat.Primes,
        w n < (p : ℕ) →
          ‖localFactor n p - 1‖ ≤
            C / (p : ℝ) ^ 2) :
    Tendsto
      (fun n =>
        ∏' p : Nat.Primes,
          boundedMaskedComplexPrimeLocalFactor
            (w n) (localFactor n) p)
      𝓕 (𝓝 1) := by
  apply
    HasComplexPrimeSquareError.tendsto_tprod_one
  · filter_upwards [herror] with n hn
    exact
      hasComplexPrimeSquareError_boundedMasked
        (w n) hC (fun p hp => hn p hp)
  · exact fun p =>
      tendsto_boundedMaskedComplexPrimeLocalFactor_one
        w localFactor hw p

end Wikipedia.SzemeredisTheorem
