/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.Elementary
import ErdosProblems.Erdos387.SieveInstantiation

/-! Basic shifted products and sifted candidate sets used by both moments and sieves. -/

namespace Erdos851

namespace ShiftSieve

/-- The product whose prime divisors encode the forbidden shifted classes. -/
def shiftedProduct (shifts : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ s ∈ shifts, (a - s)

/-- Points in `(X,2X]` for which every shifted residual avoids all primes in `(z,Y)`. -/
def siftedShiftCandidates (shifts : Finset ℕ) (X z Y : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun a ↦
    Nat.Coprime (Erdos387.sievePrimeProduct z Y) (shiftedProduct shifts a)

end ShiftSieve

end Erdos851
