import Mathlib

namespace Erdos730

/-- Infinitely many consecutive central binomial coefficients have equal prime support. -/
theorem erdos_730_consecutive :
    {n : ℕ | n.centralBinom.primeFactors = (n + 1).centralBinom.primeFactors}.Infinite := by
  sorry

/-- There are infinitely many distinct pairs with identical prime divisors. -/
theorem erdos_730 :
    {z : ℕ × ℕ | z.1 < z.2 ∧
      z.1.centralBinom.primeFactors = z.2.centralBinom.primeFactors}.Infinite := by
  sorry

end Erdos730
