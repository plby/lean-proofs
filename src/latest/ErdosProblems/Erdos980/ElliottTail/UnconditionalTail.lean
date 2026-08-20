import ErdosProblems.Erdos980.ElliottTail.FinalAssembly
import ErdosProblems.Erdos980.ElliottTail.OddPrimeMediumApplication
import ErdosProblems.Erdos980.ElliottTail.QuadraticMediumSieve

/-!
# Unconditional Elliott tail for every exponent

This module combines the unconditional quadratic and odd-prime medium
estimates, then applies least-prime-factor reduction to obtain the exact
uniformly negligible tail required for Erdős Problem 980.
-/

namespace Erdos980.ElliottTail

/-- The unconditional medium estimate for every prime exponent. -/
theorem unconditionalPrimeExponentMediumEstimate
    (ell : ℕ) (hell : ell.Prime) :
    PrimeExponentMediumEstimate ell :=
  allPrimeExponentMediumEstimate_of_two_of_odd
    quadraticPrimeExponentMediumEstimate oddPrimeExponentMediumEstimate
    ell hell

/-- Elliott's unconditional uniform-tail estimate for every exponent
`k ≥ 2`, in the exact least-nonresidue model and Erdős 980 scale. -/
theorem unconditional_uniformlyNegligibleTail
    (k : ℕ) (hk : 2 ≤ k) :
    UniformlyNegligibleTail
      (primeValueTail (leastNonresidueModel k hk)) erdos980Scale :=
  uniformlyNegligibleTail_of_all_primeExponentMedium
    unconditionalPrimeExponentMediumEstimate k hk

end Erdos980.ElliottTail
