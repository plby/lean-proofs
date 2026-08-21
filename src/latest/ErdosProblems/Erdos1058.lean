import ErdosProblems.Erdos1058.Erdos1058Assembly
import ErdosProblems.Erdos1058.Erdos1058BugeaudLaurentProof

/-!
# Erdős Problem 1058

This file combines the finite certificate development with the specialized
Bugeaud--Laurent interpolation-determinant estimate.  The module split keeps
both substantial kernel checks within Lean's ordinary default resource limits.
-/

noncomputable section

namespace Erdos1058

/-- The specialized Bugeaud--Laurent estimate in the notation used by the
finite assembly. -/
theorem bugeaudLaurentSpecial : BugeaudLaurentSpecial := by
  intro p q a b hp hq hpq ha hb
  simpa only [blMaximum, blBPrime,
    BugeaudLaurent.parameterMaximum, BugeaudLaurent.parameterBPrime] using
      BugeaudLaurent.bugeaudLaurent_special p q a b hp hq hpq ha hb

/-- The resulting bound on the second prime in a putative large solution. -/
theorem largePrimeBound : LargePrimeBound :=
  largePrimeBound_of_bugeaudLaurentSpecial bugeaudLaurentSpecial

/-- Erdős Problem 1058 (Luca): the only positive integers whose factorial
plus one has no prime divisors beyond the first two primes after `n` are
`1, 2, 3, 4, 5`. -/
theorem erdos1058 (n : ℕ) :
    IsSolution n ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 :=
  erdos1058_classification_of_large_certificates
    largePrimeBound largeCubicCertificate n

end Erdos1058
