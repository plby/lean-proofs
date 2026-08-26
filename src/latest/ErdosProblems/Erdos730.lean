import ErdosProblems.Erdos730.Proof

/-!
Will Blair's formalized proof claim for Erdős Problem 730, developed with Codex
and Claude Code. Source versions and attribution are in Erdos730/README.md.
-/

namespace Erdos730

/-- Infinitely many consecutive central binomial coefficients have equal prime support. -/
theorem erdos_730_consecutive :
    {n : ℕ | n.centralBinom.primeFactors = (n + 1).centralBinom.primeFactors}.Infinite := by
  have hgood := FullDensityReduction.goodParameters_infinite_of_candidatePositiveDensity
    FullDensityTheorem.candidatePositiveDensity
  have himage : (FullDensityCore.n '' FullDensityCore.GoodParameters).Infinite :=
    hgood.image (fun _ _ _ _ h => FullDensityCore.n_strictMono.injective h)
  apply himage.mono
  rintro _ ⟨x, hx, rfl⟩
  exact hx.2

/-- There are infinitely many distinct pairs with identical prime divisors. -/
theorem erdos_730 :
    {z : ℕ × ℕ | z.1 < z.2 ∧
      z.1.centralBinom.primeFactors = z.2.centralBinom.primeFactors}.Infinite := by
  exact FullDensityTheorem.pairSet_infinite

end Erdos730

#print axioms Erdos730.erdos_730_consecutive
#print axioms Erdos730.erdos_730
