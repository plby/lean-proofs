/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 730.
https://www.erdosproblems.com/forum/thread/730

Informal authors:
- Liam Price
- Tomodovodoo
- Will Blair
- GPT Pro

Formal authors:
- Will Blair
- Codex
- Claude Code

URLs:
- https://www.erdosproblems.com/forum/thread/730/proof-claims#proof-claim-58
- https://github.com/williamjblair/lean-proofs/tree/03729c9cbb0b602f5a828bb850c85e84c5a6d460/ErdosProblems/Erdos730
- https://github.com/williamjblair/lean-proofs/tree/5d10b4d91f257cfbe8c563cf927f543a868845e0/ErdosProblems/Erdos730
- https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-22-000001&version=1
-/
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
