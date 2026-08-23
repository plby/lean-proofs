/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 277

Haight proved that integers with arbitrarily large abundancy can be chosen so
that their nontrivial divisors cannot be the distinct moduli of a covering
system.
-/

open scoped ArithmeticFunction.sigma BigOperators Pointwise

/-- A finite covering system over a commutative semiring. -/
structure CoveringSystem (R : Type*) [CommSemiring R] where
  ι : Type
  [fintypeIndex : Fintype ι]
  residue : ι → R
  moduli : ι → Ideal R
  unionCovers : ⋃ i, ({residue i} : Set R) + (moduli i : Set R) = Set.univ
  ne_bot : ∀ i, moduli i ≠ ⊥
  ne_top : ∀ i, moduli i ≠ ⊤

attribute [instance] CoveringSystem.fintypeIndex

/-- A covering system whose modulus ideals are pairwise distinct. -/
structure StrictCoveringSystem (R : Type*) [CommSemiring R]
    extends CoveringSystem R where
  injective_moduli : moduli.Injective

namespace Erdos277

noncomputable section

open MeasureTheory ProbabilityTheory Set


open scoped Classical in
theorem erdos_277 :
    ∀ c : ℝ, ∃ n : ℕ, (σ 1 n : ℝ) > c * n ∧
      ∀ (m : StrictCoveringSystem ℤ), ∃ i, (n : ℤ) ∉ m.moduli i := by
  sorry
