import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Pollack17

/-- The analytic cutoff `m^(1/4 + ε)` appearing in Theorem 1.3. -/
noncomputable def residuePrimeUpperBound (m : ℕ) (ε : ℝ) : ℝ :=
  Real.rpow (m : ℝ) ((1 / 4 : ℝ) + ε)

/--
The finite set of primes `ℓ` with `ℓ ≤ m^(1/4 + ε)` and `χ(ℓ) = 1`.

This definition does **not** assume `χ` is quadratic; the quadraticity hypothesis
belongs only to `theorem_1_3`, matching the statement of the paper.
-/
noncomputable def residuePrimesUpTo (m : ℕ) (χ : DirichletCharacter ℂ m) (ε : ℝ) : Finset ℕ := by
  classical
  exact
    ((Finset.range (Nat.ceil (residuePrimeUpperBound m ε) + 1)).filter fun ℓ =>
      Nat.Prime ℓ ∧
      (ℓ : ℝ) ≤ residuePrimeUpperBound m ε ∧
      χ (ℓ : ZMod m) = (1 : ℂ))

end Pollack17
