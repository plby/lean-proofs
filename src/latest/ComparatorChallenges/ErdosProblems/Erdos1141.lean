/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Pollack17

noncomputable def residuePrimeUpperBound (m : ℕ) (ε : ℝ) : ℝ :=
  Real.rpow (m : ℝ) ((1 / 4 : ℝ) + ε)

noncomputable def residuePrimesUpTo
    (m : ℕ) (χ : DirichletCharacter ℂ m) (ε : ℝ) : Finset ℕ := by
  classical
  exact
    ((Finset.range (Nat.ceil (residuePrimeUpperBound m ε) + 1)).filter fun ℓ =>
      Nat.Prime ℓ ∧
      (ℓ : ℝ) ≤ residuePrimeUpperBound m ε ∧
      χ (ℓ : ZMod m) = (1 : ℂ))

axiom theorem_1_3
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ m0 : ℕ, ∀ m : ℕ,
      m > m0 →
      ∀ χ : DirichletCharacter ℂ m,
        MulChar.IsQuadratic χ →
          Real.rpow (Real.log (m : ℝ)) A ≤
            ((residuePrimesUpTo m χ ε).card : ℝ)

end Pollack17

namespace Erdos1141

open scoped BigOperators
open Finset Real

def Pa (a n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → Nat.Coprime k n → a * k ^ 2 < n → Nat.Prime (n - a * k ^ 2)
open Nat Set

def Erdos1141Prop (n : ℕ) : Prop :=
  ∀ k, k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime
end Erdos1141

open scoped BigOperators
open Finset Real
open Nat Set

namespace Erdos1141

open scoped Classical in
theorem erdos_1141_variant : Set.Finite {n : ℕ | Pa 1 n} := by
  sorry

open scoped Classical in
theorem erdos_1141 :
    ¬ Infinite { n | Erdos1141Prop n } := by
  sorry

end Erdos1141
