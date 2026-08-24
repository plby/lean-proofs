/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Polynomial

namespace PolynomialEgyptianSums

def imageSet (p : ℚ[X]) : Set ℚ :=
  Set.range (fun (n : ℕ) ↦ p.eval (n : ℚ) + 1 / (n : ℚ))

def IsStronglyComplete (A : Set ℚ) : Prop :=
  ∀ B : Finset ℚ,
    ∀ᶠ (m : ℕ) in Filter.atTop,
      ((m : ℕ) : ℚ) ∈ { ∑ x ∈ X, x | (X : Finset ℚ) (_ : (↑X : Set ℚ) ⊆ A \ ↑B) }
end PolynomialEgyptianSums

namespace Erdos351

def imageSet (P : ℚ[X]) : Set ℚ := PolynomialEgyptianSums.imageSet P

def HasCompleteImage (P : ℚ[X]) : Prop :=
  PolynomialEgyptianSums.IsStronglyComplete (imageSet P)

theorem erdos_351 :
    ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff →
      HasCompleteImage P := by
  sorry

end Erdos351
