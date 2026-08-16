import Mathlib

namespace PolynomialEgyptianSums
open Polynomial Filter

def imageSet (p : ℚ[X]) : Set ℚ :=
  Set.range (fun (n : ℕ) ↦ p.eval (n : ℚ) + 1 / (n : ℚ))

def IsStronglyComplete (A : Set ℚ) : Prop :=
  ∀ B : Finset ℚ,
    ∀ᶠ (m : ℕ) in Filter.atTop,
      ((m : ℕ) : ℚ) ∈ { ∑ x ∈ X, x | (X : Finset ℚ) (_ : (↑X : Set ℚ) ⊆ A \ ↑B) }
end PolynomialEgyptianSums

namespace Erdos351

open Polynomial

def imageSet (P : ℚ[X]) : Set ℚ := PolynomialEgyptianSums.imageSet P

def HasCompleteImage (P : ℚ[X]) : Prop :=
  PolynomialEgyptianSums.IsStronglyComplete (imageSet P)
end Erdos351

attribute [local instance] Classical.propDecidable

open Polynomial

namespace Erdos351

theorem erdos_351 :
    True ↔ ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff →
      HasCompleteImage P := by
  sorry

end Erdos351
