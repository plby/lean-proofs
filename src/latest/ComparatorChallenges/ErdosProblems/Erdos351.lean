import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Order.Filter.AtTopBot.Defs

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

theorem Erdos351.erdos_351 :
    Iff True
      (∀ (P : @Polynomial.{0} Rat Rat.semiring),
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Polynomial.natDegree.{0} Rat Rat.semiring P) →
          @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
              (@Polynomial.leadingCoeff.{0} Rat Rat.semiring P) →
            Erdos351.HasCompleteImage P)
  := by
  sorry
