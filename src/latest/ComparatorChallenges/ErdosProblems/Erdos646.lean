import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Data.Real.Basic

namespace Erdos646

set_option linter.style.longLine false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

def partial_sum (k : ℕ) (p : Fin k → ℕ) (n : ℕ) : Fin k → ZMod 2 :=
  fun i => padicValNat (p i) (Nat.factorial n)
end Erdos646

attribute [local instance] Classical.propDecidable

theorem Erdos646.infinitely_many_even_factorial_exponents :
    ∀ (k : Nat) (p : Fin k → Nat),
      (∀ (i : Fin k), Nat.Prime (p i)) →
        @Function.Injective.{1, 1} (Fin k) Nat p →
          @Set.Infinite.{0} Nat
            (@setOf.{0} Nat fun (n : Nat) ↦
              ∀ (i : Fin k),
                @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Erdos646.partial_sum k p n i)
                  (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (nat_lit 0)
                    (@Zero.toOfNat0.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@MulZeroClass.toZero.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@instMulZeroClassOfSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@DivisionSemiring.toSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Semifield.toDivisionSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Field.toSemifield.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@ZMod.instField
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  Nat.fact_prime_two)))))))))
  := by
  sorry
