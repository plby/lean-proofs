import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace UnitFractions

open scoped BigOperators
open Filter Real Finset Nat
open _root_.Finset

noncomputable section
attribute [local instance] Classical.propDecidable

section

variable (A : Set ℕ)

def partial_density (N : ℕ) : ℝ := ((range N).filter fun n ↦ n ∈ A).card / N
def upper_density : ℝ := limsup (partial_density A) atTop
def lower_density : ℝ := liminf (partial_density A) atTop
def has_density (d : ℝ) : Prop := upper_density A = d ∧ lower_density A = d
variable {A}

end

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n
namespace Nat

end Nat

end

end UnitFractions

attribute [local instance] Classical.propDecidable

theorem Erdos298.erdos298 :
    ∀ (A : Set.{0} Nat),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (UnitFractions.upper_density A) →
        @Exists.{1} (Finset.{0} Nat) fun (S : Finset.{0} Nat) ↦
          And
            (@LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat)
              (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat) S) A)
            (@Eq.{1} Rat (UnitFractions.rec_sum S)
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
  := by
  sorry
theorem Erdos298.erdos298_density :
    ∀ (A : Set.{0} Nat) (d : Real),
      UnitFractions.has_density A d →
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d →
          @Exists.{1} (Finset.{0} Nat) fun (S : Finset.{0} Nat) ↦
            And
              (@LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat)
                (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat) S) A)
              (@Eq.{1} Rat (UnitFractions.rec_sum S)
                (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
  := by
  sorry
