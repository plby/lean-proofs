import Mathlib.Data.Int.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace Erdos947

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

def IsExactCoveringSystem (l : List (ℤ × ℕ)) : Prop :=
  (∀ p ∈ l, 0 ≤ p.1 ∧ p.1 < p.2) ∧
  (∀ m : ℤ, ∃! i : Fin l.length, let (a, n) := l.get i; m ≡ a [ZMOD n])
open PowerSeries

open PowerSeries

open PowerSeries

open PowerSeries

open Polynomial

open Polynomial

end Erdos947

attribute [local instance] Classical.propDecidable

theorem Erdos947.exact_covering_system_distinct_moduli_impossible :
    ∀ (l : List.{0} (Prod.{0, 0} Int Nat)),
      Erdos947.IsExactCoveringSystem l →
        @List.Pairwise.{0} (Prod.{0, 0} Int Nat)
            (fun (p q : Prod.{0, 0} Int Nat) ↦
              @Ne.{1} Nat (@Prod.snd.{0, 0} Int Nat p) (@Prod.snd.{0, 0} Int Nat q))
            l →
          @GE.ge.{0} Nat instLENat (@List.length.{0} (Prod.{0, 0} Int Nat) l)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            False
  := by
  sorry
