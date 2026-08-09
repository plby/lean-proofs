import Mathlib.Data.Finite.Defs
import Mathlib.Algebra.Group.Nat.Defs

namespace Erdos674

open Nat

def solutionSet : Set (ℕ × ℕ × ℕ) :=
    { (x, y, z) | 1 < x ∧ 1 < y ∧ 1 < z ∧ x ^ x * y ^ y = z ^ z }
end Erdos674

attribute [local instance] Classical.propDecidable

theorem Erdos674.erdos_674_infinite :
    @Set.Infinite.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) Erdos674.solutionSet
  := by
  sorry
