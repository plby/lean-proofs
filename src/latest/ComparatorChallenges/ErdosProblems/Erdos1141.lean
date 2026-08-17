import Mathlib
namespace Erdos1141

open scoped BigOperators
open Finset Real

def Pa (a n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → Nat.Coprime k n → a * k ^ 2 < n → Nat.Prime (n - a * k ^ 2)
open Nat Set

def Erdos1141Prop (n : ℕ) : Prop :=
  ∀ k, k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime
end Erdos1141

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open Finset Real
open Nat Set

namespace Erdos1141

theorem erdos_1141_variant : Set.Finite {n : ℕ | Pa 1 n} := by
  sorry


theorem erdos_1141 :
    ¬ Infinite { n | Erdos1141Prop n } := by
  sorry

end Erdos1141
