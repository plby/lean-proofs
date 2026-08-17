import Mathlib

open Nat Finset Real Filter Asymptotics Topology
open scoped Pointwise
namespace Erdos237

open Nat Set Finset Real

noncomputable def repCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {a ∈ A | a ≤ n ∧ (n - a).Prime}
end Erdos237

attribute [local instance] Classical.propDecidable

open Nat Set Finset Real

namespace Erdos237

theorem erdos_237 (A : Set ℕ) (hA : A.Infinite) :
    ∀ C : ℕ, ∃ n : ℕ, C < repCount A n := by
  sorry

end Erdos237
