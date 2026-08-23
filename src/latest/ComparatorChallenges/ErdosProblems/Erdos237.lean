/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib
import ErdosProblems.Axioms

open Nat Finset Real Filter Asymptotics Topology
open scoped Pointwise
namespace Erdos237

open Nat Set Finset Real

noncomputable def repCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {a ∈ A | a ≤ n ∧ (n - a).Prime}
end Erdos237


open Nat Set Finset Real

namespace Erdos237

open scoped Classical in
theorem erdos_237 (A : Set ℕ) (hA : A.Infinite) :
    ∀ C : ℕ, ∃ n : ℕ, C < repCount A n := by
  sorry

end Erdos237
