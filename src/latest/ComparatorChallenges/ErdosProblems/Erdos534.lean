/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

noncomputable section

namespace Erdos534

open scoped Classical in
def interval (N : ℕ) : Finset ℕ := Finset.Icc 1 N

end Erdos534

namespace Erdos534

open scoped Classical in
def Admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ interval N ∧
    N ∈ A ∧
    Set.Pairwise (A : Set ℕ) (fun a b ↦ 1 < Nat.gcd a b)

end Erdos534

namespace Erdos534

open scoped Classical in
def primePrefix (N q : ℕ) : Finset ℕ :=
  N.primeFactors.filter (· ≤ q)

end Erdos534

namespace Erdos534

open scoped Classical in
def prefixProduct (N q : ℕ) : ℕ :=
  ∏ p ∈ primePrefix N q, p

end Erdos534

namespace Erdos534

open scoped Classical in
def candidate (N q : ℕ) : Finset ℕ :=
  (interval N).filter fun m ↦
    prefixProduct N q ∣ m ∨ ∃ p ∈ primePrefix N q, 2 * p ∣ m

end Erdos534

namespace Erdos534

open scoped Classical in
theorem erdos_534 (N : ℕ) (hN : 2 ≤ N) :
    ∃ q ∈ N.primeFactors,
      Admissible N (candidate N q) ∧
        ∀ A, Admissible N A → A.card ≤ (candidate N q).card := by
  sorry

end Erdos534

end
