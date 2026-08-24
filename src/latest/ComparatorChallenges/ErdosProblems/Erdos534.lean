/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos534

def interval (N : ℕ) : Finset ℕ := Finset.Icc 1 N

def Admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ interval N ∧
    N ∈ A ∧
    Set.Pairwise (A : Set ℕ) (fun a b ↦ 1 < Nat.gcd a b)

def primePrefix (N q : ℕ) : Finset ℕ :=
  N.primeFactors.filter (· ≤ q)

def prefixProduct (N q : ℕ) : ℕ :=
  ∏ p ∈ primePrefix N q, p

def candidate (N q : ℕ) : Finset ℕ :=
  (interval N).filter fun m ↦
    prefixProduct N q ∣ m ∨ ∃ p ∈ primePrefix N q, 2 * p ∣ m

theorem erdos_534 (N : ℕ) (hN : 2 ≤ N) :
    ∃ q ∈ N.primeFactors,
      Admissible N (candidate N q) ∧
        ∀ A, Admissible N A → A.card ≤ (candidate N q).card := by
  sorry

end Erdos534
