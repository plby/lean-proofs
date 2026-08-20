import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos534

def interval (N : ℕ) : Finset ℕ := Finset.Icc 1 N

end Erdos534

namespace Erdos534

def Admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ interval N ∧
    N ∈ A ∧
    Set.Pairwise (A : Set ℕ) (fun a b ↦ 1 < Nat.gcd a b)

end Erdos534

namespace Erdos534

def primePrefix (N q : ℕ) : Finset ℕ :=
  N.primeFactors.filter (· ≤ q)

end Erdos534

namespace Erdos534

def prefixProduct (N q : ℕ) : ℕ :=
  ∏ p ∈ primePrefix N q, p

end Erdos534

namespace Erdos534

def candidate (N q : ℕ) : Finset ℕ :=
  (interval N).filter fun m ↦
    prefixProduct N q ∣ m ∨ ∃ p ∈ primePrefix N q, 2 * p ∣ m

end Erdos534

namespace Erdos534

theorem erdos_534 (N : ℕ) (hN : 2 ≤ N) :
    ∃ q ∈ N.primeFactors,
      Admissible N (candidate N q) ∧
        ∀ A, Admissible N A → A.card ≤ (candidate N q).card := by
  sorry

end Erdos534

end
