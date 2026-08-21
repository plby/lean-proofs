import Mathlib

namespace Erdos471

/-- Three natural numbers are pairwise distinct. -/
def PairwiseDistinct3 (a b c : ℕ) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c

instance (a b c : ℕ) : Decidable (PairwiseDistinct3 a b c) := by
  unfold PairwiseDistinct3
  infer_instance

/-- The sums of ordered triples of distinct elements of `Q`. -/
def tripleSums (Q : Finset ℕ) : Finset ℕ :=
  ((((Q ×ˢ Q) ×ˢ Q).filter fun t : (ℕ × ℕ) × ℕ ↦
      PairwiseDistinct3 t.1.1 t.1.2 t.2).image fun t ↦
        t.1.1 + t.1.2 + t.2)

/-- The prime-valued sums of three distinct elements of `Q`. -/
def newPrimes (Q : Finset ℕ) : Finset ℕ :=
  (tripleSums Q).filter Nat.Prime

/-- One step of the prime-closure process. -/
def step (Q : Finset ℕ) : Finset ℕ :=
  Q ∪ newPrimes Q

/-- The successive generations, starting from the initial prime set. -/
def generation (Q : Finset ℕ) : ℕ → Finset ℕ
  | 0 => Q
  | i + 1 => step (generation Q i)

/-- Every member of the finite set is prime. -/
def IsPrimeFinset (Q : Finset ℕ) : Prop :=
  ∀ p ∈ Q, Nat.Prime p

/-- The cardinalities of successive generations are unbounded. -/
def HasUnboundedGenerations (Q : Finset ℕ) : Prop :=
  ∀ k : ℕ, ∃ i : ℕ, k ≤ (generation Q i).card

/-- Some finite set of primes generates arbitrarily large generations. -/
theorem erdos471 :
    ∃ Q : Finset ℕ, IsPrimeFinset Q ∧ HasUnboundedGenerations Q := by
  sorry

end Erdos471
