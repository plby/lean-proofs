import Mathlib

namespace Erdos964

/-
The divisor function tau(n) counts the number of divisors of n.
-/
def tau (n : ℕ) : ℕ := (Nat.divisors n).card

/-
E2(C) is the set of products of two distinct primes both greater than C.
-/
def E2 (C : ℕ) : Set ℕ :=
  { n | ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ p1 ≠ p2 ∧ C < p1 ∧ C < p2 ∧ n = p1 * p2 }

/-
L_i(x) = a_i * x + 1
-/
def L (a : ℕ) (x : ℕ) : ℕ := a * x + 1

/-
The set of ratios of consecutive values of the divisor function.
-/
def divisor_ratios : Set ℚ :=
  { q | ∃ n : ℕ, n > 0 ∧ q = (tau (n + 1) : ℚ) / (tau n : ℚ) }

/-
The statement of the Goldston-Graham-Pintz-Yildirim theorem (Corollary 2.1 in the paper).
-/
def GoldstonGrahamPintzYildirimStatement : Prop :=
  ∀ (a r : Fin 3 → ℕ),
    (∀ i, 0 < a i) → (∀ i, 0 < r i) →
    (∀ i, (r i).Coprime (a i)) →
    (∀ i j, i ≠ j → (r i).Coprime (if a i > a j then a i - a j else a j - a i)) →
    (∀ i j, i ≠ j → (r i).Coprime (r j)) →
    ∀ C : ℕ,
      ∃ i j, i < j ∧ {x : ℕ | r i ∣ L (a i) x ∧ r j ∣ L (a j) x ∧
        (L (a i) x) / r i ∈ E2 C ∧ (L (a j) x) / r j ∈ E2 C}.Infinite

/-
R is the set of values attained infinitely many times by the sequence d(n+1)/d(n).
-/
def R_set : Set ℚ := {q | {n | (tau (n + 1) : ℚ) / (tau n : ℚ) = q}.Infinite}

end Erdos964
