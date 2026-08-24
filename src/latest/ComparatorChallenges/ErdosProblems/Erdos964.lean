/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos964

def tau (n : ℕ) : ℕ := (Nat.divisors n).card
def E2 (C : ℕ) : Set ℕ :=
  { n | ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ p1 ≠ p2 ∧ C < p1 ∧ C < p2 ∧ n = p1 * p2 }
def L (a : ℕ) (x : ℕ) : ℕ := a * x + 1
def divisor_ratios : Set ℚ :=
  { q | ∃ n : ℕ, n > 0 ∧ q = (tau (n + 1) : ℚ) / (tau n : ℚ) }

theorem erdos_964 (hGPY : (∀ (a r : Fin 3 → ℕ),
  (∀ i, 0 < a i) → (∀ i, 0 < r i) →
  (∀ i, (r i).Coprime (a i)) →
  (∀ i j, i ≠ j → (r i).Coprime (if a i > a j then a i - a j else a j - a i)) →
  (∀ i j, i ≠ j → (r i).Coprime (r j)) →
  ∀ C : ℕ,
    ∃ i j, i < j ∧ {x : ℕ | r i ∣ Erdos964.L (a i) x ∧ r j ∣ Erdos964.L (a j) x ∧
      (Erdos964.L (a i) x) / r i ∈ Erdos964.E2 C ∧ (Erdos964.L (a j) x) / r j ∈ Erdos964.E2 C}.Infinite)) :
    Set.Ioi (0 : ℝ) ⊆ closure (Set.image (fun q : ℚ => (q : ℝ)) divisor_ratios) := by
  sorry

end Erdos964
