import Mathlib

namespace Erdos964

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxRecDepth 4000
set_option synthInstance.maxSize 128

def tau (n : ℕ) : ℕ := (Nat.divisors n).card
def E2 (C : ℕ) : Set ℕ :=
  { n | ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ p1 ≠ p2 ∧ C < p1 ∧ C < p2 ∧ n = p1 * p2 }
def L (a : ℕ) (x : ℕ) : ℕ := a * x + 1
def divisor_ratios : Set ℚ :=
  { q | ∃ n : ℕ, n > 0 ∧ q = (tau (n + 1) : ℚ) / (tau n : ℚ) }
def GoldstonGrahamPintzYildirimStatement : Prop :=
  ∀ (a r : Fin 3 → ℕ),
    (∀ i, 0 < a i) → (∀ i, 0 < r i) →
    (∀ i, (r i).Coprime (a i)) →
    (∀ i j, i ≠ j → (r i).Coprime (if a i > a j then a i - a j else a j - a i)) →
    (∀ i j, i ≠ j → (r i).Coprime (r j)) →
    ∀ C : ℕ,
      ∃ i j, i < j ∧ {x : ℕ | r i ∣ L (a i) x ∧ r j ∣ L (a j) x ∧
        (L (a i) x) / r i ∈ E2 C ∧ (L (a j) x) / r j ∈ E2 C}.Infinite
end Erdos964

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos964

theorem ErdosProblem964 (hGPY : GoldstonGrahamPintzYildirimStatement) :
  Set.Ioi (0 : ℝ) ⊆ closure (Set.image (fun q : ℚ => (q : ℝ)) divisor_ratios) := by
  sorry

end Erdos964
