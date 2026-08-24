/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1187

/-- A positive-step arithmetic progression of natural primes, regarded as
integers by the coloring, is monochromatic. -/
def HasMonochromaticPrimeAP {κ : Type*} (color : ℤ → κ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧
    (∀ j : ℕ, j < k → Nat.Prime (a + d * j)) ∧
    ∃ gamma : κ, ∀ j : ℕ, j < k → color ((a + d * j : ℕ) : ℤ) = gamma

/-- An integer arithmetic progression with positive prime common difference
is monochromatic. -/
def HasMonochromaticAPWithPrimeStep {κ : Type*}
    (color : ℤ → κ) (k : ℕ) : Prop :=
  ∃ a : ℤ, ∃ p : ℕ, Nat.Prime p ∧
    ∃ gamma : κ, ∀ j : ℕ, j < k →
      color (a + ((p * j : ℕ) : ℤ)) = gamma

/-- The first question at one fixed requested length, literally quantified
over all finite color types and all colorings of the integers. -/
def FirstQuestionAt (k : ℕ) : Prop :=
  ∀ (κ : Type) [Finite κ], ∀ color : ℤ → κ,
    HasMonochromaticPrimeAP color k

/-- The second question at one fixed requested length. -/
def SecondQuestionAt (k : ℕ) : Prop :=
  ∀ (κ : Type) [Finite κ], ∀ color : ℤ → κ,
    HasMonochromaticAPWithPrimeStep color k

theorem erdos_1187 :
    (∀ k : ℕ, 3 ≤ k → Erdos1187.FirstQuestionAt k) ∧ ∀ k : ℕ, 3 ≤ k → ¬ SecondQuestionAt k := by
  sorry

end Erdos1187
