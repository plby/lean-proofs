/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset
open scoped Pointwise

namespace Erdos38

open scoped Classical in
noncomputable def countIn (A : Set ℕ) (N : ℕ) : ℕ :=
  #{a ∈ Ioc 0 N | a ∈ A}

def hSumset : ℕ → Set ℕ → Set ℕ
  | 0, _ => {0}
  | h + 1, B => hSumset h B + B

def IsAdditiveBasis (B : Set ℕ) : Prop :=
  ∃ h : ℕ, ∀ᶠ n in Filter.atTop, n ∈ hSumset h B

def translateSet (A : Set ℕ) (b : ℕ) : Set ℕ := (· + b) '' A

noncomputable def unionTranslateCount (A : Set ℕ) (b : ℕ) (N : ℕ) : ℕ :=
  countIn (A ∪ translateSet A b) N

open scoped Classical in
theorem erdos_38 :
    ∃ (B : Set ℕ) (f : ℝ → ℝ),
      ¬IsAdditiveBasis B ∧
        (∀ α : ℝ, 0 < α → α < 1 → 0 < f α) ∧
          ∀ (A : Set ℕ),
            0 < schnirelmannDensity A →
            schnirelmannDensity A < 1 →
            ∀ (N : ℕ), 0 < N → ∃ b ∈ B,
              (schnirelmannDensity A + f (schnirelmannDensity A)) * ↑N ≤
                (unionTranslateCount A b N : ℝ) := by
  sorry

end Erdos38
