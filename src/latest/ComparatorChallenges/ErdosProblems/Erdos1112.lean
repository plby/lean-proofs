/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Copyright 2026 Johan Land.
Licensed under the Apache License, Version 2.0.
Definitions and statements adapted for this repository. -/
import Mathlib

namespace Erdos1112

/-- Positive, strictly increasing sequences with multiplicative gaps at least `r`. -/
def IsLacunaryWith (r : ℕ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧ ∀ i, r * b i ≤ b (i + 1)

/-- Positive sequences whose consecutive gaps lie in `[d₁, d₂]`. -/
def HasGapsIn (d₁ d₂ : ℕ) (a : ℕ → ℕ) : Prop :=
  0 < a 0 ∧ ∀ i, a i + d₁ ≤ a (i + 1) ∧ a (i + 1) ≤ a i + d₂

/-- The `k`-fold sumset, allowing repeated summands. -/
def kFoldSumset (k : ℕ) (a : ℕ → ℕ) : Set ℕ :=
  { n | ∃ f : Fin k → ℕ, n = ∑ j, a (f j) }

/-- Lacunarity with an arbitrary prescribed sequence of lower ratios. -/
def IsVarLacunaryWith (R : ℕ → ℕ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧ ∀ i, R i * b i ≤ b (i + 1)

/-- Lacunarity with an integer ratio. -/
def IsLacunaryWithInt (r : ℤ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧ ∀ i, r * (b i : ℤ) ≤ (b (i + 1) : ℤ)

theorem erdos_1112_existence_bound (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁)
    (hd : d₁ < d₂) (h : k + 1 ≤ d₂) :
    ∀ b : ℕ → ℕ, IsLacunaryWith (192 * d₂) b →
      ∃ a : ℕ → ℕ, HasGapsIn d₁ d₂ a ∧ Disjoint (kFoldSumset k a) (Set.range b) := by
  sorry

theorem erdos_1112_strong_nonexistence (k d₁ d₂ : ℕ) (hk : 3 ≤ k)
    (hd₁ : 1 ≤ d₁) (h : d₂ ≤ k) (R : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, IsVarLacunaryWith R b ∧
      ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a →
        (kFoldSumset k a ∩ Set.range b).Nonempty := by
  sorry

theorem erdos_1112 (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) :
    (∃ r : ℕ, ∀ b : ℕ → ℕ, IsLacunaryWith r b →
      ∃ a : ℕ → ℕ, HasGapsIn d₁ d₂ a ∧ Disjoint (kFoldSumset k a) (Set.range b)) ↔
      k + 1 ≤ d₂ := by
  sorry

theorem erdos_1112_int (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) :
    (∃ r : ℤ, ∀ b : ℕ → ℕ, IsLacunaryWithInt r b →
      ∃ a : ℕ → ℕ, HasGapsIn d₁ d₂ a ∧ Disjoint (kFoldSumset k a) (Set.range b)) ↔
      k + 1 ≤ d₂ := by
  sorry

end Erdos1112
