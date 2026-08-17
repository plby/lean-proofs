/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import ErdosProblems.Erdos438.Basic
import ErdosProblems.Erdos438.Massias

/-!
# Erdős Problem 438: the final limiting argument

This file contains the order-theoretic bookkeeping which turns a convergent
family of explicit examples and the quantitative eventual upper bound into the
limit of the finite extremal function.
-/

open Filter

namespace Erdos438

/-- A squeeze lemma tailored to the form in which the two substantive halves
of the proof are used.  The lower comparison tends to `c`, while the upper
estimate is allowed to be stated with an arbitrary positive additive error. -/
theorem tendsto_of_lower_comparison_of_eventually_le_add
    {f g : ℕ → ℝ} {c : ℝ}
    (hg : Tendsto g atTop (nhds c))
    (hgf : ∀ᶠ n in atTop, g n ≤ f n)
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f n ≤ c + ε) :
    Tendsto f atTop (nhds c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hg) (ε / 2) hhalf
  obtain ⟨N₂, hN₂⟩ := (eventually_atTop.1 hgf)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 (hupper (ε / 2) hhalf)
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_right N₁ (max N₂ N₃)) hn)
  have hn₃ : N₃ ≤ n :=
    le_trans (le_max_right _ _) (le_trans (le_max_right N₁ (max N₂ N₃)) hn)
  have hclose := hN₁ n hn₁
  have hlower : c - ε / 2 < g n := by
    rw [Real.dist_eq] at hclose
    have := (abs_lt.mp hclose).1
    linarith
  have hgf' : g n ≤ f n := hN₂ n hn₂
  have hupper' : f n ≤ c + ε / 2 := hN₃ n hn₃
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- An eventual estimate for every admissible set applies in particular to the
extremizer which realizes `extremalSize`. -/
theorem eventually_extremalSize_div_le_of_eventually_all
    {C : ℝ}
    (hupper : ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, admissible N A →
      (A.card : ℝ) / (N : ℝ) ≤ C) :
    ∀ᶠ N : ℕ in atTop, (extremalSize N : ℝ) / (N : ℝ) ≤ C := by
  filter_upwards [hupper] with N hN
  obtain ⟨A, hA, hcard⟩ := exists_extremizer N
  rw [← hcard]
  exact hN A hA

/-- Abstract final assembly: any family of admissible examples whose density
tends to `c`, together with the eventual `c + ε` upper estimate for all
admissible sets, determines the limit of the extremal density. -/
theorem tendsto_extremalSize_div_of_construction_and_upper
    {construction : ℕ → Finset ℕ} {c : ℝ}
    (hconstruction : ∀ N, admissible N (construction N))
    (hlower : Tendsto
      (fun N : ℕ ↦ ((construction N).card : ℝ) / (N : ℝ)) atTop (nhds c))
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, admissible N A →
        (A.card : ℝ) / (N : ℝ) ≤ c + ε) :
    Tendsto (fun N : ℕ ↦ (extremalSize N : ℝ) / (N : ℝ)) atTop (nhds c) := by
  apply tendsto_of_lower_comparison_of_eventually_le_add hlower
  · filter_upwards with N
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast card_le_extremalSize (hconstruction N)) (Nat.cast_nonneg N)
  · intro ε hε
    exact eventually_extremalSize_div_le_of_eventually_all (hupper ε hε)

/-- The concrete final squeeze for Problem 438, parameterized only by the KLS
eventual upper bound proved in `Upper.lean`.  The lower side is the explicit
Massias construction and the extremal maximum is attained by
`exists_extremizer`. -/
theorem tendsto_extremalSize_density_of_eventually_upper
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, admissible N A →
        (A.card : ℝ) / (N : ℝ) ≤ (11 : ℝ) / 32 + ε) :
    Tendsto (fun N : ℕ ↦ (extremalSize N : ℝ) / (N : ℝ)) atTop
      (nhds ((11 : ℝ) / 32)) := by
  exact tendsto_extremalSize_div_of_construction_and_upper
    massiasSet_admissible tendsto_massiasSet_density hupper

end Erdos438
