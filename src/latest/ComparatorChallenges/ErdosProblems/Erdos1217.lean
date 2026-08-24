/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1217

noncomputable def positiveBelow (x : ℝ) : Finset ℕ :=
  Finset.Ico 1 ⌈x⌉₊

noncomputable def harmonicMass (A : Set ℕ) (x : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ (positiveBelow x).filter (fun n ↦ n ∈ A), (n : ℝ)⁻¹

noncomputable def lowerLogDensityTerm (A : Set ℕ) (x : ℝ) : ENNReal :=
  ENNReal.ofReal (harmonicMass A x / Real.log x)

noncomputable def lowerLogDensity (A : Set ℕ) : ENNReal :=
  Filter.liminf (lowerLogDensityTerm A) Filter.atTop

noncomputable def doublyHarmonicWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then ((n : ℝ) * Real.log n)⁻¹ else 0

noncomputable def weightedMass (A : Set ℕ) (x : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ (positiveBelow x).filter (fun n ↦ n ∈ A), doublyHarmonicWeight n

noncomputable def weightedTerm (A : Set ℕ) (x : ℝ) : ENNReal :=
  ENNReal.ofReal (weightedMass A x / Real.log (Real.log x))

noncomputable def weightedRate (A : Set ℕ) : ENNReal :=
  Filter.limsup (weightedTerm A) Filter.atTop

noncomputable def chainCount (c : ℕ → ℕ) (x : ℝ) : ℕ := by
  classical
  exact ((positiveBelow x).filter (fun n ↦ n ∈ Set.range c)).card

noncomputable def chainTerm (c : ℕ → ℕ) (x : ℝ) : ENNReal :=
  ENNReal.ofReal ((chainCount c x : ℝ) / Real.log (Real.log x))

noncomputable def chainRate (c : ℕ → ℕ) : ENNReal :=
  Filter.limsup (chainTerm c) Filter.atTop

theorem erdos_1217 :
      ∀ (a : ℕ → ℕ), StrictMono a → (∀ i, 0 < a i) →
        0 < lowerLogDensity (Set.range a) →
        ∃ n : ℕ → ℕ, StrictMono n ∧
          (∀ i, a (n i) ∣ a (n (i + 1))) ∧
          weightedRate (Set.range a) ≤ chainRate (a ∘ n) := by
  sorry

end Erdos1217
