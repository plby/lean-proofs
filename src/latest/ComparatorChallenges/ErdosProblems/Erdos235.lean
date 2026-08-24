/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Topology

namespace Erdos235

def IsInternalConsecutive (N a b : ℕ) : Prop :=
  a < b ∧ b < N ∧ a.Coprime N ∧ b.Coprime N ∧
    ∀ t, a < t → t < b → ¬t.Coprime N

noncomputable def internalShortGaps (N T : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range N).product (Finset.range N)).filter fun ab ↦
    IsInternalConsecutive N ab.1 ab.2 ∧ ab.2 - ab.1 ≤ T

noncomputable def nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

noncomputable def primeProduct (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, nthPrime i

noncomputable def normalizedThreshold (N : ℕ) (c : ℝ) : ℕ :=
  ⌊c * (N : ℝ) / (N.totient : ℝ)⌋₊

noncomputable def gapCDF (k : ℕ) (c : ℝ) : ℝ :=
  ((internalShortGaps (primeProduct k)
      (normalizedThreshold (primeProduct k) c)).card : ℝ) /
    ((primeProduct k).totient : ℝ)

theorem erdos_235 :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ c, 0 ≤ c → Tendsto (fun k ↦ gapCDF k c) atTop (𝓝 (f c)) := by
  sorry

end Erdos235
