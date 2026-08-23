/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos484

open Finset

open Finset

noncomputable def monochromaticSumSet (N : ℕ) (k : ℕ) (f : ℕ → Fin k) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun n =>
    ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N, a ≠ b ∧ f a = f b ∧ a + b = n)
end Erdos484

open Finset

namespace Erdos484

open scoped Classical in
theorem monochromatic_sums_linear :
    ∃ c : ℝ, c > 0 ∧
      ∀ k : ℕ, k ≥ 1 →
        ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
          ∀ f : ℕ → Fin k,
            (monochromaticSumSet N k f).card ≥ ⌊c * (N : ℝ)⌋₊ := by
  sorry

end Erdos484
