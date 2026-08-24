/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Topology

namespace Erdos1000

def phiA (n : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 (n k)).filter (fun m =>
      ∀ j ∈ Finset.range k, n k / Nat.gcd m (n k) ≠ n j)).card

noncomputable def cesaroPhi (n : ℕ → ℕ) (N : ℕ) : ℝ :=
  ((N : ℝ)⁻¹) *
    ∑ k ∈ Finset.range N, (phiA n k : ℝ) / (n k : ℝ)

theorem erdos_1000 :
  ∃ n : ℕ → ℕ,
    StrictMono n ∧
    (∀ k, 0 < n k) ∧
    Tendsto (cesaroPhi n) atTop (𝓝 (0 : ℝ)) := by
  sorry

end Erdos1000
