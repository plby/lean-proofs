/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

open SimpleGraph Filter
open scoped NNReal

namespace Erdos750

/-- Every nonnegative error function tending to infinity permits a graph of infinite
chromatic number whose finite vertex sets have almost-half independent subsets. -/
theorem erdos_750 :
    ∀ (f : ℕ → ℝ≥0), Tendsto f atTop atTop →
      ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ (m : ℝ≥0) / 2 - f m ≤ (I.ncard : ℝ≥0) := by
  sorry

end Erdos750
