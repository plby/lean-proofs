/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos300

def AvoidsOne (A : Finset ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ A → UnitFractions.rec_sum B ≠ 1

noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter AvoidsOne

noncomputable def erdos300Max (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

theorem erdos_300 :
    Tendsto (fun N : ℕ => (erdos300Max N : ℝ) / (N : ℝ)) atTop
      (𝓝 (1 - 1 / Real.exp 1)) := by
  sorry

end Erdos300
