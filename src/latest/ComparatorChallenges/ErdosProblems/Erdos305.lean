/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Real
open scoped Topology

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos305

def HasBoundedExpansion (a b B : ℕ) : Prop :=
  ∃ E : Finset ℕ,
    0 ∉ E ∧
    (∀ n ∈ E, n ≤ B) ∧
    UnitFractions.rec_sum E = (a : ℚ) / b

noncomputable def D (a b : ℕ) : ℕ :=
  sInf {B : ℕ | HasBoundedExpansion a b B}

noncomputable def Dmax (b : ℕ) : ℕ :=
  (Finset.Ico 1 b).sup fun a ↦ D a b

theorem erdos_305 :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ b : ℕ in atTop,
          (Dmax b : ℝ) ≤ C * b * (log b) ^ (1 + δ b) := by
  sorry

end Erdos305
