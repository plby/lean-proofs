import ErdosProblems.Erdos746.Model
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Parameters and exact statement for Erdős 746

All logarithms are natural.  The edge-count sample space is the exact uniform
fixed-size model from `Model.lean`; the eventual upper bound below is precisely
the condition that this sample space is nonempty.
-/

open Filter

namespace Erdos746

/-- The integer edge threshold `(1/2 + ε) n log n`, rounded upward. -/
noncomputable def edgeThreshold (ε : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil ((1 / 2 + ε) * (n : ℝ) * Real.log (n : ℝ))

/-- The lower-density prefix used before the random-edge sprinkling. -/
noncomputable def baseEdgeThreshold (ρ : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil ((1 / 2 + ρ / 2) * (n : ℝ) * Real.log (n : ℝ))

/-- Number of additional random edges exposed between the two thresholds. -/
noncomputable def sprinklingLength (ε ρ : ℝ) (n : ℕ) : ℕ :=
  edgeThreshold ε n - baseEdgeThreshold ρ n

theorem edgeThreshold_le_of_real_le {ε : ℝ} {n m : ℕ}
    (h : (1 / 2 + ε) * (n : ℝ) * Real.log (n : ℝ) ≤ (m : ℝ)) :
    edgeThreshold ε n ≤ m := by
  exact Nat.ceil_le.mpr h

theorem real_le_edgeThreshold (ε : ℝ) (n : ℕ) :
    (1 / 2 + ε) * (n : ℝ) * Real.log (n : ℝ) ≤
      (edgeThreshold ε n : ℝ) := by
  exact Nat.le_ceil _

/-- Exact sequence formulation of Erdős Problem 746 in the uniform `G(n,m)`
model.  It asserts the result for every eventually admissible edge-count
sequence, and hence includes every fixed choice above the stated threshold. -/
def Erdos746Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ m : ℕ → ℕ,
    (∀ᶠ n : ℕ in atTop,
      (1 / 2 + ε) * (n : ℝ) * Real.log (n : ℝ) ≤ (m n : ℝ)) →
    (∀ᶠ n : ℕ in atTop, m n ≤ n.choose 2) →
    Tendsto (fun n ↦ hamiltonianProbability n (m n)) atTop (nhds 1)

end Erdos746
