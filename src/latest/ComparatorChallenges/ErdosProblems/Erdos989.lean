/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.Ring

namespace Erdos989

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def IsAdmissible (A : Set Plane) : Prop :=
  A.Infinite ∧ ∀ K : Set Plane, IsCompact K → (A ∩ K).Finite

noncomputable def diskCount (A : Set Plane) (x : Plane) (r : ℝ) : ℕ :=
  (A ∩ Metric.closedBall x r).ncard

noncomputable def diskError (A : Set Plane) (x : Plane) (r : ℝ) : ℝ :=
  |(diskCount A x r : ℝ) - Real.pi * r ^ 2|

theorem erdos_989_quantifier_counterexample :
    ∃ P : ℕ → ℕ → Prop,
      (∀ scale : ℕ, ∃ witness : ℕ, P witness scale) ∧
        ¬ ∃ witness : ℕ, ∀ scale : ℕ, P witness scale := by
  sorry

theorem erdos_989 :
    (∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, ∀ r ≥ R, ∃ A : Set Erdos989.Plane,
      Erdos989.IsAdmissible A ∧ ∀ x : Erdos989.Plane,
        Erdos989.diskError A x r ≤ C * Real.sqrt (r * Real.log r)) ∧ (∃ P : ℕ → ℕ → Prop,
      (∀ scale : ℕ, ∃ witness : ℕ, P witness scale) ∧
        ¬ ∃ witness : ℕ, ∀ scale : ℕ, P witness scale) := by
  sorry

end Erdos989
