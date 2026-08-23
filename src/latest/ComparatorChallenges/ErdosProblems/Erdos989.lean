import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.Ring

namespace Erdos989

open Filter MeasureTheory Set
open scoped ENNReal Topology

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def IsAdmissible (A : Set Plane) : Prop :=
  A.Infinite ∧ ∀ K : Set Plane, IsCompact K → (A ∩ K).Finite

noncomputable def diskCount (A : Set Plane) (x : Plane) (r : ℝ) : ℕ :=
  (A ∩ Metric.closedBall x r).ncard

noncomputable def diskError (A : Set Plane) (x : Plane) (r : ℝ) : ℝ :=
  |(diskCount A x r : ℝ) - Real.pi * r ^ 2|

def HasSqrtLogUpperConstruction : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, ∀ r ≥ R, ∃ A : Set Plane,
    IsAdmissible A ∧ ∀ x : Plane,
      diskError A x r ≤ C * Real.sqrt (r * Real.log r)

def HasFixedScaleButNoGlobalWitness : Prop :=
  ∃ P : ℕ → ℕ → Prop,
    (∀ scale : ℕ, ∃ witness : ℕ, P witness scale) ∧
      ¬ ∃ witness : ℕ, ∀ scale : ℕ, P witness scale

def SourceCorrectFixedScaleResolution : Prop :=
  HasSqrtLogUpperConstruction ∧ HasFixedScaleButNoGlobalWitness

theorem erdos_989_quantifier_counterexample :
    HasFixedScaleButNoGlobalWitness := by
  sorry

theorem erdos_989 : SourceCorrectFixedScaleResolution := by
  sorry

end Erdos989
