import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators

namespace Erdos1121

structure Circle2D where
  center : EuclideanSpace ℝ (Fin 2)
  radius : ℝ
  radius_pos : 0 < radius

def CirclesNonseparable {n : ℕ} (_circles : Fin n → Circle2D) : Prop := by
  sorry

theorem erdos_1121 {n : ℕ} (circles : Fin n → Circle2D)
    (hns : CirclesNonseparable circles) :
    ∃ T : EuclideanSpace ℝ (Fin 2),
      ∀ i, Metric.closedBall (circles i).center (circles i).radius ⊆
        Metric.closedBall T (∑ j, (circles j).radius) := by
  sorry

end Erdos1121
