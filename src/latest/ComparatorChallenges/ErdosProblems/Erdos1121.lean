/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1121

structure Circle2D where
  center : EuclideanSpace ℝ (Fin 2)
  radius : ℝ
  radius_pos : 0 < radius

structure Line2D where
  point : EuclideanSpace ℝ (Fin 2)
  direction : EuclideanSpace ℝ (Fin 2)
  direction_unit : ‖direction‖ = 1

noncomputable def perp2D (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-(v 1), v 0]

noncomputable def Line2D.signedDist (L : Line2D) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  inner ℝ (perp2D L.direction) (x - L.point)

def Circle2D.disjointFromLine (C : Circle2D) (L : Line2D) : Prop :=
  |L.signedDist C.center| > C.radius

def Line2D.onDifferentSides (L : Line2D) (x y : EuclideanSpace ℝ (Fin 2)) : Prop :=
  (L.signedDist x > 0 ∧ L.signedDist y < 0) ∨
  (L.signedDist x < 0 ∧ L.signedDist y > 0)

def Circle2D.onDifferentSidesOfLine (C₁ C₂ : Circle2D) (L : Line2D) : Prop :=
  L.onDifferentSides C₁.center C₂.center

def CirclesNonseparable {n : ℕ} (circles : Fin n → Circle2D) : Prop :=
  ∀ L : Line2D, (∀ i, (circles i).disjointFromLine L) →
    ¬∃ i j, (circles i).onDifferentSidesOfLine (circles j) L

theorem erdos_1121 {n : ℕ} (circles : Fin n → Circle2D)
    (hns : CirclesNonseparable circles) :
    ∃ T : EuclideanSpace ℝ (Fin 2),
      ∀ i, Metric.closedBall (circles i).center (circles i).radius ⊆
        Metric.closedBall T (∑ j, (circles j).radius) := by
  sorry
end Erdos1121
