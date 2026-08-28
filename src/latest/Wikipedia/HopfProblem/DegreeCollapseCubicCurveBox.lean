import Wikipedia.HopfProblem.DegreeCollapseCubicFlowCylinder

/-!
# Cubic trajectories stay in an axis-centered box between their endpoints

The longitudinal coordinate is monotone and each transverse coordinate
has monotone absolute value. In the actual max-norm model, two endpoints
in an axis-centered closed ball therefore keep the whole intervening
trajectory inside that same ball. This supplies actual endpoint-chart
domain control for native ODE comparison.
-/

noncomputable section

open Set Function Metric
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ}

theorem monotone_cubicAxisParameter {a : ℝ} (ha : 0 < a) : Monotone (cubicAxisParameter a) := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left
    (strictMono_tanh.monotone (mul_le_mul_of_nonneg_left hst ha.le)) ha.le

/-- Every transverse norm is bounded by the larger endpoint transverse norm. -/
theorem cubicFlowCylinder_transverse_norm_le_max (σ : Fin m → ℝ) (a : ℝ) (z : Fin m → ℝ)
    {s t u : ℝ} (ht : t ∈ Icc s u) :
    ‖(cubicFlowCylinder σ a (z, t)).2‖ ≤
      max ‖(cubicFlowCylinder σ a (z, s)).2‖ ‖(cubicFlowCylinder σ a (z, u)).2‖ := by
  let Z (r : ℝ) : Fin m → ℝ := (cubicFlowCylinder σ a (z, r)).2
  have hcoord (r : ℝ) (i : Fin m) : ‖Z r i‖ = Real.exp (-σ i * r) * ‖z i‖ := by
    change ‖Real.exp (-σ i * r) * z i‖ = _
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg (Z s)))).mpr
  intro i
  change ‖Z t i‖ ≤ max ‖Z s‖ ‖Z u‖
  by_cases hi : 0 ≤ σ i
  · calc
      ‖Z t i‖ = Real.exp (-σ i * t) * ‖z i‖ := hcoord t i
      _ ≤ Real.exp (-σ i * s) * ‖z i‖ :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.mpr hi))) (norm_nonneg _)
      _ = ‖Z s i‖ := (hcoord s i).symm
      _ ≤ ‖Z s‖ := norm_le_pi_norm (Z s) i
      _ ≤ max ‖Z s‖ ‖Z u‖ := le_max_left _ _
  · calc
      ‖Z t i‖ = Real.exp (-σ i * t) * ‖z i‖ := hcoord t i
      _ ≤ Real.exp (-σ i * u) * ‖z i‖ :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (neg_nonneg.mpr (le_of_not_ge hi))))
          (norm_nonneg _)
      _ = ‖Z u i‖ := (hcoord u i).symm
      _ ≤ ‖Z u‖ := norm_le_pi_norm (Z u) i
      _ ≤ max ‖Z s‖ ‖Z u‖ := le_max_right _ _

/-- The whole actual cubic trajectory segment stays in the same axis-centered max-norm ball. -/
theorem cubicFlowCylinder_stays_axis_ball (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (z : Fin m → ℝ) {s t u c r : ℝ} (ht : t ∈ Icc s u)
    (hs : cubicFlowCylinder σ a (z, s) ∈ closedBall (c, (0 : Fin m → ℝ)) r)
    (hu : cubicFlowCylinder σ a (z, u) ∈ closedBall (c, (0 : Fin m → ℝ)) r) :
    cubicFlowCylinder σ a (z, t) ∈ closedBall (c, (0 : Fin m → ℝ)) r := by
  have hs' : |cubicAxisParameter a s - c| ≤ r ∧ ‖(cubicFlowCylinder σ a (z, s)).2‖ ≤ r := by
    simpa only [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right,
      cubicFlowCylinder] using hs
  have hu' : |cubicAxisParameter a u - c| ≤ r ∧ ‖(cubicFlowCylinder σ a (z, u)).2‖ ≤ r := by
    simpa only [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right,
      cubicFlowCylinder] using hu
  rw [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right]
  constructor
  · change |cubicAxisParameter a t - c| ≤ r
    apply abs_le.mpr
    have hst := monotone_cubicAxisParameter ha ht.1
    have htu := monotone_cubicAxisParameter ha ht.2
    constructor <;> linarith [(abs_le.mp hs'.1).1, (abs_le.mp hu'.1).2]
  · exact (cubicFlowCylinder_transverse_norm_le_max σ a z ht).trans (max_le hs'.2 hu'.2)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
