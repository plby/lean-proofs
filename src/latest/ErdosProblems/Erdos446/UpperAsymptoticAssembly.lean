/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.LowerBound

/-!
# Erdős Problem 446: assembly of the sharp upper bound

This file isolates the short final passage needed after Ford's analytic
upper estimate has been proved.  The analytic estimate naturally controls
finite prefix counts, while the statement of the problem concerns the exact
periodic density `epsilon`.  The first theorem passes a uniform prefix-count
upper bound to that density.  The remaining theorems combine the resulting
upper `O` estimate with the already proved lower half and transfer the
half-open estimate to the literal open interval.

Keeping this passage separate makes the remaining analytic obligation
precise: it is enough to prove `DyadicPrefixUpperBound C Y` for some positive
absolute constant `C` and some cutoff `Y`.
-/

namespace Erdos446

open Filter Real Asymptotics
open scoped Topology

/-- The natural output of the prime-block/order-statistics calculation before
the selected depth is converted to logarithms. -/
noncomputable def fordUpperDensityModel (M y : ℕ) : ℝ :=
  fordCombinatorialWeight (fordScaleDepth M y) /
    Real.log (y : ℝ) ^ 2

theorem fordUpperDensityModel_nonneg (M y : ℕ) :
    0 ≤ fordUpperDensityModel M y := by
  dsimp [fordUpperDensityModel, fordCombinatorialWeight]
  positivity

/-- The depth-indexed upper model has exactly Ford's sharp order. -/
theorem fordUpperDensityModel_isTheta_growth446 (M : ℕ) :
    fordUpperDensityModel M =Θ[atTop] growth446 := by
  have hcoeff := fordCombinatorialWeight_depth_isTheta_depthModel M
  have hinv :
      (fun y : ℕ ↦ (Real.log (y : ℝ) ^ 2)⁻¹) =Θ[atTop]
        (fun y : ℕ ↦ (Real.log (y : ℝ) ^ 2)⁻¹) :=
    isTheta_refl
      (fun y : ℕ ↦ (Real.log (y : ℝ) ^ 2)⁻¹) atTop
  have hproduct := hcoeff.mul hinv
  have hleft : fordUpperDensityModel M =ᶠ[atTop]
      fun y : ℕ ↦
        fordCombinatorialWeight (fordScaleDepth M y) *
          (Real.log (y : ℝ) ^ 2)⁻¹ :=
    Eventually.of_forall fun y ↦ by
      dsimp [fordUpperDensityModel]
      rw [div_eq_mul_inv]
  have hright : (fun y : ℕ ↦
      fordDepthModel M y * (Real.log (y : ℝ) ^ 2)⁻¹) =ᶠ[atTop]
        fordDepthDensityModel M :=
    Eventually.of_forall fun y ↦ by
      dsimp [fordDepthDensityModel]
      rw [div_eq_mul_inv]
  exact hleft.isTheta.trans
    (hproduct.trans (hright.isTheta.trans
      (fordDepthDensityModel_isTheta_growth446 M)))

/-- A direct asymptotic upper comparison with the depth model is enough for
the final theorem. -/
theorem delta_isTheta_growth446_of_upperModel (M : ℕ)
    (hupper : (fun y : ℕ ↦ epsilon y (2 * y)) =O[atTop]
      fordUpperDensityModel M) :
    delta =Θ[atTop] growth446 :=
  delta_isTheta_growth446_of_epsilon
    ⟨hupper.trans (fordUpperDensityModel_isTheta_growth446 M).1,
      growth446_isBigO_epsilon⟩

/-- The upper half of Ford's uniform finite dyadic estimate. -/
def DyadicPrefixUpperBound (C : ℝ) (Y : ℕ) : Prop :=
  ∀ y : ℕ, Y ≤ y → ∀ X : ℕ, y * y ≤ X →
    (divisorPrefixCount X y (2 * y) : ℝ) ≤
      C * (X : ℝ) * growth446 y

/-- A uniform upper estimate for finite prefixes passes to the exact natural
density. -/
theorem epsilon_upper_of_dyadicPrefixUpperBound
    {C : ℝ} {Y : ℕ} (hY : 1 ≤ Y)
    (h : DyadicPrefixUpperBound C Y) :
    ∀ y : ℕ, Y ≤ y → epsilon y (2 * y) ≤ C * growth446 y := by
  intro y hy
  have hypos : 0 < y := lt_of_lt_of_le Nat.zero_lt_one (hY.trans hy)
  have htend := tendsto_divisorPrefixCount_div y (2 * y) hypos
  apply le_of_tendsto htend
  filter_upwards [eventually_ge_atTop (y * y), eventually_gt_atTop 0]
    with X hX hXpos
  have hcount := h y hy X hX
  have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
  apply (div_le_iff₀ hXR).2
  nlinarith

/-- The density upper estimate, in the asymptotic notation used by the final
theorem. -/
theorem epsilon_isBigO_growth446_of_dyadicPrefixUpperBound
    {C : ℝ} {Y : ℕ} (hY : 1 ≤ Y)
    (h : DyadicPrefixUpperBound C Y) :
    (fun y : ℕ ↦ epsilon y (2 * y)) =O[atTop] growth446 := by
  have hupper := epsilon_upper_of_dyadicPrefixUpperBound hY h
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop Y, eventually_growthDenominator446_pos]
    with y hy hden
  have heps : 0 ≤ epsilon y (2 * y) := epsilon_nonneg _ _
  have hgrowth : 0 < growth446 y := inv_pos.mpr hden
  simpa only [Real.norm_eq_abs, abs_of_nonneg heps, abs_of_pos hgrowth]
    using hupper y hy

/-- Once the analytic upper half is available, it combines directly with the
proved lower half to give Ford's sharp half-open estimate. -/
theorem epsilon_isTheta_growth446_of_upper
    (hupper : (fun y : ℕ ↦ epsilon y (2 * y)) =O[atTop] growth446) :
    (fun y : ℕ ↦ epsilon y (2 * y)) =Θ[atTop] growth446 :=
  ⟨hupper, growth446_isBigO_epsilon⟩

/-- The sharp estimate for the literal interval `(n,2n)` follows from any
proof of the half-open upper half. -/
theorem delta_isTheta_growth446_of_upper
    (hupper : (fun y : ℕ ↦ epsilon y (2 * y)) =O[atTop] growth446) :
    delta =Θ[atTop] growth446 :=
  delta_isTheta_growth446_of_epsilon
    (epsilon_isTheta_growth446_of_upper hupper)

/-- Fully assembled final growth theorem from Ford's uniform finite upper
bound. -/
theorem delta_isTheta_growth446_of_dyadicPrefixUpperBound
    {C : ℝ} {Y : ℕ} (hY : 1 ≤ Y)
    (h : DyadicPrefixUpperBound C Y) :
    delta =Θ[atTop] growth446 :=
  delta_isTheta_growth446_of_upper
    (epsilon_isBigO_growth446_of_dyadicPrefixUpperBound hY h)

end Erdos446
