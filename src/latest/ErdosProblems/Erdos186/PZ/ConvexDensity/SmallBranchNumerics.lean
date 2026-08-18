/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.BranchNumerics
import ErdosProblems.Erdos186.PZ.ConvexDensity.Definitions

/-! # Numerical closure of the small common-hull branch -/

open Filter Set
open scoped Topology

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

theorem smallBranchSaving_pos {d : ℕ} {epsilon : ℝ}
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon) :
    0 < tau epsilon * densityExponent d epsilon := by
  have halpha := alpha_nonneg (by omega : 1 ≤ d)
  change 0 < tau epsilon * (alpha d + epsilon)
  exact mul_pos (tau_pos hepsilon) (by linarith)

/-- The first dyadic logarithmic loss is absorbed by the density power at
`eta = delta ^ tau`. -/
theorem exists_deltaZero_smallBranchCard
    {d : ℕ} {epsilon : ℝ} (hd : 2 ≤ d) (hepsilon : 0 < epsilon) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta < deltaZero →
        2 * ((dyadicLevelCount delta : ℝ) + 1) *
            (delta ^ tau epsilon) ^ densityExponent d epsilon ≤ 1 := by
  let D : ℝ := 2 / Real.log 2 + 1
  have hsave := smallBranchSaving_pos hd hepsilon
  obtain ⟨deltaPower, hpowerPos, hpowerOne, hpower⟩ :=
    exists_deltaZero_const_mul_log_one_div_pow_mul_rpow_le
      (2 * D) 1 hsave zero_lt_one
  let deltaZero := min deltaPower (1 / 4)
  refine ⟨deltaZero, by positivity, by
    calc
      deltaZero ≤ 1 / 4 := min_le_right _ _
      _ < 1 := by norm_num, ?_⟩
  intro delta hdelta hsmall
  have hquarter : delta ≤ (1 / 4 : ℝ) :=
    hsmall.le.trans (min_le_right _ _)
  have hpower' := hpower delta hdelta
    (hsmall.trans_le (min_le_left _ _))
  have hlevel := dyadicLevelCount_cast_le_of_le_quarter hdelta hquarter
  have hlogOne : 1 ≤ Real.log (1 / delta) := by
    have hinv : (4 : ℝ) ≤ 1 / delta := by
      rw [le_div_iff₀ hdelta]
      nlinarith
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hinv
    have : (1 : ℝ) < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)]
      exact Real.exp_one_lt_d9.trans (by norm_num)
    linarith
  have hL : (dyadicLevelCount delta : ℝ) + 1 ≤
      D * Real.log (1 / delta) := by
    dsimp only [D]
    nlinarith
  have hpowEq :
      (delta ^ tau epsilon) ^ densityExponent d epsilon =
        delta ^ (tau epsilon * densityExponent d epsilon) := by
    rw [← Real.rpow_mul hdelta.le]
  rw [hpowEq]
  calc
    2 * ((dyadicLevelCount delta : ℝ) + 1) *
          delta ^ (tau epsilon * densityExponent d epsilon)
        ≤ 2 * (D * Real.log (1 / delta)) *
          delta ^ (tau epsilon * densityExponent d epsilon) := by
            gcongr
    _ = (2 * D) * (Real.log (1 / delta)) ^ (1 : ℕ) *
          delta ^ (tau epsilon * densityExponent d epsilon) := by ring
    _ ≤ 1 := hpower'

end
end Erdos186.PZ.ConvexDensity
