/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.LiteralRealAnnulus
import ErdosProblems.Erdos1165.PotentialRadialGlobal

/-!
# Potential kernel on a literal real-radius boundary

The HLOZ radii are real.  This file records the corresponding boundary-shell
geometry and evaluates the planar potential kernel there without introducing
an integer radius.  The shell geometry is imported from the literal
real-radius Poisson-kernel development.
-/

open Real Set

namespace Erdos1165.LiteralRealBoundaryPotential

open PotentialAsymptotic PotentialConvergence PotentialEuclideanGeometry
open PotentialRadialAsymptotic
open PotentialRadialGlobal ThickPoint
open LiteralRealAnnulus

noncomputable section

/-! ## Potential on a unit-thick real shell -/

/-- The global radial expansion, evaluated against the outer real radius of
a unit-thick shell.  The explicit threshold ensures that both logarithms and
the denominator `r-1` are positive. -/
theorem abs_planarPotentialKernel_sub_log_realRadius_le_of_shell
    {r : ℝ} {z : Point} (hr : 2 < r)
    (hzLower : r - 1 < euclideanRadius z)
    (hzUpper : euclideanRadius z ≤ r) :
    |planarPotentialKernel z -
        (2 / Real.pi) * Real.log r - cPotential| ≤
      (globalRadialConstant + 2) / (r - 1) := by
  have hdenPos : 0 < r - 1 := by linarith
  have hzPos : 0 < euclideanRadius z := hdenPos.trans hzLower
  have hzNe : z ≠ 0 := (euclideanRadius_pos_iff z).mp hzPos
  have hradial :=
    abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_global
      hzNe
  have hconstantNonneg : 0 ≤ globalRadialConstant :=
    globalRadialConstant_pos.le
  have hradial' :
      |planarPotentialKernel z -
          (2 / Real.pi) * Real.log (euclideanRadius z) - cPotential| ≤
        globalRadialConstant / (r - 1) := by
    exact hradial.trans
      (div_le_div_of_nonneg_left hconstantNonneg hdenPos hzLower.le)
  have hradiusGap : |r - euclideanRadius z| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hzUpper)]
    linarith
  have hlog := abs_log_sub_log_le_two_div
    (by linarith : 2 ≤ r) hzPos hradiusGap
  have hcoefficient : (2 : ℝ) / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]
    exact Real.two_le_pi
  have hlogScaled :
      |(2 / Real.pi) *
          (Real.log (euclideanRadius z) - Real.log r)| ≤
        2 / (r - 1) := by
    rw [abs_mul,
      abs_of_nonneg (div_nonneg (by norm_num) Real.pi_nonneg)]
    calc
      (2 / Real.pi) *
          |Real.log (euclideanRadius z) - Real.log r| ≤
        1 * (2 / r) := by
          exact mul_le_mul hcoefficient hlog (abs_nonneg _) (by positivity)
      _ = 2 / r := by ring
      _ ≤ 2 / (r - 1) := by
        exact div_le_div_of_nonneg_left (by norm_num) hdenPos (by linarith)
  calc
    |planarPotentialKernel z -
        (2 / Real.pi) * Real.log r - cPotential| =
      |(planarPotentialKernel z -
          (2 / Real.pi) * Real.log (euclideanRadius z) - cPotential) +
        (2 / Real.pi) *
          (Real.log (euclideanRadius z) - Real.log r)| := by
            congr 1
            ring
    _ ≤ |planarPotentialKernel z -
          (2 / Real.pi) * Real.log (euclideanRadius z) - cPotential| +
        |(2 / Real.pi) *
          (Real.log (euclideanRadius z) - Real.log r)| := abs_add_le _ _
    _ ≤ globalRadialConstant / (r - 1) + 2 / (r - 1) :=
      add_le_add hradial' hlogScaled
    _ = (globalRadialConstant + 2) / (r - 1) := by ring

/-- Potential-kernel expansion on the literal boundary `∂D(0,r)`. -/
theorem abs_planarPotentialKernel_sub_log_realRadius_le
    {r : ℝ} {z : Point} (hr : 2 < r)
    (hz : z ∈ discBoundary 0 r) :
    |planarPotentialKernel z -
        (2 / Real.pi) * Real.log r - cPotential| ≤
      (globalRadialConstant + 2) / (r - 1) := by
  exact abs_planarPotentialKernel_sub_log_realRadius_le_of_shell hr
    (discBoundary_zero_euclideanRadius_bounds_real hz).1
    (discBoundary_zero_euclideanRadius_bounds_real hz).2

end

end Erdos1165.LiteralRealBoundaryPotential
