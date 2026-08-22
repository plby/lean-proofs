/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.PotentialRadialGlobal

/-!
# Wide-shell potential-kernel oscillation

The unit-shell estimate is not quite the form needed for a Poisson-kernel
Harnack inequality.  If a pole is allowed to move in a small inner disc,
the distances from that pole to an outer boundary range over a shell whose
width is comparable with the inner radius.  This file derives the required
wide-shell estimate directly from the global radial expansion.
-/

open Real

namespace Erdos1165.PoissonKernelRadial

open PlanarPotential PotentialConvergence PotentialEuclideanGeometry
  PotentialRadialAsymptotic PotentialRadialGlobal

noncomputable section

/-- Logarithm is `1 / rho`-Lipschitz on `[rho, infinity)`. -/
theorem abs_log_sub_log_le_div
    {r s rho width : ℝ} (hrho : 0 < rho)
    (hr : rho ≤ r) (hs : rho ≤ s) (hgap : |r - s| ≤ width) :
    |Real.log r - Real.log s| ≤ width / rho := by
  have hrpos : 0 < r := hrho.trans_le hr
  have hspos : 0 < s := hrho.trans_le hs
  rcases le_total r s with hrs | hsr
  · have hlog : Real.log r ≤ Real.log s := Real.log_le_log hrpos hrs
    rw [abs_of_nonpos (sub_nonpos.mpr hlog), neg_sub]
    calc
      Real.log s - Real.log r = Real.log (s / r) := by
        rw [Real.log_div hspos.ne' hrpos.ne']
      _ ≤ s / r - 1 := Real.log_le_sub_one_of_pos (div_pos hspos hrpos)
      _ = (s - r) / r := by field_simp
      _ ≤ width / r := by
        apply div_le_div_of_nonneg_right _ hrpos.le
        have := (abs_le.mp hgap).1
        linarith
      _ ≤ width / rho := by
        have hwidth : 0 ≤ width := (abs_nonneg (r - s)).trans hgap
        exact div_le_div_of_nonneg_left hwidth hrho hr
  · have hlog : Real.log s ≤ Real.log r := Real.log_le_log hspos hsr
    rw [abs_of_nonneg (sub_nonneg.mpr hlog)]
    calc
      Real.log r - Real.log s = Real.log (r / s) := by
        rw [Real.log_div hrpos.ne' hspos.ne']
      _ ≤ r / s - 1 := Real.log_le_sub_one_of_pos (div_pos hrpos hspos)
      _ = (r - s) / s := by field_simp
      _ ≤ width / s := by
        apply div_le_div_of_nonneg_right _ hspos.le
        exact (abs_le.mp hgap).2
      _ ≤ width / rho := by
        have hwidth : 0 ≤ width := (abs_nonneg (r - s)).trans hgap
        exact div_le_div_of_nonneg_left hwidth hrho hs

/-- Explicit wide-shell potential oscillation.  The constant consists of
two global radial remainders and the logarithmic displacement term. -/
theorem abs_planarPotentialKernel_sub_le_of_wide_euclidean_shell
    {x y : Point} {rho width : ℝ} (hrho : 0 < rho)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : rho ≤ euclideanRadius x)
    (hy : rho ≤ euclideanRadius y)
    (hgap : |euclideanRadius x - euclideanRadius y| ≤ width) :
    |planarPotentialKernel x - planarPotentialKernel y| ≤
      (2 * globalRadialConstant + width) / rho := by
  have hxpos : 0 < euclideanRadius x := hrho.trans_le hx
  have hypos : 0 < euclideanRadius y := hrho.trans_le hy
  have hax :=
    abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_global
      hx0
  have hay :=
    abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_global
      hy0
  have hax' :
      |planarPotentialKernel x -
          (2 / Real.pi) * Real.log (euclideanRadius x) - cPotential| ≤
        globalRadialConstant / rho :=
    hax.trans (div_le_div_of_nonneg_left globalRadialConstant_pos.le hrho hx)
  have hay' :
      |planarPotentialKernel y -
          (2 / Real.pi) * Real.log (euclideanRadius y) - cPotential| ≤
        globalRadialConstant / rho :=
    hay.trans (div_le_div_of_nonneg_left globalRadialConstant_pos.le hrho hy)
  have hlog := abs_log_sub_log_le_div hrho hx hy hgap
  have hcoef : |(2 : ℝ) / Real.pi| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (by norm_num) Real.pi_nonneg),
      div_le_one Real.pi_pos]
    exact Real.two_le_pi
  have hlog' :
      |(2 / Real.pi) *
          (Real.log (euclideanRadius x) - Real.log (euclideanRadius y))| ≤
        width / rho := by
    rw [abs_mul]
    calc
      |(2 : ℝ) / Real.pi| *
          |Real.log (euclideanRadius x) - Real.log (euclideanRadius y)| ≤
        1 * (width / rho) := by
          exact mul_le_mul hcoef hlog (abs_nonneg _) (by positivity)
      _ = width / rho := one_mul _
  calc
    |planarPotentialKernel x - planarPotentialKernel y| =
      |(planarPotentialKernel x -
          (2 / Real.pi) * Real.log (euclideanRadius x) - cPotential) -
        (planarPotentialKernel y -
          (2 / Real.pi) * Real.log (euclideanRadius y) - cPotential) +
        (2 / Real.pi) *
          (Real.log (euclideanRadius x) - Real.log (euclideanRadius y))| := by
            congr 1
            ring
    _ ≤ |planarPotentialKernel x -
          (2 / Real.pi) * Real.log (euclideanRadius x) - cPotential| +
        |planarPotentialKernel y -
          (2 / Real.pi) * Real.log (euclideanRadius y) - cPotential| +
        |(2 / Real.pi) *
          (Real.log (euclideanRadius x) - Real.log (euclideanRadius y))| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ globalRadialConstant / rho + globalRadialConstant / rho +
        width / rho := add_le_add (add_le_add hax' hay') hlog'
    _ = (2 * globalRadialConstant + width) / rho := by ring

end

end Erdos1165.PoissonKernelRadial
