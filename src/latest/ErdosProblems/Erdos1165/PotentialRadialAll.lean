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

import ErdosProblems.Erdos1165.PotentialRadialAsymptotic
import ErdosProblems.Erdos1165.SharpAnnulusHarnack

/-!
# Whole-lattice radial potential asymptotic

The even-parity estimate is supplied by `PotentialRadialAsymptotic`.  At an
odd point the potential is exactly the average of its four even neighbors.
Their Euclidean radii differ from the original radius by at most one, so both
the inverse-radius error and the logarithmic main term remain uniform.
-/

open Real
open scoped BigOperators

namespace Erdos1165
namespace PotentialRadialAll

open EndpointDiagonal PotentialAsymptotic PotentialConvergence
open PotentialEuclideanGeometry PotentialRadialAsymptotic
open Annulus

private lemma abs_log_sub_log_le_two_div {r s : ℝ}
    (hr : 2 ≤ r) (hs : 0 < s) (hrs : |r - s| ≤ 1) :
    |Real.log s - Real.log r| ≤ 2 / r := by
  have hrpos : 0 < r := by linarith
  have hdiff₁ : s - r ≤ 1 := by linarith [(abs_le.mp hrs).1]
  have hdiff₂ : r - s ≤ 1 := (abs_le.mp hrs).2
  rcases le_total r s with hrs' | hsr
  · have hlog : Real.log r ≤ Real.log s := Real.log_le_log hrpos hrs'
    rw [abs_of_nonneg (sub_nonneg.mpr hlog)]
    have hratio : 0 < s / r := div_pos hs hrpos
    calc
      Real.log s - Real.log r = Real.log (s / r) := by
        rw [Real.log_div hs.ne' hrpos.ne']
      _ ≤ s / r - 1 := Real.log_le_sub_one_of_pos hratio
      _ ≤ 1 / r := by
        apply (sub_le_iff_le_add).2
        rw [div_le_iff₀ hrpos]
        calc
          s ≤ r + 1 := by linarith
          _ = (1 / r + 1) * r := by field_simp <;> ring
      _ ≤ 2 / r := by gcongr <;> norm_num
  · have hslow : r / 2 ≤ s := by linarith
    have hlog : Real.log s ≤ Real.log r := Real.log_le_log hs hsr
    rw [abs_of_nonpos (sub_nonpos.mpr hlog), neg_sub]
    have hratio : 0 < r / s := div_pos hrpos hs
    calc
      Real.log r - Real.log s = Real.log (r / s) := by
        rw [Real.log_div hrpos.ne' hs.ne']
      _ ≤ r / s - 1 := Real.log_le_sub_one_of_pos hratio
      _ ≤ 1 / s := by
        apply (sub_le_iff_le_add).2
        rw [div_le_iff₀ hs]
        calc
          r ≤ s + 1 := by linarith
          _ = (1 / s + 1) * s := by field_simp <;> ring
      _ ≤ 2 / r := by
        rw [div_le_div_iff₀ hs hrpos]
        nlinarith

private lemma neighbor_diagonalMax_ge_two {x : Point}
    (hx : ¬Even (x.1 + x.2)) (d : Direction)
    (hr : 4 ≤ euclideanRadius x) :
    2 ≤ max (firstDiagonalOffset (x - directionVector d))
      (secondDiagonalOffset (x - directionVector d)) := by
  let y := x - directionVector d
  change 2 ≤ max (firstDiagonalOffset y) (secondDiagonalOffset y)
  have hyEven : Even (y.1 + y.2) := by
    simpa only [y] using neighbor_even_of_not_even hx d
  have hgap := abs_euclideanRadius_sub_neighbor_le x d
  have hgap' : |euclideanRadius x - euclideanRadius y| ≤ 1 := by
    simpa only [y] using hgap
  have hyr : 3 ≤ euclideanRadius y := by
    linarith [(abs_le.mp hgap').2]
  have hupper := euclideanRadius_le_two_mul_diagonalMax_of_even hyEven
  by_contra h
  have hmax : max (firstDiagonalOffset y) (secondDiagonalOffset y) ≤ 1 := by omega
  have hcast :
      (max (firstDiagonalOffset y) (secondDiagonalOffset y) : ℕ) ≤ (1 : ℝ) := by
    exact_mod_cast hmax
  have : euclideanRadius y ≤ 2 := by
    calc
      euclideanRadius y ≤
          2 * (max (firstDiagonalOffset y) (secondDiagonalOffset y) : ℕ) := hupper
      _ ≤ 2 := by nlinarith
  linarith

private lemma neighbor_radial_error {x : Point}
    (hx : ¬Even (x.1 + x.2)) (hr : 4 ≤ euclideanRadius x)
    (d : Direction) :
    |planarPotentialKernel (x - directionVector d) -
        (2 / Real.pi) * Real.log (euclideanRadius x) - cPotential| ≤
      6444040002 / euclideanRadius x := by
  let y := x - directionVector d
  have hyEven : Even (y.1 + y.2) := by
    simpa only [y] using neighbor_even_of_not_even hx d
  have hyR := neighbor_diagonalMax_ge_two hx d hr
  have heven :=
    abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_of_even
      hyEven hyR
  have hgap := abs_euclideanRadius_sub_neighbor_le x d
  have hgap' : |euclideanRadius x - euclideanRadius y| ≤ 1 := by
    simpa only [y] using hgap
  have hrpos : 0 < euclideanRadius x := by linarith
  have hypos : 0 < euclideanRadius y := by
    linarith [(abs_le.mp hgap').2]
  have hyhalf : euclideanRadius x / 2 ≤ euclideanRadius y := by
    linarith [(abs_le.mp hgap').2]
  have heven' :
      |planarPotentialKernel y -
          (2 / Real.pi) * Real.log (euclideanRadius y) - cPotential| ≤
        6444040000 / euclideanRadius x := by
    calc
      _ ≤ 3222020000 / euclideanRadius y := heven
      _ ≤ 6444040000 / euclideanRadius x := by
        rw [div_le_div_iff₀ hypos hrpos]
        nlinarith
  have hlog := abs_log_sub_log_le_two_div (by linarith : 2 ≤ euclideanRadius x)
    hypos (by simpa only [abs_sub_comm] using hgap')
  have hcoef : (2 : ℝ) / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]
    exact Real.two_le_pi
  have hlog' :
      |(2 / Real.pi) *
          (Real.log (euclideanRadius y) - Real.log (euclideanRadius x))| ≤
        2 / euclideanRadius x := by
    rw [abs_mul, abs_of_nonneg (div_nonneg (by norm_num) Real.pi_nonneg)]
    exact (mul_le_mul hcoef hlog (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
  calc
    |planarPotentialKernel y -
        (2 / Real.pi) * Real.log (euclideanRadius x) - cPotential| =
      |(planarPotentialKernel y -
          (2 / Real.pi) * Real.log (euclideanRadius y) - cPotential) +
        (2 / Real.pi) *
          (Real.log (euclideanRadius y) - Real.log (euclideanRadius x))| := by
            congr 1
            ring
    _ ≤ |planarPotentialKernel y -
          (2 / Real.pi) * Real.log (euclideanRadius y) - cPotential| +
        |(2 / Real.pi) *
          (Real.log (euclideanRadius y) - Real.log (euclideanRadius x))| :=
      abs_add_le _ _
    _ ≤ 6444040000 / euclideanRadius x + 2 / euclideanRadius x :=
      add_le_add heven' hlog'
    _ = 6444040002 / euclideanRadius x := by ring

/-- **Classical whole-lattice potential-kernel expansion.**  The constant is
`(2γ + 3 log 2)/π`, and the error is uniform in the angle and in parity. -/
theorem abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le
    {x : Point} (hr : 4 ≤ euclideanRadius x) :
    |planarPotentialKernel x -
        (2 / Real.pi) * Real.log (euclideanRadius x) - cPotential| ≤
      6500000000 / euclideanRadius x := by
  have hrpos : 0 < euclideanRadius x := by linarith
  by_cases hx : Even (x.1 + x.2)
  · have hdiag : 2 ≤ max (firstDiagonalOffset x) (secondDiagonalOffset x) := by
      have hupper := euclideanRadius_le_two_mul_diagonalMax_of_even hx
      by_contra h
      have hmax : max (firstDiagonalOffset x) (secondDiagonalOffset x) ≤ 1 := by omega
      have hcast :
          (max (firstDiagonalOffset x) (secondDiagonalOffset x) : ℕ) ≤ (1 : ℝ) := by
        exact_mod_cast hmax
      have : euclideanRadius x ≤ 2 := hupper.trans (by nlinarith)
      linarith
    have heven :=
      abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_of_even
        hx hdiag
    exact heven.trans (div_le_div_of_nonneg_right (by norm_num) hrpos.le)
  · rw [planarPotentialKernel_eq_neighbor_average_of_not_even hx]
    let M : ℝ := (2 / Real.pi) * Real.log (euclideanRadius x) + cPotential
    have hrewrite :
        (1 / 4 : ℝ) * ∑ d : Direction,
            planarPotentialKernel (x - directionVector d) - M =
          (1 / 4 : ℝ) * ∑ d : Direction,
            (planarPotentialKernel (x - directionVector d) - M) := by
      rw [Finset.sum_sub_distrib]
      norm_num
      ring
    rw [show (1 / 4 : ℝ) * ∑ d : Direction,
          planarPotentialKernel (x - directionVector d) -
            (2 / Real.pi) * Real.log (euclideanRadius x) - cPotential =
        (1 / 4 : ℝ) * ∑ d : Direction,
          planarPotentialKernel (x - directionVector d) - M by
            dsimp [M]
            ring]
    rw [hrewrite, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    calc
      (1 / 4 : ℝ) *
          |∑ d : Direction,
            (planarPotentialKernel (x - directionVector d) - M)| ≤
        (1 / 4 : ℝ) * ∑ d : Direction,
          |planarPotentialKernel (x - directionVector d) - M| := by
            gcongr
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (1 / 4 : ℝ) * ∑ _d : Direction,
          (6444040002 / euclideanRadius x) := by
            gcongr with d
            simpa [M, sub_sub] using neighbor_radial_error hx hr d
      _ = 6444040002 / euclideanRadius x := by
        norm_num
        ring
      _ ≤ 6500000000 / euclideanRadius x :=
        div_le_div_of_nonneg_right (by norm_num) hrpos.le

/-! ## Direct use of the frozen annular shell API -/

open SharpAnnulusHarnack

/-- The radial shell comparison proved from the sharp asymptotic machinery
directly discharges the outer-boundary oscillation premise in the killed
Green/hitting-probability Harnack theorem. -/
theorem closedDisc_boundary_oscillation_of_radialShellPair
    (R rho : ℕ) {target q : Point}
    (hgeom : ∀ z, z ∈ outerBoundary (closedDisc R) →
      RadialShellPair (q - target) (z - target) rho) :
    ∀ z, z ∈ outerBoundary (closedDisc R) →
      |planarPotentialKernel (z - target) -
        planarPotentialKernel (q - target)| ≤ radialShellError rho :=
  closedDisc_boundary_potential_oscillation_le_radialShellError R rho hgeom

end PotentialRadialAll
end Erdos1165
