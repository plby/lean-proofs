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

import ErdosProblems.Erdos1165.PotentialRadialAll

/-!
# Global form of the radial potential-kernel expansion

The analytic estimate applies outside radius four.  The remaining lattice
points form an explicit finite box.  Adding their finitely many weighted
errors to the analytic constant gives a single constant valid at every
nonzero lattice point.
-/

open Real
open scoped BigOperators

namespace Erdos1165
namespace PotentialRadialGlobal

open PotentialAsymptotic PotentialConvergence
open PotentialEuclideanGeometry PotentialRadialAsymptotic PotentialRadialAll

/-- The finite box containing all lattice points of Euclidean radius below
four. -/
noncomputable def smallRadialPoints : Finset Point :=
  (Finset.Icc (-3 : ℤ) 3).product (Finset.Icc (-3 : ℤ) 3)

/-- The centered radial error. -/
noncomputable def radialError (x : Point) : ℝ :=
  planarPotentialKernel x -
    (2 / Real.pi) * Real.log (euclideanRadius x) - cPotential

/-- An explicit global constant: the large-radius analytic constant plus
the finite sum of all weighted small-radius errors. -/
noncomputable def globalRadialConstant : ℝ :=
  6500000000 + ∑ x ∈ smallRadialPoints,
    euclideanRadius x * |radialError x|

theorem globalRadialConstant_pos : 0 < globalRadialConstant := by
  unfold globalRadialConstant
  have hsum : 0 ≤ ∑ x ∈ smallRadialPoints,
      euclideanRadius x * |radialError x| := by
    exact Finset.sum_nonneg fun x _ ↦
      mul_nonneg (euclideanRadius_nonneg x) (abs_nonneg _)
  linarith

private lemma mem_smallRadialPoints_of_radius_lt_four {x : Point}
    (hx : euclideanRadius x < 4) : x ∈ smallRadialPoints := by
  have hre : |(x.1 : ℝ)| ≤ euclideanRadius x := by
    rw [euclideanRadius_eq_norm_pointComplex]
    simpa [pointComplex] using Complex.abs_re_le_norm (pointComplex x)
  have him : |(x.2 : ℝ)| ≤ euclideanRadius x := by
    rw [euclideanRadius_eq_norm_pointComplex]
    simpa [pointComplex] using Complex.abs_im_le_norm (pointComplex x)
  have hre' : |(x.1 : ℝ)| < 4 := hre.trans_lt hx
  have him' : |(x.2 : ℝ)| < 4 := him.trans_lt hx
  have hx1lo : (-3 : ℤ) ≤ x.1 := by
    have : (-4 : ℝ) < (x.1 : ℝ) := (abs_lt.mp hre').1
    have hz : (-4 : ℤ) < x.1 := by exact_mod_cast this
    omega
  have hx1hi : x.1 ≤ (3 : ℤ) := by
    have : (x.1 : ℝ) < 4 := (abs_lt.mp hre').2
    have hz : x.1 < (4 : ℤ) := by exact_mod_cast this
    omega
  have hx2lo : (-3 : ℤ) ≤ x.2 := by
    have : (-4 : ℝ) < (x.2 : ℝ) := (abs_lt.mp him').1
    have hz : (-4 : ℤ) < x.2 := by exact_mod_cast this
    omega
  have hx2hi : x.2 ≤ (3 : ℤ) := by
    have : (x.2 : ℝ) < 4 := (abs_lt.mp him').2
    have hz : x.2 < (4 : ℤ) := by exact_mod_cast this
    omega
  exact Finset.mem_product.2
    ⟨Finset.mem_Icc.2 ⟨hx1lo, hx1hi⟩, Finset.mem_Icc.2 ⟨hx2lo, hx2hi⟩⟩

/-- **Uniform classical planar potential-kernel expansion.**  The same
constant works for every nonzero lattice point, independently of angle and
parity. -/
theorem abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_global
    {x : Point} (hx : x ≠ 0) :
    |planarPotentialKernel x -
        (2 / Real.pi) * Real.log (euclideanRadius x) - cPotential| ≤
      globalRadialConstant / euclideanRadius x := by
  have hrpos : 0 < euclideanRadius x := (euclideanRadius_pos_iff x).2 hx
  change |radialError x| ≤ globalRadialConstant / euclideanRadius x
  by_cases hr : 4 ≤ euclideanRadius x
  · have hlarge :=
      abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le hr
    change |radialError x| ≤ 6500000000 / euclideanRadius x at hlarge
    exact hlarge.trans (div_le_div_of_nonneg_right (by
      unfold globalRadialConstant
      have hsum : 0 ≤ ∑ y ∈ smallRadialPoints,
          euclideanRadius y * |radialError y| := by
        exact Finset.sum_nonneg fun y _ ↦
          mul_nonneg (euclideanRadius_nonneg y) (abs_nonneg _)
      linarith) hrpos.le)
  · have hxmem : x ∈ smallRadialPoints :=
      mem_smallRadialPoints_of_radius_lt_four (lt_of_not_ge hr)
    have hterm : euclideanRadius x * |radialError x| ≤
        ∑ y ∈ smallRadialPoints, euclideanRadius y * |radialError y| := by
      exact Finset.single_le_sum
        (f := fun y ↦ euclideanRadius y * |radialError y|)
        (fun y _ ↦ mul_nonneg (euclideanRadius_nonneg y) (abs_nonneg _)) hxmem
    apply (le_div_iff₀ hrpos).2
    calc
      |radialError x| * euclideanRadius x =
          euclideanRadius x * |radialError x| := by ring
      _ ≤ ∑ y ∈ smallRadialPoints,
          euclideanRadius y * |radialError y| := hterm
      _ ≤ globalRadialConstant := by
        unfold globalRadialConstant
        norm_num

/-- A public logarithmic Lipschitz estimate used to turn the radial
expansion into shell oscillation bounds. -/
theorem abs_log_sub_log_le_two_div {r s : ℝ}
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

/-- Potential-kernel oscillation between two points in a unit-thick
Euclidean shell. -/
theorem abs_planarPotentialKernel_sub_le_of_euclidean_shell
    {x y : Point} {ρ : ℕ} (hρ : 4 ≤ ρ)
    (hx : (ρ : ℝ) ≤ euclideanRadius x)
    (hy : (ρ : ℝ) ≤ euclideanRadius y)
    (hxy : |euclideanRadius x - euclideanRadius y| ≤ 1) :
    |planarPotentialKernel x - planarPotentialKernel y| ≤
      13000000002 / (ρ : ℝ) := by
  have hρpos : (0 : ℝ) < ρ := by positivity
  have hxpos : 0 < euclideanRadius x := hρpos.trans_le hx
  have hypos : 0 < euclideanRadius y := hρpos.trans_le hy
  have hax :=
    abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le
      (show 4 ≤ euclideanRadius x by
        have hρR : (4 : ℝ) ≤ ρ := by exact_mod_cast hρ
        exact hρR.trans hx)
  have hay :=
    abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le
      (show 4 ≤ euclideanRadius y by
        have hρR : (4 : ℝ) ≤ ρ := by exact_mod_cast hρ
        exact hρR.trans hy)
  have hax' :
      |planarPotentialKernel x -
          (2 / Real.pi) * Real.log (euclideanRadius x) - cPotential| ≤
        6500000000 / (ρ : ℝ) :=
    hax.trans (div_le_div_of_nonneg_left (by norm_num) hρpos hx)
  have hay' :
      |planarPotentialKernel y -
          (2 / Real.pi) * Real.log (euclideanRadius y) - cPotential| ≤
        6500000000 / (ρ : ℝ) :=
    hay.trans (div_le_div_of_nonneg_left (by norm_num) hρpos hy)
  have hlog := abs_log_sub_log_le_two_div
    (show 2 ≤ euclideanRadius x by
      have hρR : (4 : ℝ) ≤ ρ := by exact_mod_cast hρ
      linarith)
    hypos (by simpa only [abs_sub_comm] using hxy)
  have hlogρ :
      |(2 / Real.pi) *
          (Real.log (euclideanRadius x) - Real.log (euclideanRadius y))| ≤
        2 / (ρ : ℝ) := by
    rw [abs_mul, abs_of_nonneg (div_nonneg (by norm_num) Real.pi_nonneg)]
    have hcoef : (2 : ℝ) / Real.pi ≤ 1 := by
      rw [div_le_one Real.pi_pos]
      exact Real.two_le_pi
    calc
      (2 / Real.pi) *
          |Real.log (euclideanRadius x) - Real.log (euclideanRadius y)| ≤
        1 * (2 / euclideanRadius x) := by
          apply mul_le_mul hcoef (by simpa only [abs_sub_comm] using hlog)
            (abs_nonneg _) (by positivity)
      _ ≤ 2 / (ρ : ℝ) := by
        rw [one_mul]
        exact div_le_div_of_nonneg_left (by norm_num) hρpos hx
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
    _ ≤ 6500000000 / (ρ : ℝ) + 6500000000 / (ρ : ℝ) +
        2 / (ρ : ℝ) := add_le_add (add_le_add hax' hay') hlogρ
    _ = 13000000002 / (ρ : ℝ) := by ring

end PotentialRadialGlobal
end Erdos1165

open Erdos1165.PotentialRadialGlobal
