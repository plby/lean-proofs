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

import ErdosProblems.Erdos1165.AppendixLocalTime

/-!
# Algebra for marked Poisson kernels

Once the outer exit kernel is pointwise Harnack-comparable and the probability
of first hitting the marked point is comparable, the joint kernel of the
number of marked-point visits and the outer exit location is an elementary
calculation.  The positive atoms factor multiplicatively.  The zero atom is
the subtraction of paths which first hit the marked point, and therefore has
a slightly different (but explicit) error.
-/

namespace Erdos1165.PoissonKernelMarkedAlgebra

open AppendixLocalTime

/-- Abstract joint kernel forced by first-hit and positive-return
regeneration.  `outer u w` is the unmarked outer-exit kernel, `hit u` is the
probability of first hitting the marked point, and `center` is the marked
point itself. -/
def regeneratedMarkedKernel {Entrance Exit : Type*}
    (outer : Entrance → Exit → ℝ) (center : Entrance)
    (hit : Entrance → ℝ) (escape : ℝ)
    (u : Entrance) (k : ℕ) (w : Exit) : ℝ :=
  match k with
  | 0 => outer u w - hit u * outer center w
  | k + 1 => hit u * escape * (1 - escape) ^ k * outer center w

@[simp] theorem regeneratedMarkedKernel_zero {Entrance Exit : Type*}
    (outer : Entrance → Exit → ℝ) (center : Entrance)
    (hit : Entrance → ℝ) (escape : ℝ)
    (u : Entrance) (w : Exit) :
    regeneratedMarkedKernel outer center hit escape u 0 w =
      outer u w - hit u * outer center w := rfl

@[simp] theorem regeneratedMarkedKernel_succ {Entrance Exit : Type*}
    (outer : Entrance → Exit → ℝ) (center : Entrance)
    (hit : Entrance → ℝ) (escape : ℝ)
    (u : Entrance) (k : ℕ) (w : Exit) :
    regeneratedMarkedKernel outer center hit escape u (k + 1) w =
      hit u * escape * (1 - escape) ^ k * outer center w := rfl

/-- Positive visit atoms inherit the product of the hit-kernel and
Poisson-kernel Harnack factors. -/
theorem regeneratedMarkedKernel_succ_compare
    {Entrance Exit : Type*}
    {outer : Entrance → Exit → ℝ} {center u : Entrance} {w : Exit}
    {hit : Entrance → ℝ} {escape q hitError exitError : ℝ}
    (hq0 : 0 ≤ q) (hescape0 : 0 ≤ escape)
    (hescape1 : escape ≤ 1) (houter0 : 0 ≤ outer u w)
    (hhitLower : (1 - hitError) * q ≤ hit u)
    (hhitUpper : hit u ≤ (1 + hitError) * q)
    (hexitLower : (1 - exitError) * outer u w ≤ outer center w)
    (hexitUpper : outer center w ≤ (1 + exitError) * outer u w)
    (hhitError0 : 0 ≤ hitError) (hexitError0 : 0 ≤ exitError)
    (hhitFactor0 : 0 ≤ 1 - hitError)
    (hexitFactor0 : 0 ≤ 1 - exitError)
    (k : ℕ) :
    ((1 - hitError) * (1 - exitError)) *
        visitMass q escape (k + 1) * outer u w ≤
      regeneratedMarkedKernel outer center hit escape u (k + 1) w ∧
    regeneratedMarkedKernel outer center hit escape u (k + 1) w ≤
      ((1 + hitError) * (1 + exitError)) *
        visitMass q escape (k + 1) * outer u w := by
  have htail0 : 0 ≤ escape * (1 - escape) ^ k :=
    mul_nonneg hescape0 (pow_nonneg (sub_nonneg.mpr hescape1) _)
  have hhit0 : 0 ≤ hit u :=
    (mul_nonneg hhitFactor0 hq0).trans hhitLower
  have hcenter0 : 0 ≤ outer center w :=
    (mul_nonneg hexitFactor0 houter0).trans hexitLower
  have hhitUpper0 : 0 ≤ (1 + hitError) * q :=
    mul_nonneg (by linarith) hq0
  have hexitUpper0 : 0 ≤ 1 + exitError := by linarith
  rw [regeneratedMarkedKernel_succ, visitMass_succ_formula]
  constructor
  · calc
      ((1 - hitError) * (1 - exitError)) *
          (q * escape * (1 - escape) ^ k) * outer u w =
        ((1 - hitError) * q) * (escape * (1 - escape) ^ k) *
          ((1 - exitError) * outer u w) := by ring
      _ ≤ hit u * (escape * (1 - escape) ^ k) * outer center w := by
        gcongr
      _ = hit u * escape * (1 - escape) ^ k * outer center w := by ring
  · calc
      hit u * escape * (1 - escape) ^ k * outer center w =
        hit u * (escape * (1 - escape) ^ k) * outer center w := by ring
      _ ≤ ((1 + hitError) * q) * (escape * (1 - escape) ^ k) *
          ((1 + exitError) * outer u w) := by
        gcongr
      _ = ((1 + hitError) * (1 + exitError)) *
          (q * escape * (1 - escape) ^ k) * outer u w := by ring

/-- Lower comparison for the zero-visit atom.  Unlike positive atoms, the
error is amplified by the odds `q / (1-q)`, exactly as expected after
subtracting paths which first hit the marked point. -/
theorem regeneratedMarkedKernel_zero_lower
    {Entrance Exit : Type*}
    {outer : Entrance → Exit → ℝ} {center u : Entrance} {w : Exit}
    {hit : Entrance → ℝ} {escape q hitError exitError : ℝ}
    (houter0 : 0 ≤ outer u w)
    (hhit0 : 0 ≤ hit u)
    (hcenter0 : 0 ≤ outer center w)
    (hhitUpper : hit u ≤ (1 + hitError) * q)
    (hexitUpper : outer center w ≤ (1 + exitError) * outer u w)
    (hhitUpperFactor0 : 0 ≤ (1 + hitError) * q)
    (hexitUpperFactor0 : 0 ≤ 1 + exitError)
    (hq1 : q < 1) :
    (1 - (hitError + exitError + hitError * exitError) * q / (1 - q)) *
        visitMass q escape 0 * outer u w ≤
      regeneratedMarkedKernel outer center hit escape u 0 w := by
  rw [visitMass_zero, regeneratedMarkedKernel_zero]
  have hprod : hit u * outer center w ≤
      ((1 + hitError) * q) * ((1 + exitError) * outer u w) := by
    exact mul_le_mul hhitUpper hexitUpper
      hcenter0 hhitUpperFactor0
  have hqpos : 0 < 1 - q := sub_pos.mpr hq1
  rw [div_eq_mul_inv]
  field_simp [hqpos.ne']
  nlinarith

/-- Upper comparison for the zero-visit atom. -/
theorem regeneratedMarkedKernel_zero_upper
    {Entrance Exit : Type*}
    {outer : Entrance → Exit → ℝ} {center u : Entrance} {w : Exit}
    {hit : Entrance → ℝ} {escape q hitError exitError : ℝ}
    (houter0 : 0 ≤ outer u w)
    (hcenter0 : 0 ≤ outer center w)
    (hhitLower : (1 - hitError) * q ≤ hit u)
    (hexitLower : (1 - exitError) * outer u w ≤ outer center w)
    (hhitLowerFactor0 : 0 ≤ (1 - hitError) * q)
    (hexitLowerFactor0 : 0 ≤ 1 - exitError)
    (hq1 : q < 1) :
    regeneratedMarkedKernel outer center hit escape u 0 w ≤
      (1 + (hitError + exitError - hitError * exitError) * q / (1 - q)) *
        visitMass q escape 0 * outer u w := by
  rw [visitMass_zero, regeneratedMarkedKernel_zero]
  have hprod : ((1 - hitError) * q) *
      ((1 - exitError) * outer u w) ≤ hit u * outer center w := by
    have hhit0 : 0 ≤ hit u := hhitLowerFactor0.trans hhitLower
    exact mul_le_mul hhitLower hexitLower
      (mul_nonneg hexitLowerFactor0 houter0) hhit0
  have hqpos : 0 < 1 - q := sub_pos.mpr hq1
  rw [div_eq_mul_inv]
  field_simp [hqpos.ne']
  nlinarith

end Erdos1165.PoissonKernelMarkedAlgebra
