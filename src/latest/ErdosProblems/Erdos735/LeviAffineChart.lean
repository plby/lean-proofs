/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos735.ProjectiveArrangement

/-!
# The affine chart attached to a selected dual line

For a concrete point `p`, the selected dual line has normal
`normalVec p = (p₀,p₁,1)`.  The affine plane on which this normal evaluates
to one is parametrized by

`u ↦ (u₀,u₁,1-p₀u₀-p₁u₁)`.

In this chart the dual line belonging to `q` has the particularly simple
equation

`1 + (q-p)₀u₀ + (q-p)₁u₁ = 0`.

The homogeneous direction associated with `u` is obtained by deleting the
constant `1`; it lies on the selected projective line.  These identities are
the algebraic transport used by the exterior-wedge proof of Levi's theorem.
-/

open scoped Matrix
open Matrix

namespace Erdos735.LeviAffineChart

noncomputable section

abbrev Point := ProjectiveArrangement.Point
abbrev Vec3 := SignVector.Vec3

/-- The affine chart `normalVec p · x = 1` attached to the selected owner
`p`. -/
def chartPoint (p u : Point) : Vec3 :=
  ![u 0, u 1, 1 - p 0 * u 0 - p 1 * u 1]

/-- The homogeneous point at infinity in chart direction `u`. -/
def chartDirection (p u : Point) : Vec3 :=
  ![u 0, u 1, -(p 0 * u 0 + p 1 * u 1)]

/-- The affine linear equation of the dual line belonging to `q`, in the
chart selected by `p`. -/
def lineEval (p q u : Point) : ℝ :=
  1 + (q 0 - p 0) * u 0 + (q 1 - p 1) * u 1

/-- The linear part of `lineEval`; this is evaluation on a point at
infinity of the selected chart. -/
def directionEval (p q u : Point) : ℝ :=
  (q 0 - p 0) * u 0 + (q 1 - p 1) * u 1

@[simp] theorem normalVec_dot_chartPoint (p q u : Point) :
    ProjectiveArrangement.normalVec q ⬝ᵥ chartPoint p u = lineEval p q u := by
  simp [ProjectiveArrangement.normalVec, chartPoint, lineEval]
  ring

@[simp] theorem selected_dot_chartPoint (p u : Point) :
    ProjectiveArrangement.normalVec p ⬝ᵥ chartPoint p u = 1 := by
  rw [normalVec_dot_chartPoint]
  simp [lineEval]

@[simp] theorem normalVec_dot_chartDirection (p q u : Point) :
    ProjectiveArrangement.normalVec q ⬝ᵥ chartDirection p u =
      directionEval p q u := by
  simp [ProjectiveArrangement.normalVec, chartDirection, directionEval]
  ring

@[simp] theorem selected_dot_chartDirection (p u : Point) :
    ProjectiveArrangement.normalVec p ⬝ᵥ chartDirection p u = 0 := by
  rw [normalVec_dot_chartDirection]
  simp [directionEval]

theorem lineEval_eq_one_add_directionEval (p q u : Point) :
    lineEval p q u = 1 + directionEval p q u := by
  simp [lineEval, directionEval]
  ring

theorem lineEval_add (p q u v : Point) :
    lineEval p q (u + v) =
      lineEval p q u + directionEval p q v := by
  simp [lineEval, directionEval]
  ring

theorem lineEval_add_smul (p q u v : Point) (t : ℝ) :
    lineEval p q (u + t • v) =
      lineEval p q u + t * directionEval p q v := by
  simp [lineEval, directionEval]
  ring

theorem directionEval_add (p q u v : Point) :
    directionEval p q (u + v) =
      directionEval p q u + directionEval p q v := by
  simp [directionEval]
  ring

theorem directionEval_smul (p q u : Point) (t : ℝ) :
    directionEval p q (t • u) = t * directionEval p q u := by
  simp [directionEval]
  ring

theorem chartPoint_add_direction (p u v : Point) :
    chartPoint p (u + v) = chartPoint p u + chartDirection p v := by
  funext i
  fin_cases i <;> simp [chartPoint, chartDirection] <;> ring

theorem chartPoint_add_smul_direction (p u v : Point) (t : ℝ) :
    chartPoint p (u + t • v) =
      chartPoint p u + t • chartDirection p v := by
  funext i
  fin_cases i <;> simp [chartPoint, chartDirection] <;> ring

theorem chartDirection_injective (p : Point) :
    Function.Injective (chartDirection p) := by
  intro u v huv
  apply PiLp.ext
  intro i
  fin_cases i
  · exact congrFun huv 0
  · exact congrFun huv 1

theorem chartPoint_injective (p : Point) :
    Function.Injective (chartPoint p) := by
  intro u v huv
  apply PiLp.ext
  intro i
  fin_cases i
  · exact congrFun huv 0
  · exact congrFun huv 1

theorem chartDirection_ne_zero {p u : Point} (hu : u ≠ 0) :
    chartDirection p u ≠ 0 := by
  intro hzero
  apply hu
  apply chartDirection_injective p
  simpa [chartDirection] using hzero

/-- A point lies on the affine dual line of `q` exactly when its homogeneous
chart representative lies on the corresponding projective line. -/
theorem lineEval_eq_zero_iff (p q u : Point) :
    lineEval p q u = 0 ↔
      ProjectiveArrangement.normalVec q ⬝ᵥ chartPoint p u = 0 := by
  rw [normalVec_dot_chartPoint]

/-- A chart direction is cut by the affine direction of `q` exactly when
the corresponding homogeneous point at infinity is on the dual line of
`q`. -/
theorem directionEval_eq_zero_iff (p q u : Point) :
    directionEval p q u = 0 ↔
      ProjectiveArrangement.normalVec q ⬝ᵥ chartDirection p u = 0 := by
  rw [normalVec_dot_chartDirection]

end

end Erdos735.LeviAffineChart
