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

import ErdosProblems.Erdos636.External.Erdos88.Concentration

/-!
# Truncated expectations on finite probability spaces

This file records the elementary second-moment truncation estimate used to
discard the exceptional outer choices in the Kwan--Sudakov construction.
All expectations are normalized counting expectations on a nonempty finite
type.
-/

open scoped BigOperators

namespace Erdos636
namespace TailExpectation

open Finset Real
open Erdos88.Concentration

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The absolute first moment of `X`, restricted to outcomes on which
`|X|` is at least `u`. -/
noncomputable def truncatedAbsExpectation (X : Ω → ℝ) (u : ℝ) : ℝ :=
  uniformExpectation fun ω ↦ if u ≤ |X ω| then |X ω| else 0

lemma truncatedAbsExpectation_nonneg (X : Ω → ℝ) (u : ℝ) :
    0 ≤ truncatedAbsExpectation X u := by
  rw [truncatedAbsExpectation, uniformExpectation]
  positivity

/-- Division-free second-moment truncation.  On the exceptional event
`u ≤ |X|`, multiplication by `u` turns the truncated first moment into a
quantity bounded pointwise by `|X|²`. -/
lemma mul_truncatedAbsExpectation_le_secondMoment (X : Ω → ℝ) (u : ℝ) :
    u * truncatedAbsExpectation X u ≤
      uniformExpectation fun ω ↦ |X ω| ^ 2 := by
  rw [truncatedAbsExpectation, uniformExpectation, uniformExpectation]
  have hcard : (0 : ℝ) ≤ Fintype.card Ω := by positivity
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hcard
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _hω
  by_cases htail : u ≤ |X ω|
  · simp only [if_pos htail]
    simpa [pow_two] using
      mul_le_mul_of_nonneg_right htail (abs_nonneg (X ω))
  · simp only [if_neg htail, mul_zero]
    exact sq_nonneg _

/-- A truncated first moment is at most the second moment divided by the
positive truncation threshold. -/
lemma truncatedAbsExpectation_le_secondMoment_div (X : Ω → ℝ) (u : ℝ)
    (hu : 0 < u) :
    truncatedAbsExpectation X u ≤
      (uniformExpectation fun ω ↦ |X ω| ^ 2) / u := by
  rw [le_div_iff₀ hu]
  simpa [mul_comm] using
    mul_truncatedAbsExpectation_le_secondMoment X u

/-- Explicit square-root-scale truncation bound.  If the uniform second
moment of `X` is at most `v`, then the contribution from
`|X| ≥ Q * sqrt v` is at most `sqrt v / Q`. -/
lemma truncatedAbsExpectation_mul_sqrt_le
    (X : Ω → ℝ) (v Q : ℝ) (hv : 0 < v) (hQ : 0 < Q)
    (hsecond : uniformExpectation (fun ω ↦ |X ω| ^ 2) ≤ v) :
    truncatedAbsExpectation X (Q * sqrt v) ≤ sqrt v / Q := by
  have hsqrt : 0 < sqrt v := sqrt_pos.2 hv
  have hthreshold : 0 < Q * sqrt v := mul_pos hQ hsqrt
  calc
    truncatedAbsExpectation X (Q * sqrt v) ≤
        (uniformExpectation fun ω ↦ |X ω| ^ 2) / (Q * sqrt v) :=
      truncatedAbsExpectation_le_secondMoment_div X _ hthreshold
    _ ≤ v / (Q * sqrt v) :=
      div_le_div_of_nonneg_right hsecond hthreshold.le
    _ = (sqrt v * sqrt v) / (Q * sqrt v) := by
      congr 1
      nlinarith [sq_sqrt hv.le]
    _ = sqrt v / Q := mul_div_mul_right _ _ hsqrt.ne'

/-- The same estimate with `X²` instead of `|X|²` in the hypothesis. -/
lemma truncatedAbsExpectation_mul_sqrt_le_of_sq
    (X : Ω → ℝ) (v Q : ℝ) (hv : 0 < v) (hQ : 0 < Q)
    (hsecond : uniformExpectation (fun ω ↦ X ω ^ 2) ≤ v) :
    truncatedAbsExpectation X (Q * sqrt v) ≤ sqrt v / Q := by
  apply truncatedAbsExpectation_mul_sqrt_le X v Q hv hQ
  simpa only [sq_abs] using hsecond

end TailExpectation
end Erdos636
