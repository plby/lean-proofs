/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.ExternalGreenRenewal
import ErdosProblems.Erdos1165.ExternalQuantitativeRenewal

/-!
# Sharp external one-point tail from a finite Tauberian estimate

This module joins three already checked ingredients:

* the exact renewal recursion for the retained-block walk;
* the sharp finite Tauberian upper bound for its truncated Green function;
* a coarse reciprocal return bound, used only over a distant short interval.

The comparison horizon `m` may be much larger than the local-time horizon
`n`, while the Abelian parameter `D` may in turn be moderately larger than
`m`.  Thus `n / m` controls the renewal numerator, `m / D` is the finite
Tauberian loss, and the denominator retains the sharp coefficient
`15 / (16 * π)`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.ExternalSharpOnePoint

open ExternalWalk ExternalOnePoint LazyDecomposition

/-- Explicit upper bound for the external truncated Green function obtained
by solving the finite Tauberian inequality for `G(m)`. -/
noncomputable def sharpGreenUpper (m : ℕ) (D : ℝ) : ℝ :=
  ((15 * D / (16 * D - 1)) *
      (1 + Real.log ((16 * D - 1) / 15) / Real.pi + Real.pi / 9)) /
    (1 - (m : ℝ) / D)

/-- The coarse distant-horizon Green increment supplied by a reciprocal
coefficient bound with constant `B`. -/
noncomputable def distantIncrementUpper (B : ℝ) (n m : ℕ) : ℝ :=
  B * (n : ℝ) / (m + 1 : ℝ)

theorem externalTruncatedGreenCount_le_sharpGreenUpper
    (o : Orientation) (m : ℕ) (D : ℝ)
    (hD : 1 ≤ D) (hmD : (m : ℝ) < D) :
    ExternalGreenRenewal.externalTruncatedGreenCount o m ≤
      sharpGreenUpper m D := by
  have hfactor : 0 < 1 - (m : ℝ) / D := by
    have hDpos : 0 < D := zero_lt_one.trans_le hD
    rw [sub_pos, div_lt_one hDpos]
    exact hmD
  apply (le_div_iff₀ hfactor).2
  simpa [mul_comm] using
    ExternalGreenRenewal.one_sub_nat_div_mul_externalTruncatedGreenCount_le_log_D
      o m D hD

theorem externalTruncatedGreenCount_increment_le_distant
    (o : Orientation) (B : ℝ) (hB : 0 ≤ B)
    (hpoint : ∀ k : ℕ, 0 < k →
      ExternalGreenRenewal.externalReturnProbability o k ≤ B / (k : ℝ))
    (n m : ℕ) :
    ExternalGreenRenewal.externalTruncatedGreenCount o (n + m) -
        ExternalGreenRenewal.externalTruncatedGreenCount o m ≤
      distantIncrementUpper B n m := by
  exact ExternalGreenRenewal.externalTruncatedGreenCount_increment_le_of_reciprocal
    o B hB hpoint m n

/-- Quantitative one-point local-time tail retaining the sharp Green
coefficient.  This is the direct reusable interface for HLOZ (7.4); its sole
coefficient hypothesis is the coarse reciprocal bound used in the distant
increment. -/
theorem externalOriginLocalTime_tail_le_sharp
    (o : Orientation) (r n m : ℕ) (B D : ℝ)
    (hB : 0 ≤ B)
    (hpoint : ∀ k : ℕ, 0 < k →
      ExternalGreenRenewal.externalReturnProbability o k ≤ B / (k : ℝ))
    (hD : 1 ≤ D) (hmD : (m : ℝ) < D)
    (hdelta : distantIncrementUpper B n m ≤ 1) :
    externalBlocks o {eta | r + 1 ≤ externalOriginLocalTime o eta n} ≤
      (ENNReal.ofReal
        (1 - (1 - distantIncrementUpper B n m) /
          sharpGreenUpper m D)) ^ r := by
  have hgreenCount := externalTruncatedGreenCount_le_sharpGreenUpper
    o m D hD hmD
  have hincrementCount := externalTruncatedGreenCount_increment_le_distant
    o B hB hpoint n m
  have hgreen :
      ExternalRenewal.externalTruncatedGreenReal o m ≤ sharpGreenUpper m D := by
    rw [← ExternalGreenRenewal.externalTruncatedGreenCount_eq_renewal]
    exact hgreenCount
  have hincrement :
      ExternalRenewal.externalTruncatedGreenReal o (n + m) -
          ExternalRenewal.externalTruncatedGreenReal o m ≤
        distantIncrementUpper B n m := by
    rw [← ExternalGreenRenewal.externalTruncatedGreenCount_eq_renewal,
      ← ExternalGreenRenewal.externalTruncatedGreenCount_eq_renewal]
    exact hincrementCount
  have hfirst : ExternalRenewal.externalFirstReturnMass o n ≤
      1 - (1 - distantIncrementUpper B n m) / sharpGreenUpper m D := by
    exact QuantitativeRenewal.firstReturnMass_le_one_sub_div_of_green_bounds
      (ExternalRenewal.externalFirstReturnProbability o)
      (ExternalRenewal.externalReturnProbability o)
      (ExternalRenewal.externalFirstReturnProbability_nonneg o)
      (ExternalRenewal.externalReturnProbability_nonneg o)
      (ExternalRenewal.externalFirstReturnProbability_zero o)
      (ExternalRenewal.externalReturnProbability_zero o)
      (fun k hk ↦ ExternalRenewal.externalReturnProbabilityReal_renewal o hk)
      n m (distantIncrementUpper B n m) (sharpGreenUpper m D)
      hdelta hincrement hgreen
  have hmass : 0 ≤ ExternalRenewal.externalFirstReturnMass o n :=
    RenewalTail.firstReturnMass_nonneg
      (ExternalRenewal.externalFirstReturnProbability_nonneg o) n
  have hbase : 0 ≤
      1 - (1 - distantIncrementUpper B n m) / sharpGreenUpper m D :=
    hmass.trans hfirst
  have hENN : ExternalRenewal.externalFirstReturnMassENNReal o n ≤
      ENNReal.ofReal
        (1 - (1 - distantIncrementUpper B n m) / sharpGreenUpper m D) := by
    apply (ENNReal.toReal_le_toReal
      (ExternalRenewal.externalFirstReturnMassENNReal_ne_top o n)
      ENNReal.ofReal_ne_top).mp
    rw [ExternalRenewal.externalFirstReturnMassENNReal_toReal o n,
      ENNReal.toReal_ofReal hbase]
    exact hfirst
  exact (ExternalRenewal.externalReturnTail_le_firstReturnMass_pow o r n).trans
    (pow_le_pow_left' hENN r)

end Erdos1165.ExternalSharpOnePoint
