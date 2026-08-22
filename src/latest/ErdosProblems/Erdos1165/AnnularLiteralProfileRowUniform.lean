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

import ErdosProblems.Erdos1165.AnnularOffspringKernelLiteralProfile
import ErdosProblems.Erdos1165.AnnularIntegratedProfileKernel

/-!
# A common row error for every literal profile gap

The radial estimate naturally supplies a slightly different error at each
profile level.  Eventually every one of those errors is bounded by `n⁻⁶`.
This file records the resulting literal stopped-event comparison with the
single common factor `(1 - n⁻⁶)^(q+1)`, which is the form needed by the
nested child-vector dynamic program.
-/

open Filter

namespace Erdos1165.AnnularLiteralProfileRowUniform

open AnnularBoundaryExcursionKernel AnnularOffspringKernel
open AnnularOffspringKernelRadial
open AnnularIntegratedProfileKernel
open AnnularOffspringKernelLiteralProfile AnnularProfileClocks
open AppendixFirstMoment LiteralRealAnnulusRadialExit
open ProfileAnnularRowRegular ThickPoint

noncomputable section

/-- At every regular profile gap, the actual exact-count stopped-event mass
has the common lower comparison obtained by replacing its level-dependent
row error with `n⁻⁶`. -/
theorem eventually_literalProfileGapIntegratedMarkedKernel_lower_inv_pow_six :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 0 < k → k + 1 ≤ n →
      ∀ (q : ℕ) (center : Point) (u : ProfileCycleMiddlePoint n k center),
        (1 - 1 / (n : ℝ) ^ 6) ^ (q + 1) * halfGeometricMass q ≤
          (literalGapIntegratedMarkedKernel
            (profileOuterBoundary n k center)
            (profileInnerBoundary n k center)
            (profileInnerBoundary n (k + 1) center) u.1 q).toReal := by
  filter_upwards
    [eventually_literalProfileGapIntegratedMarkedKernel_two_sided_regular,
      eventually_profileRegularRowError_le_inv_pow_six,
      eventually_ge_atTop 2] with n hrow herror hn
  intro k hk0 hk q center u
  let rowError := literalRealAnnulusRowError
    (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))
  have hnReal : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hinv0 : 0 ≤ 1 / (n : ℝ) ^ 6 := by positivity
  have hinv1 : 1 / (n : ℝ) ^ 6 ≤ 1 := by
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ hnReal
    exact (div_le_one (by positivity)).2 hpow
  have herror' : rowError ≤ 1 / (n : ℝ) ^ 6 := herror k hk0 hk
  have hpow :
      (1 - 1 / (n : ℝ) ^ 6) ^ (q + 1) ≤
        (1 - rowError) ^ (q + 1) := by
    exact pow_le_pow_left₀ (sub_nonneg.mpr hinv1) (by linarith) _
  calc
    (1 - 1 / (n : ℝ) ^ 6) ^ (q + 1) * halfGeometricMass q ≤
        (1 - rowError) ^ (q + 1) * halfGeometricMass q :=
      mul_le_mul_of_nonneg_right hpow (halfGeometricMass_nonneg q)
    _ ≤ (literalGapIntegratedMarkedKernel
          (profileOuterBoundary n k center)
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) u.1 q).toReal := by
      simpa only [rowError] using (hrow k hk0 hk q center u).1

/-- The common `n⁻⁶` row loss costs at most a factor two over any constrained
profile. -/
theorem one_half_le_one_sub_inv_pow_six_profileRadialWordLength
    {n : ℕ} (hn : 3 ≤ n) {delta : ℝ} {m : Profile n}
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1) :
    (1 / 2 : ℝ) ≤
      (1 - 1 / (n : ℝ) ^ 6) ^ radialWordLength (profileList m) := by
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hinv0 : 0 ≤ 1 / (n : ℝ) ^ 6 := by positivity
  have hinv1 : 1 / (n : ℝ) ^ 6 ≤ 1 := by
    exact (div_le_one (pow_pos hnPos 6)).2 (one_le_pow₀ hnOne)
  have hcube : (12 : ℝ) ≤ (n : ℝ) ^ 3 := by
    have hnThree : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : (3 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hnThree _
    norm_num at hpow ⊢
    linarith
  have hnum : 12 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 6 := by
    calc
      12 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 * (n : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hcube (pow_nonneg (by positivity) _)
      _ = (n : ℝ) ^ 6 := by ring
  have hsmall : 12 * (n : ℝ) ^ 3 * (1 / (n : ℝ) ^ 6) ≤ 1 := by
    calc
      12 * (n : ℝ) ^ 3 * (1 / (n : ℝ) ^ 6) =
          (12 * (n : ℝ) ^ 3) / (n : ℝ) ^ 6 := by ring
      _ ≤ 1 := (div_le_one (pow_pos hnPos 6)).2 hnum
  exact one_half_le_one_sub_pow_profileRadialWordLength
    hinv0 hinv1 hsmall hm hdelta

end

end Erdos1165.AnnularLiteralProfileRowUniform
