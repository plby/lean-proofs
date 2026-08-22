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

import ErdosProblems.Erdos1165.AnnularNestedProfileKernelUpper
import ErdosProblems.Erdos1165.AnnularOffspringKernelLiteralProfile
import ErdosProblems.Erdos1165.AppendixPairMoment

/-!
# Uniform upper loss for the endpoint-integrated profile kernel

The literal radial-row estimate has relative error at most `n⁻⁶` per
letter.  A constrained profile has at most `6 n³` letters, so the whole
upper comparison costs at most `exp 1`.  This is the numerical coefficient
needed when the far-pair reference continuation is summed over its retained
prefix before applying the A.11 tail estimate.
-/

open scoped ENNReal

namespace Erdos1165.AnnularProfileUniformUpperLoss

open AnnularIntegratedProfileKernel AnnularNestedProfileKernel
open AnnularNestedProfileKernelUpper AppendixFirstMoment AppendixPairMoment
open AnnularBoundaryExcursionKernel AnnularOffspringKernelRadial
open AnnularOffspringKernel
open AnnularOffspringKernelLiteralProfile AnnularProfileClocks
open LiteralRealAnnulusRadialExit ProfileAnnularRowRegular ThickPoint
open PathInsertion ProfileGapChain ProfileSmallBall

noncomputable section

/-- Walk-facing upper half of A.6 with the same common `n⁻⁶` error at
every nonterminal profile gap.  Both spatial endpoints of the fresh row are
integrated before this estimate is applied. -/
theorem eventually_literalProfileGapIntegratedMarkedKernel_upper_inv_pow_six :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ k : ℕ, 0 < k → k + 1 ≤ n →
      ∀ (q : ℕ) (center : Point) (u : ProfileCycleMiddlePoint n k center),
        (literalGapIntegratedMarkedKernel
          (profileOuterBoundary n k center)
          (profileInnerBoundary n k center)
          (profileInnerBoundary n (k + 1) center) u.1 q).toReal ≤
            (1 + 1 / (n : ℝ) ^ 6) ^ (q + 1) * halfGeometricMass q := by
  filter_upwards
    [eventually_literalProfileGapIntegratedMarkedKernel_two_sided_regular,
      eventually_profileRegularRowError_le_inv_pow_six,
      Filter.eventually_ge_atTop 2] with n hrow herror hn
  intro k hk0 hk q center u
  let rowError := literalRealAnnulusRowError
    (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))
  obtain ⟨hinner, hmiddle, _houter, _hInnerSep, _hOuterSep,
      hdelta, _hmidpoint⟩ := profile_regular_geometry hn hk0 hk
  have herror0 : 0 ≤ rowError :=
    literalRealAnnulusRowError_nonneg
      (by linarith) (by linarith) hdelta
  have herror' : rowError ≤ 1 / (n : ℝ) ^ 6 := herror k hk0 hk
  have hpow : (1 + rowError) ^ (q + 1) ≤
      (1 + 1 / (n : ℝ) ^ 6) ^ (q + 1) := by
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  exact (hrow k hk0 hk q center u).2.trans
    (mul_le_mul_of_nonneg_right hpow (halfGeometricMass_nonneg q))

/-- The accumulated `n⁻⁶` row error of any constrained radial word is
at most `exp 1`. -/
theorem one_add_inv_pow_six_profileRadialWordLength_le_exp_one
    {n : ℕ} {delta : ℝ} {m : Profile n}
    (hn : 2 ≤ n) (hm : IsConstrainedProfile delta m)
    (hdelta : delta ≤ 1) :
    (1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (profileList m) ≤
      Real.exp 1 := by
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hlengthNat := radialWordLength_profileList_le_six_mul_cube hdelta hm
  have hlength : (radialWordLength (profileList m) : ℝ) ≤
      6 * (n : ℝ) ^ 3 := by
    exact_mod_cast hlengthNat
  have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcube : (6 : ℝ) ≤ (n : ℝ) ^ 3 := by
    have hp : (2 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hnTwo 3
    norm_num at hp ⊢
    linarith
  have hcost :
      (radialWordLength (profileList m) : ℝ) *
          (1 / (n : ℝ) ^ 6) ≤ 1 := by
    have hpow : (n : ℝ) ^ 6 = (n : ℝ) ^ 3 * (n : ℝ) ^ 3 := by
      ring
    have hbound : (radialWordLength (profileList m) : ℝ) ≤
        (n : ℝ) ^ 6 := by
      rw [hpow]
      exact hlength.trans
        (mul_le_mul_of_nonneg_right hcube (pow_nonneg (by positivity) 3))
    calc
      (radialWordLength (profileList m) : ℝ) *
            (1 / (n : ℝ) ^ 6) =
          (radialWordLength (profileList m) : ℝ) / (n : ℝ) ^ 6 := by
            ring
      _ ≤ 1 := (div_le_one (pow_pos hnPos 6)).2 hbound
  exact (pow_one_add_le_exp_nat_mul (by positivity)
      (radialWordLength (profileList m))).trans
    (Real.exp_le_exp.mpr hcost)

/-- A nested endpoint-integrated literal profile sum with row error `n⁻⁶`
is at most `exp 1` times its exact negative-binomial profile weight. -/
theorem nestedENNRealProfileSum_toReal_le_exp_one_mul_profileWeight
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernelENNReal State} {delta : ℝ}
    {n : ℕ} {m : Profile n}
    (hn : 2 ≤ n) (hm : IsConstrainedProfile delta m)
    (hdelta : delta ≤ 1)
    (hedge : ∀ depth a b g entrance next,
      edge depth a b g entrance next ≠ ⊤)
    (hupper : NestedEdgeUpperENNReal (1 / (n : ℝ) ^ 6) edge)
    (depth a : ℕ) (rest : List ℕ)
    (hlist : profileList m = a :: rest)
    (entrance : BoundaryVector State depth a) :
    (∑ chain : GapChain (a :: rest),
        nestedGapChainKernelENNReal edge depth a rest entrance chain).toReal ≤
      Real.exp 1 * profileWeight m := by
  have hraw := nestedENNRealProfileSum_toReal_le_one_add_pow_mul_profileWeight
    hm hdelta (by positivity : 0 ≤ 1 / (n : ℝ) ^ 6)
    hedge hupper depth a rest hlist entrance
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (one_add_inv_pow_six_profileRadialWordLength_le_exp_one hn hm hdelta)
    (profileWeight_nonneg m))

end

end Erdos1165.AnnularProfileUniformUpperLoss
