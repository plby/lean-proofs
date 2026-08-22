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

import ErdosProblems.Erdos1165.AnnularProfileNestedEdge
import ErdosProblems.Erdos1165.AnnularNestedProfileUniformLoss

/-!
# Quantitative lower bound for the concrete nested annular profile kernel

This file combines the exact child-vector marginal with the uniform literal
one-gap radial estimate.  Intermediate endpoints are retained in the nested
dynamic program, while the complete vector marginal at a single level is
the product of its endpoint-integrated parent-gap masses.
-/

open Filter
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularLiteralNestedProfileLower

open AnnularBoundaryExcursionKernel AnnularGapChildVector
open AnnularIntegratedProfileKernel AnnularLiteralProfileRowUniform
open AnnularNestedProfileKernel AnnularNestedProfileUniformLoss
open AnnularOffspringKernel AnnularOffspringKernelRadial
open AnnularProfileClocks AnnularProfileNestedEdge
open AppendixFirstMoment PathInsertion ProfileGapChain ProfileSmallBall
open ThickPoint

noncomputable section

/-- A uniform literal one-parent row estimate implies the corresponding
whole-level child-vector estimate. -/
theorem literalProfileNestedEdgeLowerAt_of_parentRows
    {n depth : ℕ} {center : Point} {epsilon : ℝ}
    (hepsilon1 : epsilon ≤ 1)
    (hparent : ∀ (q : ℕ) (u : ProfileCycleMiddlePoint n (depth + 2) center),
      (1 - epsilon) ^ (q + 1) * halfGeometricMass q ≤
        (literalGapIntegratedMarkedKernel
          (profileOuterBoundary n (depth + 2) center)
          (profileInnerBoundary n (depth + 2) center)
          (profileInnerBoundary n (depth + 3) center) u.1 q).toReal) :
    NestedEdgeLowerAtENNReal epsilon
      (literalProfileNestedEdgeKernelENNReal n center) depth := by
  intro a b g entrance
  have hfinite : ∀ children :
      BoundaryVector (ProfileNestedState n center) (depth + 1) b,
      literalProfileNestedEdgeKernelENNReal n center
        depth a b g entrance children ≠ ⊤ :=
    fun children ↦ literalProfileNestedEdgeKernelENNReal_ne_top
      n center depth a b g entrance children
  rw [← ENNReal.toReal_sum]
  · rw [sum_literalProfileNestedEdgeKernelENNReal_eq_product_integrated]
    rw [ENNReal.toReal_prod]
    · calc
        (1 - epsilon) ^ (a + b) *
              (∏ i : Fin a, halfGeometricMass (gapMultiplicity g i)) =
            ∏ i : Fin a,
              ((1 - epsilon) ^ (gapMultiplicity g i + 1) *
                halfGeometricMass (gapMultiplicity g i)) := by
          have hsum : ∑ i : Fin a, (gapMultiplicity g i + 1) = a + b := by
            rw [Finset.sum_add_distrib, sum_gapMultiplicity]
            simp
            omega
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
        _ ≤ ∏ i : Fin a,
              (literalGapIntegratedMarkedKernel
                (profileOuterBoundary n (depth + 2) center)
                (profileInnerBoundary n (depth + 2) center)
                (profileInnerBoundary n (depth + 3) center)
                (entrance i).1 (gapMultiplicity g i)).toReal := by
          exact Finset.prod_le_prod
            (fun i _ ↦ mul_nonneg
              (pow_nonneg (sub_nonneg.mpr hepsilon1) _)
              (halfGeometricMass_nonneg (gapMultiplicity g i)))
            (fun i _ ↦ hparent (gapMultiplicity g i) (entrance i))
  · intro children _
    exact hfinite children

/-- Eventually every actual internal profile level satisfies the common
`n⁻⁶` whole-level nested edge comparison. -/
theorem eventually_literalProfileNestedEdgeLowerAt_inv_pow_six :
    ∀ᶠ n : ℕ in atTop, ∀ (center : Point) (depth : ℕ), depth + 3 ≤ n →
      NestedEdgeLowerAtENNReal (1 / (n : ℝ) ^ 6)
        (literalProfileNestedEdgeKernelENNReal n center) depth := by
  filter_upwards
    [eventually_literalProfileGapIntegratedMarkedKernel_lower_inv_pow_six,
      eventually_ge_atTop 2] with n hrow hn
  intro center depth hdepth
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  apply literalProfileNestedEdgeLowerAt_of_parentRows
    ((div_le_one (pow_pos hnPos 6)).2 (one_le_pow₀ hnOne))
  intro q u
  exact hrow (depth + 2) (by omega) (by omega) q center u

/-- The complete concrete nested radial hierarchy, summed over every weak
composition tree, has at least half the HLOZ reference profile mass.  The
entrance vector at the first (`k=2`) profile boundary remains arbitrary; it
is supplied later by the initial annular-history factor. -/
theorem eventually_ofReal_half_mul_profileWeight_le_literalNestedSum :
    ∀ᶠ n : ℕ in atTop, ∀ (center : Point) (delta : ℝ) (m : Profile n),
      IsConstrainedProfile delta m → delta ≤ 1 →
      ∀ (a : ℕ) (rest : List ℕ), profileList m = a :: rest →
      ∀ entrance : BoundaryVector (ProfileNestedState n center) 0 a,
        ENNReal.ofReal ((1 / 2 : ℝ) * profileWeight m) ≤
          ∑ chain : GapChain (a :: rest),
            nestedGapChainKernelENNReal
              (literalProfileNestedEdgeKernelENNReal n center)
              0 a rest entrance chain := by
  filter_upwards
    [eventually_literalProfileNestedEdgeLowerAt_inv_pow_six,
      eventually_ge_atTop 3] with n hlower hn
  intro center delta m hm hdelta a rest hlist entrance
  apply ofReal_half_mul_profileWeight_le_nestedSum_on
    hn hm hdelta
    (literalProfileNestedEdgeKernelENNReal_ne_top n center)
    0 a rest hlist
  intro depth _hdepth0 hdepth1
  apply hlower center depth
  have hlength : (profileList m).length = n - 1 := by
    simp [profileList]
  rw [hlist] at hlength
  simp only [List.length_cons] at hlength
  omega

end

end Erdos1165.AnnularLiteralNestedProfileLower
