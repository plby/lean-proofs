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

import ErdosProblems.Erdos1165.AnnularIntegratedProfileKernel

/-!
# Upper endpoint-integrated kernel bound along a complete profile

`AnnularIntegratedProfileKernel` contains the lower half of the A.6
comparison.  The far-pair argument also needs the source-correct upper half:
spatial endpoints are summed at every fresh annular row, the resulting
scalar row estimates are multiplied along a radial word, and only then are
all weak-composition words summed.

This file supplies that finite algebra.  It does not assert any stopped
event comparison; its hypotheses are literal one-row inequalities for the
endpoint-integrated edge kernel.
-/

open scoped BigOperators

namespace Erdos1165.AnnularIntegratedProfileKernelUpper

open AppendixFirstMoment AnnularIntegratedProfileKernel
open PathInsertion ProfileGapChain ProfileSmallBall

noncomputable section

/-- Pointwise multiplication of endpoint-integrated one-level upper bounds
along one fixed weak-composition chain. -/
theorem integratedGapChainKernel_le_one_add_pow_radialWordLength :
    ∀ {edge : ℕ → (a b : ℕ) → GapPattern a b → ℝ}
      {epsilon : ℝ},
      0 ≤ epsilon →
      (∀ depth a b g, 0 ≤ edge depth a b g) →
      (∀ depth a b (g : GapPattern a b),
        edge depth a b g ≤
          (1 + epsilon) ^ (a + b) *
            (∏ i, halfGeometricMass (gapMultiplicity g i))) →
      ∀ depth values (chain : GapChain values),
        integratedGapChainKernel edge depth values chain ≤
          (1 + epsilon) ^ radialWordLength values *
            gapChainMass values chain
  | edge, epsilon, hepsilon0, hedge, hupper, _, [], _ => by
      simp [radialWordLength, gapChainMass, integratedGapChainKernel]
  | edge, epsilon, hepsilon0, hedge, hupper, _, [_], _ => by
      simp [radialWordLength, gapChainMass, integratedGapChainKernel]
  | edge, epsilon, hepsilon0, hedge, hupper,
      depth, a :: b :: rest, chain => by
      have hhead := hupper depth a b chain.1
      have htail := integratedGapChainKernel_le_one_add_pow_radialWordLength
        hepsilon0 hedge hupper (depth + 1) (b :: rest) chain.2
      have hheadUpper0 : 0 ≤ (1 + epsilon) ^ (a + b) *
          (∏ i, halfGeometricMass (gapMultiplicity chain.1 i)) :=
        mul_nonneg (pow_nonneg (by linarith) _)
          (Finset.prod_nonneg fun _ _ ↦ halfGeometricMass_nonneg _)
      have htailActual0 : 0 ≤
          integratedGapChainKernel edge (depth + 1) (b :: rest) chain.2 :=
        integratedGapChainKernel_nonneg hedge (depth + 1)
          (b :: rest) chain.2
      calc
        integratedGapChainKernel edge depth (a :: b :: rest) chain =
            edge depth a b chain.1 *
              integratedGapChainKernel edge (depth + 1)
                (b :: rest) chain.2 := rfl
        _ ≤ ((1 + epsilon) ^ (a + b) *
              (∏ i, halfGeometricMass (gapMultiplicity chain.1 i))) *
            ((1 + epsilon) ^ radialWordLength (b :: rest) *
              gapChainMass (b :: rest) chain.2) :=
          mul_le_mul hhead htail htailActual0 hheadUpper0
        _ = (1 + epsilon) ^ radialWordLength (a :: b :: rest) *
              gapChainMass (a :: b :: rest) chain := by
          simp only [radialWordLength, gapChainMass, pow_add]
          ring

/-- Summing every endpoint-integrated radial word gives at most the exact
negative-binomial transition product times the accumulated row loss. -/
theorem sum_integratedGapChainKernel_le_one_add_pow_mul_transitionProduct
    {edge : ℕ → (a b : ℕ) → GapPattern a b → ℝ}
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon)
    (hedge : ∀ depth a b g, 0 ≤ edge depth a b g)
    (hupper : ∀ depth a b (g : GapPattern a b),
      edge depth a b g ≤
        (1 + epsilon) ^ (a + b) *
          (∏ i, halfGeometricMass (gapMultiplicity g i)))
    (depth : ℕ) (values : List ℕ)
    (hpos : ∀ a ∈ values, 0 < a) :
    (∑ chain : GapChain values,
        integratedGapChainKernel edge depth values chain) ≤
      (1 + epsilon) ^ radialWordLength values * transitionProduct values := by
  rw [← sum_gapChainMass_eq_transitionProduct values hpos,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun chain _ ↦
    integratedGapChainKernel_le_one_add_pow_radialWordLength
      hepsilon0 hedge hupper depth values chain

/-- Profile specialization of the endpoint-integrated A.6 upper bound. -/
theorem sum_integratedGapChainKernel_profile_le_one_add_pow_mul_profileWeight
    {n : ℕ} {delta epsilon : ℝ} {m : Profile n}
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1)
    (hepsilon0 : 0 ≤ epsilon)
    {edge : ℕ → (a b : ℕ) → GapPattern a b → ℝ}
    (hedge : ∀ depth a b g, 0 ≤ edge depth a b g)
    (hupper : ∀ depth a b (g : GapPattern a b),
      edge depth a b g ≤
        (1 + epsilon) ^ (a + b) *
          (∏ i, halfGeometricMass (gapMultiplicity g i)))
    (depth : ℕ) :
    (∑ chain : GapChain (profileList m),
        integratedGapChainKernel edge depth (profileList m) chain) ≤
      (1 + epsilon) ^ radialWordLength (profileList m) * profileWeight m := by
  apply sum_integratedGapChainKernel_le_one_add_pow_mul_transitionProduct
    hepsilon0 hedge hupper
  intro a ha
  have hatwo := constrainedProfile_all_entries_two_le hdelta hm a ha
  omega

end

end Erdos1165.AnnularIntegratedProfileKernelUpper
