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

import ErdosProblems.Erdos1165.AnnularNestedProfileKernel

/-!
# Upper bounds for chronologically nested annular profile kernels

The spatial endpoints created at one annular level are the entrance vector
for the next level.  Therefore the A.6 upper comparison must be iterated as a
nested finite sum, not as a product of prematurely integrated scalar rows.
This file supplies the upper counterpart of `AnnularNestedProfileKernel`.

Only a uniform endpoint-integrated row upper bound is used.  No independence
between different levels, stopped-event comparison, or pair estimate is
assumed.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AnnularNestedProfileKernelUpper

open AppendixFirstMoment AnnularIntegratedProfileKernel
open AnnularNestedProfileKernel PathInsertion ProfileGapChain ProfileSmallBall

noncomputable section

/-- Uniform one-level upper comparison after summing the full vector of child
entrance positions, before the deeper continuation is attached. -/
def NestedEdgeUpper
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    (epsilon : ℝ) (edge : NestedEdgeKernel State) : Prop :=
  ∀ depth a b (g : GapPattern a b)
      (entrance : BoundaryVector State depth a),
    (∑ next : BoundaryVector State (depth + 1) b,
        edge depth a b g entrance next) ≤
      (1 + epsilon) ^ (a + b) *
        (∏ i, halfGeometricMass (gapMultiplicity g i))

/-- The nested dynamic program is bounded above by the ideal fixed-chain
mass times the accumulated radial-word loss. -/
theorem nestedGapChainKernel_le_one_add_pow_radialWordLength_mul_gapChainMass :
    ∀ {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
      {edge : NestedEdgeKernel State} {epsilon : ℝ},
      0 ≤ epsilon →
      (∀ depth a b g entrance next,
        0 ≤ edge depth a b g entrance next) →
      NestedEdgeUpper epsilon edge →
      ∀ depth a rest entrance (chain : GapChain (a :: rest)),
        nestedGapChainKernel edge depth a rest entrance chain ≤
          (1 + epsilon) ^ radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain
  | State, _, edge, epsilon, hepsilon0, hedge, hupper,
      _, _, [], _, _ => by
        simp [radialWordLength, gapChainMass, nestedGapChainKernel]
  | State, _, edge, epsilon, hepsilon0, hedge, hupper,
      depth, a, b :: rest, entrance, chain => by
      let headReference : ℝ :=
        (1 + epsilon) ^ (a + b) *
          (∏ i, halfGeometricMass (gapMultiplicity chain.1 i))
      let tailReference : ℝ :=
        (1 + epsilon) ^ radialWordLength (b :: rest) *
          gapChainMass (b :: rest) chain.2
      have hhead :
          (∑ next : BoundaryVector State (depth + 1) b,
              edge depth a b chain.1 entrance next) ≤ headReference :=
        hupper depth a b chain.1 entrance
      have htail (next : BoundaryVector State (depth + 1) b) :
          nestedGapChainKernel edge (depth + 1) b rest next chain.2 ≤
            tailReference :=
        nestedGapChainKernel_le_one_add_pow_radialWordLength_mul_gapChainMass
          hepsilon0 hedge hupper (depth + 1) b rest next chain.2
      have htailReference0 : 0 ≤ tailReference :=
        mul_nonneg (pow_nonneg (by linarith) _)
          (gapChainMass_nonneg chain.2)
      calc
        nestedGapChainKernel edge depth a (b :: rest) entrance chain =
            ∑ next : BoundaryVector State (depth + 1) b,
              edge depth a b chain.1 entrance next *
                nestedGapChainKernel edge (depth + 1) b rest next chain.2 := rfl
        _ ≤ ∑ next : BoundaryVector State (depth + 1) b,
              edge depth a b chain.1 entrance next * tailReference := by
          apply Finset.sum_le_sum
          intro next _
          exact mul_le_mul_of_nonneg_left (htail next)
            (hedge depth a b chain.1 entrance next)
        _ = (∑ next : BoundaryVector State (depth + 1) b,
              edge depth a b chain.1 entrance next) * tailReference := by
          rw [Finset.sum_mul]
        _ ≤ headReference * tailReference :=
          mul_le_mul_of_nonneg_right hhead htailReference0
        _ = (1 + epsilon) ^ radialWordLength (a :: b :: rest) *
              gapChainMass (a :: b :: rest) chain := by
          simp only [headReference, tailReference, radialWordLength,
            gapChainMass, pow_add]
          ring

/-- Summing the nested weak-composition chains gives the exact transition
product with only the accumulated row loss. -/
theorem nestedSum_le_one_add_pow_radialWordLength_mul_transitionProduct
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernel State} {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon)
    (hedge : ∀ depth a b g entrance next,
      0 ≤ edge depth a b g entrance next)
    (hupper : NestedEdgeUpper epsilon edge)
    (depth a : ℕ) (rest : List ℕ)
    (entrance : BoundaryVector State depth a)
    (hpos : ∀ c ∈ a :: rest, 0 < c) :
    (∑ chain : GapChain (a :: rest),
        nestedGapChainKernel edge depth a rest entrance chain) ≤
      (1 + epsilon) ^ radialWordLength (a :: rest) *
        transitionProduct (a :: rest) := by
  rw [← sum_gapChainMass_eq_transitionProduct (a :: rest) hpos,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun chain _ ↦
    nestedGapChainKernel_le_one_add_pow_radialWordLength_mul_gapChainMass
      hepsilon0 hedge hupper depth a rest entrance chain

/-- Constrained-profile specialization of the nested upper comparison. -/
theorem nestedProfileSum_le_one_add_pow_mul_profileWeight
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernel State} {epsilon delta : ℝ}
    {n : ℕ} {m : Profile n}
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1)
    (hepsilon0 : 0 ≤ epsilon)
    (hedge : ∀ depth a b g entrance next,
      0 ≤ edge depth a b g entrance next)
    (hupper : NestedEdgeUpper epsilon edge)
    (depth a : ℕ) (rest : List ℕ)
    (hlist : profileList m = a :: rest)
    (entrance : BoundaryVector State depth a) :
    (∑ chain : GapChain (a :: rest),
        nestedGapChainKernel edge depth a rest entrance chain) ≤
      (1 + epsilon) ^ radialWordLength (profileList m) * profileWeight m := by
  rw [profileWeight, hlist]
  apply nestedSum_le_one_add_pow_radialWordLength_mul_transitionProduct
    hepsilon0 hedge hupper
  intro c hc
  have hc' : c ∈ profileList m := by simpa only [hlist] using hc
  have htwo := constrainedProfile_all_entries_two_le hdelta hm c hc'
  omega

/-! ## Literal ENNReal kernels -/

/-- Row-upper predicate for literal stopped-event kernels. -/
def NestedEdgeUpperENNReal
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    (epsilon : ℝ) (edge : NestedEdgeKernelENNReal State) : Prop :=
  ∀ depth a b (g : GapPattern a b)
      (entrance : BoundaryVector State depth a),
    (∑ next : BoundaryVector State (depth + 1) b,
        (edge depth a b g entrance next).toReal) ≤
      (1 + epsilon) ^ (a + b) *
        (∏ i, halfGeometricMass (gapMultiplicity g i))

/-- Real mass of a literal nested fixed-chain kernel is bounded by its ideal
reference mass. -/
theorem nestedGapChainKernelENNReal_toReal_le_one_add_pow_mul_gapChainMass
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernelENNReal State} {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon)
    (hedge : ∀ depth a b g entrance next,
      edge depth a b g entrance next ≠ ⊤)
    (hupper : NestedEdgeUpperENNReal epsilon edge)
    (depth a : ℕ) (rest : List ℕ)
    (entrance : BoundaryVector State depth a)
    (chain : GapChain (a :: rest)) :
    (nestedGapChainKernelENNReal edge depth a rest entrance chain).toReal ≤
      (1 + epsilon) ^ radialWordLength (a :: rest) *
        gapChainMass (a :: rest) chain := by
  rw [nestedGapChainKernelENNReal_toReal hedge]
  apply nestedGapChainKernel_le_one_add_pow_radialWordLength_mul_gapChainMass
    hepsilon0
  · intro d c e g u v
    exact ENNReal.toReal_nonneg
  · exact hupper

/-- Literal-probability profile upper bound, after summing every nested
weak-composition tree. -/
theorem nestedENNRealProfileSum_toReal_le_one_add_pow_mul_profileWeight
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernelENNReal State} {epsilon delta : ℝ}
    {n : ℕ} {m : Profile n}
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1)
    (hepsilon0 : 0 ≤ epsilon)
    (hedge : ∀ depth a b g entrance next,
      edge depth a b g entrance next ≠ ⊤)
    (hupper : NestedEdgeUpperENNReal epsilon edge)
    (depth a : ℕ) (rest : List ℕ)
    (hlist : profileList m = a :: rest)
    (entrance : BoundaryVector State depth a) :
    (∑ chain : GapChain (a :: rest),
        nestedGapChainKernelENNReal edge depth a rest entrance chain).toReal ≤
      (1 + epsilon) ^ radialWordLength (profileList m) * profileWeight m := by
  rw [ENNReal.toReal_sum]
  · rw [profileWeight, hlist, ← sum_gapChainMass_eq_transitionProduct]
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun chain _ ↦
        nestedGapChainKernelENNReal_toReal_le_one_add_pow_mul_gapChainMass
          hepsilon0 hedge hupper depth a rest entrance chain
    · intro c hc
      have hc' : c ∈ profileList m := by simpa only [hlist] using hc
      have htwo := constrainedProfile_all_entries_two_le hdelta hm c hc'
      omega
  · intro chain _
    exact nestedGapChainKernelENNReal_ne_top hedge
      depth a rest entrance chain

end

end Erdos1165.AnnularNestedProfileKernelUpper
