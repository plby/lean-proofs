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
import ErdosProblems.Erdos1165.AnnularProfileUniformUpperLoss
import ErdosProblems.Erdos1165.AnnularRadialProfileWords

/-!
# Literal upper bound for the nested annular profile kernel

This is the upper counterpart of `AnnularLiteralNestedProfileLower`.  The
row estimate is used only at the depths actually traversed by the finite
profile, rather than being imposed at meaningless depths beyond scale `n`.
The resulting theorem is entirely walk-facing: its edge is the literal
stopped-event kernel `literalProfileNestedEdgeKernelENNReal`.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularLiteralNestedProfileUpper

open AnnularBoundaryExcursionKernel AnnularIntegratedProfileKernel
open AnnularNestedProfileKernel
open AnnularNestedProfileKernelUpper AnnularOffspringKernel
open AnnularOffspringKernelRadial AnnularProfileNestedEdge
open AnnularProfileClocks AnnularProfileUniformUpperLoss
open AnnularRadialProfileWords AppendixFirstMoment PathInsertion
open ProfileGapChain ProfileSmallBall ThickPoint

noncomputable section

/-- Upper row comparison at one specified nested depth. -/
def NestedEdgeUpperAtENNReal
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    (epsilon : ℝ) (edge : NestedEdgeKernelENNReal State) (depth : ℕ) : Prop :=
  ∀ a b (g : GapPattern a b)
      (entrance : BoundaryVector State depth a),
    (∑ next : BoundaryVector State (depth + 1) b,
        (edge depth a b g entrance next).toReal) ≤
      (1 + epsilon) ^ (a + b) *
        (∏ i, halfGeometricMass (gapMultiplicity g i))

/-- A uniform literal one-parent upper row implies the whole-level
child-vector upper estimate. -/
theorem literalProfileNestedEdgeUpperAt_of_parentRows
    {n depth : ℕ} {center : Point} {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon)
    (hparent : ∀ (q : ℕ) (u : ProfileCycleMiddlePoint n (depth + 2) center),
      (literalGapIntegratedMarkedKernel
        (profileOuterBoundary n (depth + 2) center)
        (profileInnerBoundary n (depth + 2) center)
        (profileInnerBoundary n (depth + 3) center) u.1 q).toReal ≤
          (1 + epsilon) ^ (q + 1) * halfGeometricMass q) :
    NestedEdgeUpperAtENNReal epsilon
      (literalProfileNestedEdgeKernelENNReal n center) depth := by
  intro a b g entrance
  rw [← ENNReal.toReal_sum]
  · rw [sum_literalProfileNestedEdgeKernelENNReal_eq_product_integrated]
    rw [ENNReal.toReal_prod]
    · calc
        ∏ i : Fin a,
            (literalGapIntegratedMarkedKernel
              (profileOuterBoundary n (depth + 2) center)
              (profileInnerBoundary n (depth + 2) center)
              (profileInnerBoundary n (depth + 3) center)
              (entrance i).1 (gapMultiplicity g i)).toReal ≤
            ∏ i : Fin a,
              ((1 + epsilon) ^ (gapMultiplicity g i + 1) *
                halfGeometricMass (gapMultiplicity g i)) := by
          exact Finset.prod_le_prod
            (fun i _ ↦ ENNReal.toReal_nonneg)
            (fun i _ ↦ hparent (gapMultiplicity g i) (entrance i))
        _ = (1 + epsilon) ^ (a + b) *
              (∏ i : Fin a, halfGeometricMass (gapMultiplicity g i)) := by
          have hsum : ∑ i : Fin a, (gapMultiplicity g i + 1) = a + b := by
            rw [Finset.sum_add_distrib, sum_gapMultiplicity]
            simp
            omega
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  · intro children _
    exact literalProfileNestedEdgeKernelENNReal_ne_top
      n center depth a b g entrance children

/-- Eventually every actual internal level satisfies the common literal
`n⁻⁶` upper comparison. -/
theorem eventually_literalProfileNestedEdgeUpperAt_inv_pow_six :
    ∀ᶠ n : ℕ in atTop, ∀ (center : Point) (depth : ℕ), depth + 3 ≤ n →
      NestedEdgeUpperAtENNReal (1 / (n : ℝ) ^ 6)
        (literalProfileNestedEdgeKernelENNReal n center) depth := by
  filter_upwards
    [eventually_literalProfileGapIntegratedMarkedKernel_upper_inv_pow_six]
      with n hrow
  intro center depth hdepth
  apply literalProfileNestedEdgeUpperAt_of_parentRows (by positivity)
  intro q u
  exact hrow (depth + 2) (by omega) (by omega) q center u

/-- The depth-local version of the nested upper induction. -/
theorem nestedGapChainKernelENNReal_toReal_le_on :
    ∀ {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
      {edge : NestedEdgeKernelENNReal State} {epsilon : ℝ},
      0 ≤ epsilon →
      (∀ depth a b g entrance next,
        edge depth a b g entrance next ≠ ⊤) →
      ∀ depth a rest,
      (∀ d, depth ≤ d → d < depth + rest.length →
        NestedEdgeUpperAtENNReal epsilon edge d) →
      ∀ entrance (chain : GapChain (a :: rest)),
        (nestedGapChainKernelENNReal edge depth a rest entrance chain).toReal ≤
          (1 + epsilon) ^ radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain
  | State, _, edge, epsilon, hepsilon0, hedge, depth, a, [], _hupper,
      entrance, chain => by
        simp [nestedGapChainKernelENNReal, radialWordLength, gapChainMass]
  | State, _, edge, epsilon, hepsilon0, hedge, depth, a, b :: rest, hupper,
      entrance, chain => by
      let headReference : ℝ :=
        (1 + epsilon) ^ (a + b) *
          (∏ i, halfGeometricMass (gapMultiplicity chain.1 i))
      let tailReference : ℝ :=
        (1 + epsilon) ^ radialWordLength (b :: rest) *
          gapChainMass (b :: rest) chain.2
      have hhead :
          (∑ next : BoundaryVector State (depth + 1) b,
              (edge depth a b chain.1 entrance next).toReal) ≤
            headReference :=
        hupper depth le_rfl (by simp) a b chain.1 entrance
      have htail (next : BoundaryVector State (depth + 1) b) :
          (nestedGapChainKernelENNReal edge (depth + 1) b rest next
              chain.2).toReal ≤ tailReference := by
        apply nestedGapChainKernelENNReal_toReal_le_on hepsilon0 hedge
        intro d hd hlt
        apply hupper d (by omega)
        simp only [List.length_cons] at hlt ⊢
        omega
      have hfinite (next : BoundaryVector State (depth + 1) b) :
          edge depth a b chain.1 entrance next *
              nestedGapChainKernelENNReal edge (depth + 1) b rest next
                chain.2 ≠ ⊤ := by
        exact ENNReal.mul_ne_top
          (hedge depth a b chain.1 entrance next)
          (nestedGapChainKernelENNReal_ne_top hedge
            (depth + 1) b rest next chain.2)
      have htail0 : 0 ≤ tailReference :=
        mul_nonneg (pow_nonneg (by linarith) _)
          (gapChainMass_nonneg chain.2)
      rw [nestedGapChainKernelENNReal,
        ENNReal.toReal_sum (fun next _ ↦ hfinite next)]
      calc
        ∑ next : BoundaryVector State (depth + 1) b,
            (edge depth a b chain.1 entrance next *
              nestedGapChainKernelENNReal edge (depth + 1) b rest next
                chain.2).toReal =
            ∑ next : BoundaryVector State (depth + 1) b,
              (edge depth a b chain.1 entrance next).toReal *
                (nestedGapChainKernelENNReal edge (depth + 1) b rest next
                  chain.2).toReal := by
              apply Finset.sum_congr rfl
              intro next _
              rw [ENNReal.toReal_mul]
        _ ≤ ∑ next : BoundaryVector State (depth + 1) b,
              (edge depth a b chain.1 entrance next).toReal *
                tailReference := by
              apply Finset.sum_le_sum
              intro next _
              exact mul_le_mul_of_nonneg_left (htail next) ENNReal.toReal_nonneg
        _ = (∑ next : BoundaryVector State (depth + 1) b,
              (edge depth a b chain.1 entrance next).toReal) *
                tailReference := by rw [Finset.sum_mul]
        _ ≤ headReference * tailReference :=
          mul_le_mul_of_nonneg_right hhead htail0
        _ = (1 + epsilon) ^ radialWordLength (a :: b :: rest) *
              gapChainMass (a :: b :: rest) chain := by
          simp only [headReference, tailReference, radialWordLength,
            gapChainMass, pow_add]
          ring

/-- Complete depth-local constrained-profile upper bound. -/
theorem nestedENNRealProfileSum_toReal_le_exp_one_mul_profileWeight_on
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernelENNReal State} {delta : ℝ}
    {n : ℕ} {m : Profile n}
    (hn : 2 ≤ n) (hm : IsConstrainedProfile delta m)
    (hdelta : delta ≤ 1)
    (hedge : ∀ depth a b g entrance next,
      edge depth a b g entrance next ≠ ⊤)
    (depth a : ℕ) (rest : List ℕ)
    (hlist : profileList m = a :: rest)
    (hupper : ∀ d, depth ≤ d → d < depth + rest.length →
      NestedEdgeUpperAtENNReal (1 / (n : ℝ) ^ 6) edge d)
    (entrance : BoundaryVector State depth a) :
    (∑ chain : GapChain (a :: rest),
        nestedGapChainKernelENNReal edge depth a rest entrance chain).toReal ≤
      Real.exp 1 * profileWeight m := by
  rw [ENNReal.toReal_sum]
  · have hraw :
        ∑ chain : GapChain (a :: rest),
            (nestedGapChainKernelENNReal edge depth a rest entrance chain).toReal ≤
          (1 + 1 / (n : ℝ) ^ 6) ^ radialWordLength (profileList m) *
            profileWeight m := by
      rw [← sum_gapChainMass_profile_eq_profileWeight hdelta hm]
      rw [hlist, Finset.mul_sum]
      exact Finset.sum_le_sum fun chain _ ↦
        nestedGapChainKernelENNReal_toReal_le_on (by positivity) hedge
          depth a rest hupper entrance chain
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (one_add_inv_pow_six_profileRadialWordLength_le_exp_one
        hn hm hdelta)
      (profileWeight_nonneg m))
  · intro chain _
    exact nestedGapChainKernelENNReal_ne_top hedge
      depth a rest entrance chain

/-- Walk-facing specialization for the literal profile hierarchy. -/
theorem eventually_literalNestedProfileSum_toReal_le_exp_one_mul_profileWeight :
    ∀ᶠ n : ℕ in atTop, ∀ (center : Point) (delta : ℝ) (m : Profile n),
      IsConstrainedProfile delta m → delta ≤ 1 →
      ∀ (a : ℕ) (rest : List ℕ), profileList m = a :: rest →
      ∀ entrance : BoundaryVector (ProfileNestedState n center) 0 a,
        (∑ chain : GapChain (a :: rest),
          nestedGapChainKernelENNReal
            (literalProfileNestedEdgeKernelENNReal n center)
            0 a rest entrance chain).toReal ≤
          Real.exp 1 * profileWeight m := by
  filter_upwards [eventually_literalProfileNestedEdgeUpperAt_inv_pow_six,
    eventually_ge_atTop 2] with n hupper hn
  intro center delta m hm hdelta a rest hlist entrance
  apply nestedENNRealProfileSum_toReal_le_exp_one_mul_profileWeight_on
    hn hm hdelta (literalProfileNestedEdgeKernelENNReal_ne_top n center)
      0 a rest hlist _ entrance
  intro depth _hdepth0 hdepth
  apply hupper center depth
  have hlength : (profileList m).length = n - 1 := by
    simp [profileList]
  rw [hlist] at hlength
  simp only [List.length_cons] at hlength
  omega

/-! ## The omitted first transition absorbs the uniform row loss -/

/-- The forced first parent has at least two children in every constrained
profile, so its exact critical offspring mass is at most `1/8`. -/
theorem firstProfileTransitionMass_le_one_eighth
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    firstProfileTransitionMass hn m ≤ 1 / 8 := by
  let i : Fin (n - 1) := ⟨0, by omega⟩
  have htwo : 2 ≤ m i := by
    exact constrainedProfile_all_entries_two_le hdelta hm (m i) (by
      simp [profileList])
  rw [firstProfileTransitionMass, transitionMass_formula (by omega)]
  have hi : m ⟨0, by omega⟩ = m i := rfl
  rw [hi, show 1 + m i - 1 = m i by omega, Nat.choose_self]
  norm_num only [Nat.cast_one, one_mul]
  have hpow : (8 : ℝ) ≤ 2 ^ (m i + 1) := by
    calc
      (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
      _ ≤ 2 ^ (m i + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hden : (0 : ℝ) < 2 ^ (m i + 1) := by positivity
  rw [show 1 + m i = m i + 1 by omega]
  exact one_div_le_one_div_of_le (by norm_num) hpow

/-- The first transition pays for the complete `exp 1` upper loss of the
remaining literal nested hierarchy. -/
theorem exp_one_mul_firstProfileTransitionMass_le_one
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    Real.exp 1 * firstProfileTransitionMass hn m ≤ 1 := by
  have hfirst := firstProfileTransitionMass_le_one_eighth hn hdelta hm
  have hexp : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hnonneg : 0 ≤ firstProfileTransitionMass hn m := by
    unfold firstProfileTransitionMass
    exact transitionMass_nonneg _ _
  calc
    Real.exp 1 * firstProfileTransitionMass hn m ≤
        3 * (1 / 8 : ℝ) := mul_le_mul hexp hfirst hnonneg (by norm_num)
    _ ≤ 1 := by norm_num

theorem firstProfileTransitionMass_mul_exp_one_mul_profileWeight_le
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    firstProfileTransitionMass hn m * (Real.exp 1 * profileWeight m) ≤
      profileWeight m := by
  have hweight := profileWeight_nonneg m
  calc
    firstProfileTransitionMass hn m * (Real.exp 1 * profileWeight m) =
        (Real.exp 1 * firstProfileTransitionMass hn m) * profileWeight m := by
          ring
    _ ≤ 1 * profileWeight m :=
      mul_le_mul_of_nonneg_right
        (exp_one_mul_firstProfileTransitionMass_le_one hn hdelta hm) hweight
    _ = profileWeight m := one_mul _

end

end Erdos1165.AnnularLiteralNestedProfileUpper
