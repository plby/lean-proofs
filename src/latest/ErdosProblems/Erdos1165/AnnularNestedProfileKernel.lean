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
# Nested endpoint-integrated profile kernels

The radial words at successive Appendix-A.6 levels are chronologically
nested.  Thus their masses are not a product of independent scalar
one-level kernels.  At each level one must retain the entire vector of child
entrance positions, multiply by the continuation conditional on that vector,
and only then sum the vector.

This file formalizes that dynamic program for a family of finite boundary
state spaces.  Its main estimate uses only a uniform endpoint-integrated
one-level lower bound.  Consequently all intermediate endpoints are
integrated in the source-correct order, while the entrance vector needed by
the next radial level remains available until its continuation has been
attached.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AnnularNestedProfileKernel

open AppendixFirstMoment AnnularIntegratedProfileKernel PathInsertion
  ProfileGapChain ProfileSmallBall

noncomputable section

/-- A boundary-state vector for all excursions at one radial level. -/
abbrev BoundaryVector (State : ℕ → Type*) (depth population : ℕ) :=
  Fin population → State depth

/-- A one-level kernel retains the complete next-level entrance vector.
Summing that vector gives the endpoint-integrated radial-word mass. -/
abbrev NestedEdgeKernel (State : ℕ → Type*) :=
  (depth a b : ℕ) → GapPattern a b →
    BoundaryVector State depth a →
    BoundaryVector State (depth + 1) b → ℝ

/-- Chronologically nested mass for a fixed chain of weak compositions.
The recursive sum is deliberately inside the multiplication by the deeper
continuation. -/
def nestedGapChainKernel
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    (edge : NestedEdgeKernel State) :
    (depth a : ℕ) → (rest : List ℕ) →
      BoundaryVector State depth a → GapChain (a :: rest) → ℝ
  | _, _, [], _, _ => 1
  | depth, a, b :: rest, entrance, chain =>
      ∑ next : BoundaryVector State (depth + 1) b,
        edge depth a b chain.1 entrance next *
          nestedGapChainKernel edge (depth + 1) b rest next chain.2

lemma nestedGapChainKernel_nonneg
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernel State}
    (hedge : ∀ depth a b g entrance next,
      0 ≤ edge depth a b g entrance next) :
    ∀ depth a rest entrance (chain : GapChain (a :: rest)),
      0 ≤ nestedGapChainKernel edge depth a rest entrance chain
  | _, _, [], _, _ => by simp [nestedGapChainKernel]
  | depth, a, b :: rest, entrance, chain => by
      exact Finset.sum_nonneg fun next _ ↦
        mul_nonneg (hedge depth a b chain.1 entrance next)
          (nestedGapChainKernel_nonneg hedge (depth + 1) b rest next chain.2)

/-- Uniform one-level lower comparison, after summing the complete vector
of random child entrances but before attaching the deeper continuation. -/
def NestedEdgeLower
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    (epsilon : ℝ) (edge : NestedEdgeKernel State) : Prop :=
  ∀ depth a b (g : GapPattern a b)
      (entrance : BoundaryVector State depth a),
    (1 - epsilon) ^ (a + b) *
        (∏ i, halfGeometricMass (gapMultiplicity g i)) ≤
      ∑ next : BoundaryVector State (depth + 1) b,
        edge depth a b g entrance next

/-- The one-level row comparison at one specified depth.  This local form
is useful for an actual finite profile, whose analytic estimate is only
needed at the depths occurring in that profile. -/
def NestedEdgeLowerAt
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    (epsilon : ℝ) (edge : NestedEdgeKernel State) (depth : ℕ) : Prop :=
  ∀ a b (g : GapPattern a b)
      (entrance : BoundaryVector State depth a),
    (1 - epsilon) ^ (a + b) *
        (∏ i, halfGeometricMass (gapMultiplicity g i)) ≤
      ∑ next : BoundaryVector State (depth + 1) b,
        edge depth a b g entrance next

/-- The nested dynamic program has the same lower bound as the formal
product of one-level integrated comparisons.  The proof is a finite Tonelli
argument: apply the continuation bound pointwise in the retained child
vector, then its one-level row bound. -/
theorem one_sub_pow_radialWordLength_mul_gapChainMass_le_nested
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernel State} {epsilon : ℝ}
    (hepsilon1 : epsilon ≤ 1)
    (hedge : ∀ depth a b g entrance next,
      0 ≤ edge depth a b g entrance next)
    (hlower : NestedEdgeLower epsilon edge) :
    ∀ depth a rest entrance (chain : GapChain (a :: rest)),
      (1 - epsilon) ^ radialWordLength (a :: rest) *
          gapChainMass (a :: rest) chain ≤
        nestedGapChainKernel edge depth a rest entrance chain
  | _, _, [], _, _ => by
      simp [radialWordLength, gapChainMass, nestedGapChainKernel]
  | depth, a, b :: rest, entrance, chain => by
      let headReference : ℝ :=
        (1 - epsilon) ^ (a + b) *
          (∏ i, halfGeometricMass (gapMultiplicity chain.1 i))
      let tailReference : ℝ :=
        (1 - epsilon) ^ radialWordLength (b :: rest) *
          gapChainMass (b :: rest) chain.2
      have hhead : headReference ≤
          ∑ next : BoundaryVector State (depth + 1) b,
            edge depth a b chain.1 entrance next :=
        hlower depth a b chain.1 entrance
      have htail (next : BoundaryVector State (depth + 1) b) :
          tailReference ≤
            nestedGapChainKernel edge (depth + 1) b rest next chain.2 :=
        one_sub_pow_radialWordLength_mul_gapChainMass_le_nested
          hepsilon1 hedge hlower (depth + 1) b rest next chain.2
      have htail0 : 0 ≤ tailReference := by
        exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hepsilon1) _)
          (gapChainMass_nonneg chain.2)
      calc
        (1 - epsilon) ^ radialWordLength (a :: b :: rest) *
              gapChainMass (a :: b :: rest) chain =
            headReference * tailReference := by
              simp only [headReference, tailReference, radialWordLength,
                gapChainMass, pow_add]
              ring
        _ ≤ (∑ next : BoundaryVector State (depth + 1) b,
              edge depth a b chain.1 entrance next) * tailReference :=
          mul_le_mul_of_nonneg_right hhead htail0
        _ = ∑ next : BoundaryVector State (depth + 1) b,
              edge depth a b chain.1 entrance next * tailReference := by
          rw [Finset.sum_mul]
        _ ≤ ∑ next : BoundaryVector State (depth + 1) b,
              edge depth a b chain.1 entrance next *
                nestedGapChainKernel edge (depth + 1) b rest next chain.2 := by
          apply Finset.sum_le_sum
          intro next _
          exact mul_le_mul_of_nonneg_left (htail next)
            (hedge depth a b chain.1 entrance next)
        _ = nestedGapChainKernel edge depth a (b :: rest) entrance chain := rfl

/-- Finite-depth version of the nested lower estimate.  Only the edge rows
actually visited by the given list are assumed. -/
theorem one_sub_pow_radialWordLength_mul_gapChainMass_le_nested_on :
    ∀ {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
      {edge : NestedEdgeKernel State} {epsilon : ℝ}
      (hepsilon1 : epsilon ≤ 1)
      (hedge : ∀ depth a b g entrance next,
        0 ≤ edge depth a b g entrance next)
      (first : ℕ) (rest : List ℕ),
      (∀ depth, first ≤ depth → depth < first + rest.length →
        NestedEdgeLowerAt epsilon edge depth) →
      ∀ a entrance (chain : GapChain (a :: rest)),
        (1 - epsilon) ^ radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain ≤
          nestedGapChainKernel edge first a rest entrance chain
  | State, _, edge, epsilon, hepsilon1, hedge, first, [], _, a,
      entrance, chain => by
        simp [radialWordLength, gapChainMass, nestedGapChainKernel]
  | State, _, edge, epsilon, hepsilon1, hedge, first, b :: rest, hlower, a,
      entrance, chain => by
      let headReference : ℝ :=
        (1 - epsilon) ^ (a + b) *
          (∏ i, halfGeometricMass (gapMultiplicity chain.1 i))
      let tailReference : ℝ :=
        (1 - epsilon) ^ radialWordLength (b :: rest) *
          gapChainMass (b :: rest) chain.2
      have hhead : headReference ≤
          ∑ next : BoundaryVector State (first + 1) b,
            edge first a b chain.1 entrance next := by
        exact hlower first le_rfl (by simp) a b chain.1 entrance
      have hlowerTail : ∀ depth, first + 1 ≤ depth →
          depth < first + 1 + rest.length →
          NestedEdgeLowerAt epsilon edge depth := by
        intro depth hdepth0 hdepth1
        apply hlower depth
        · omega
        · simp only [List.length_cons]
          omega
      have htail (next : BoundaryVector State (first + 1) b) :
          tailReference ≤
            nestedGapChainKernel edge (first + 1) b rest next chain.2 :=
        one_sub_pow_radialWordLength_mul_gapChainMass_le_nested_on
          hepsilon1 hedge (first + 1) rest hlowerTail b next chain.2
      have htail0 : 0 ≤ tailReference :=
        mul_nonneg (pow_nonneg (sub_nonneg.mpr hepsilon1) _)
          (gapChainMass_nonneg chain.2)
      calc
        (1 - epsilon) ^ radialWordLength (a :: b :: rest) *
              gapChainMass (a :: b :: rest) chain =
            headReference * tailReference := by
              simp only [headReference, tailReference, radialWordLength,
                gapChainMass, pow_add]
              ring
        _ ≤ (∑ next : BoundaryVector State (first + 1) b,
              edge first a b chain.1 entrance next) * tailReference :=
          mul_le_mul_of_nonneg_right hhead htail0
        _ = ∑ next : BoundaryVector State (first + 1) b,
              edge first a b chain.1 entrance next * tailReference := by
          rw [Finset.sum_mul]
        _ ≤ ∑ next : BoundaryVector State (first + 1) b,
              edge first a b chain.1 entrance next *
                nestedGapChainKernel edge (first + 1) b rest next chain.2 := by
          apply Finset.sum_le_sum
          intro next _
          exact mul_le_mul_of_nonneg_left (htail next)
            (hedge first a b chain.1 entrance next)
        _ = nestedGapChainKernel edge first a (b :: rest) entrance chain := rfl

/-- Summing every nested weak-composition chain produces the exact
negative-binomial transition product, with the accumulated radial-word
loss. -/
theorem one_sub_pow_radialWordLength_mul_transitionProduct_le_nestedSum
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernel State} {epsilon : ℝ}
    (hepsilon1 : epsilon ≤ 1)
    (hedge : ∀ depth a b g entrance next,
      0 ≤ edge depth a b g entrance next)
    (hlower : NestedEdgeLower epsilon edge)
    (depth a : ℕ) (rest : List ℕ)
    (entrance : BoundaryVector State depth a)
    (hpos : ∀ c ∈ a :: rest, 0 < c) :
    (1 - epsilon) ^ radialWordLength (a :: rest) *
        transitionProduct (a :: rest) ≤
      ∑ chain : GapChain (a :: rest),
        nestedGapChainKernel edge depth a rest entrance chain := by
  rw [← sum_gapChainMass_eq_transitionProduct (a :: rest) hpos,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun chain _ ↦
    one_sub_pow_radialWordLength_mul_gapChainMass_le_nested
      hepsilon1 hedge hlower depth a rest entrance chain

/-- Profile specialization of the nested endpoint-integrated estimate. -/
theorem one_sub_pow_profileRadialWordLength_mul_profileWeight_le_nestedSum
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernel State} {epsilon delta : ℝ}
    {n : ℕ} {m : Profile n}
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1)
    (hepsilon1 : epsilon ≤ 1)
    (hedge : ∀ depth a b g entrance next,
      0 ≤ edge depth a b g entrance next)
    (hlower : NestedEdgeLower epsilon edge)
    (depth a : ℕ) (rest : List ℕ)
    (hlist : profileList m = a :: rest)
    (entrance : BoundaryVector State depth a) :
    (1 - epsilon) ^ radialWordLength (profileList m) * profileWeight m ≤
      ∑ chain : GapChain (a :: rest),
        nestedGapChainKernel edge depth a rest entrance chain := by
  rw [profileWeight, hlist]
  apply one_sub_pow_radialWordLength_mul_transitionProduct_le_nestedSum
    hepsilon1 hedge hlower depth a rest entrance
  intro c hc
  have hc' : c ∈ profileList m := by simpa only [hlist] using hc
  have htwo := constrainedProfile_all_entries_two_le hdelta hm c hc'
  omega

/-! ## ENNReal kernels supplied by literal stopped events -/

/-- ENNReal version of a one-level kernel retaining the complete child
entrance vector.  Literal stopped-event probabilities naturally have this
codomain. -/
abbrev NestedEdgeKernelENNReal (State : ℕ → Type*) :=
  (depth a b : ℕ) → GapPattern a b →
    BoundaryVector State depth a →
    BoundaryVector State (depth + 1) b → ℝ≥0∞

/-- Nested literal mass, with every finite child-boundary vector integrated
only after its continuation has been attached. -/
def nestedGapChainKernelENNReal
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    (edge : NestedEdgeKernelENNReal State) :
    (depth a : ℕ) → (rest : List ℕ) →
      BoundaryVector State depth a → GapChain (a :: rest) → ℝ≥0∞
  | _, _, [], _, _ => 1
  | depth, a, b :: rest, entrance, chain =>
      ∑ next : BoundaryVector State (depth + 1) b,
        edge depth a b chain.1 entrance next *
          nestedGapChainKernelENNReal edge
            (depth + 1) b rest next chain.2

theorem nestedGapChainKernelENNReal_ne_top
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernelENNReal State}
    (hedge : ∀ depth a b g entrance next,
      edge depth a b g entrance next ≠ ⊤) :
    ∀ depth a rest entrance (chain : GapChain (a :: rest)),
      nestedGapChainKernelENNReal edge depth a rest entrance chain ≠ ⊤
  | _, _, [], _, _ => by simp [nestedGapChainKernelENNReal]
  | depth, a, b :: rest, entrance, chain => by
      rw [nestedGapChainKernelENNReal]
      exact ENNReal.sum_ne_top.mpr fun next _ ↦
        ENNReal.mul_ne_top (hedge depth a b chain.1 entrance next)
          (nestedGapChainKernelENNReal_ne_top hedge
            (depth + 1) b rest next chain.2)

/-- Taking real parts commutes with the finite nested dynamic program. -/
theorem nestedGapChainKernelENNReal_toReal
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernelENNReal State}
    (hedge : ∀ depth a b g entrance next,
      edge depth a b g entrance next ≠ ⊤) :
    ∀ depth a rest entrance (chain : GapChain (a :: rest)),
      (nestedGapChainKernelENNReal edge depth a rest entrance chain).toReal =
        nestedGapChainKernel
          (fun depth a b g entrance next ↦
            (edge depth a b g entrance next).toReal)
          depth a rest entrance chain
  | _, _, [], _, _ => by
      simp [nestedGapChainKernelENNReal, nestedGapChainKernel]
  | depth, a, b :: rest, entrance, chain => by
      rw [nestedGapChainKernelENNReal, nestedGapChainKernel,
        ENNReal.toReal_sum]
      · apply Finset.sum_congr rfl
        intro next _
        rw [ENNReal.toReal_mul,
          nestedGapChainKernelENNReal_toReal hedge
            (depth + 1) b rest next chain.2]
      · intro next _
        exact ENNReal.mul_ne_top
          (hedge depth a b chain.1 entrance next)
          (nestedGapChainKernelENNReal_ne_top hedge
            (depth + 1) b rest next chain.2)

/-- A literal ENNReal edge family satisfies the quantitative row estimate
after taking its finite real-valued child-vector sum. -/
def NestedEdgeLowerENNReal
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    (epsilon : ℝ) (edge : NestedEdgeKernelENNReal State) : Prop :=
  ∀ depth a b (g : GapPattern a b)
      (entrance : BoundaryVector State depth a),
    (1 - epsilon) ^ (a + b) *
        (∏ i, halfGeometricMass (gapMultiplicity g i)) ≤
      ∑ next : BoundaryVector State (depth + 1) b,
        (edge depth a b g entrance next).toReal

/-- One specified literal radial depth satisfies the real-valued row
comparison after its finite ENNReal child-vector partition is summed. -/
def NestedEdgeLowerAtENNReal
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    (epsilon : ℝ) (edge : NestedEdgeKernelENNReal State)
    (depth : ℕ) : Prop :=
  ∀ a b (g : GapPattern a b)
      (entrance : BoundaryVector State depth a),
    (1 - epsilon) ^ (a + b) *
        (∏ i, halfGeometricMass (gapMultiplicity g i)) ≤
      ∑ next : BoundaryVector State (depth + 1) b,
        (edge depth a b g entrance next).toReal

/-- Literal-probability form of the nested fixed-chain lower estimate. -/
theorem ofReal_one_sub_pow_radialWordLength_mul_gapChainMass_le_nested
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernelENNReal State} {epsilon : ℝ}
    (hepsilon1 : epsilon ≤ 1)
    (hedge : ∀ depth a b g entrance next,
      edge depth a b g entrance next ≠ ⊤)
    (hlower : NestedEdgeLowerENNReal epsilon edge)
    (depth a : ℕ) (rest : List ℕ)
    (entrance : BoundaryVector State depth a)
    (chain : GapChain (a :: rest)) :
    ENNReal.ofReal
        ((1 - epsilon) ^ radialWordLength (a :: rest) *
          gapChainMass (a :: rest) chain) ≤
      nestedGapChainKernelENNReal edge depth a rest entrance chain := by
  apply (ENNReal.ofReal_le_iff_le_toReal
    (nestedGapChainKernelENNReal_ne_top hedge
      depth a rest entrance chain)).2
  rw [nestedGapChainKernelENNReal_toReal hedge]
  apply one_sub_pow_radialWordLength_mul_gapChainMass_le_nested
    hepsilon1
  · intro d c e g u v
    exact ENNReal.toReal_nonneg
  · exact hlower

/-- Finite-depth literal-probability form. -/
theorem ofReal_one_sub_pow_radialWordLength_mul_gapChainMass_le_nested_on
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernelENNReal State} {epsilon : ℝ}
    (hepsilon1 : epsilon ≤ 1)
    (hedge : ∀ depth a b g entrance next,
      edge depth a b g entrance next ≠ ⊤)
    (first a : ℕ) (rest : List ℕ)
    (hlower : ∀ depth, first ≤ depth →
      depth < first + rest.length →
      NestedEdgeLowerAtENNReal epsilon edge depth)
    (entrance : BoundaryVector State first a)
    (chain : GapChain (a :: rest)) :
    ENNReal.ofReal
        ((1 - epsilon) ^ radialWordLength (a :: rest) *
          gapChainMass (a :: rest) chain) ≤
      nestedGapChainKernelENNReal edge first a rest entrance chain := by
  apply (ENNReal.ofReal_le_iff_le_toReal
    (nestedGapChainKernelENNReal_ne_top hedge
      first a rest entrance chain)).2
  rw [nestedGapChainKernelENNReal_toReal hedge]
  apply one_sub_pow_radialWordLength_mul_gapChainMass_le_nested_on
    hepsilon1 (fun _ _ _ _ _ _ ↦ ENNReal.toReal_nonneg)
    first rest
  · intro depth hdepth0 hdepth1
    exact hlower depth hdepth0 hdepth1

/-- Finite-depth profile sum for a literal nested edge partition. -/
theorem ofReal_one_sub_pow_profileRadialWordLength_mul_profileWeight_le_nestedSum_on
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernelENNReal State} {epsilon delta : ℝ}
    {n : ℕ} {m : Profile n}
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1)
    (hepsilon1 : epsilon ≤ 1)
    (hedge : ∀ depth a b g entrance next,
      edge depth a b g entrance next ≠ ⊤)
    (first a : ℕ) (rest : List ℕ)
    (hlist : profileList m = a :: rest)
    (hlower : ∀ depth, first ≤ depth →
      depth < first + rest.length →
      NestedEdgeLowerAtENNReal epsilon edge depth)
    (entrance : BoundaryVector State first a) :
    ENNReal.ofReal
        ((1 - epsilon) ^ radialWordLength (profileList m) * profileWeight m) ≤
      ∑ chain : GapChain (a :: rest),
        nestedGapChainKernelENNReal edge first a rest entrance chain := by
  rw [profileWeight, hlist]
  have hsumtop :
      (∑ chain : GapChain (a :: rest),
        nestedGapChainKernelENNReal edge first a rest entrance chain) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun chain _ ↦
      nestedGapChainKernelENNReal_ne_top hedge
        first a rest entrance chain
  apply (ENNReal.ofReal_le_iff_le_toReal hsumtop).2
  rw [ENNReal.toReal_sum]
  · simp_rw [nestedGapChainKernelENNReal_toReal hedge]
    rw [← sum_gapChainMass_eq_transitionProduct]
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun chain _ ↦
        one_sub_pow_radialWordLength_mul_gapChainMass_le_nested_on
          hepsilon1 (fun _ _ _ _ _ _ ↦ ENNReal.toReal_nonneg)
          first rest (fun depth h0 h1 ↦ hlower depth h0 h1)
            a entrance chain
    · intro c hc
      have hc' : c ∈ profileList m := by simpa only [hlist] using hc
      have htwo := constrainedProfile_all_entries_two_le hdelta hm c hc'
      omega
  · intro chain _
    exact nestedGapChainKernelENNReal_ne_top hedge
      first a rest entrance chain

/-- Literal-probability profile specialization, summed over every nested
weak-composition tree. -/
theorem ofReal_one_sub_pow_profileRadialWordLength_mul_profileWeight_le_nestedSum
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernelENNReal State} {epsilon delta : ℝ}
    {n : ℕ} {m : Profile n}
    (hm : IsConstrainedProfile delta m) (hdelta : delta ≤ 1)
    (hepsilon1 : epsilon ≤ 1)
    (hedge : ∀ depth a b g entrance next,
      edge depth a b g entrance next ≠ ⊤)
    (hlower : NestedEdgeLowerENNReal epsilon edge)
    (depth a : ℕ) (rest : List ℕ)
    (hlist : profileList m = a :: rest)
    (entrance : BoundaryVector State depth a) :
    ENNReal.ofReal
        ((1 - epsilon) ^ radialWordLength (profileList m) * profileWeight m) ≤
      ∑ chain : GapChain (a :: rest),
        nestedGapChainKernelENNReal edge depth a rest entrance chain := by
  rw [profileWeight, hlist]
  have hsumtop :
      (∑ chain : GapChain (a :: rest),
        nestedGapChainKernelENNReal edge depth a rest entrance chain) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun chain _ ↦
      nestedGapChainKernelENNReal_ne_top hedge
        depth a rest entrance chain
  apply (ENNReal.ofReal_le_iff_le_toReal hsumtop).2
  rw [ENNReal.toReal_sum]
  · simp_rw [nestedGapChainKernelENNReal_toReal hedge]
    apply one_sub_pow_radialWordLength_mul_transitionProduct_le_nestedSum
      hepsilon1
    · intro d c e g u v
      exact ENNReal.toReal_nonneg
    · exact hlower
    · intro c hc
      have hc' : c ∈ profileList m := by simpa only [hlist] using hc
      have htwo := constrainedProfile_all_entries_two_le hdelta hm c hc'
      omega
  · intro chain _
    exact nestedGapChainKernelENNReal_ne_top hedge
      depth a rest entrance chain

end

end Erdos1165.AnnularNestedProfileKernel
