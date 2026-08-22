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

import ErdosProblems.Erdos1165.AnnularLiteralProfileRowUniform
import ErdosProblems.Erdos1165.AnnularNestedProfileKernel

/-!
# Uniform-loss conclusion for a nested literal profile kernel

This is the final abstract numerical step after a concrete child-vector edge
has been shown to satisfy the common `n⁻⁶` one-level row comparison.  It
turns the exact nested dynamic program into a lower bound by one half of the
HLOZ profile weight.
-/

open scoped ENNReal

namespace Erdos1165.AnnularNestedProfileUniformLoss

open AnnularIntegratedProfileKernel AnnularLiteralProfileRowUniform
open AnnularNestedProfileKernel AppendixFirstMoment PathInsertion
open ProfileGapChain ProfileSmallBall

noncomputable section

/-- A concrete finite-depth nested child-vector kernel that has the literal
`n⁻⁶` row lower bound carries at least half the reference profile mass. -/
theorem ofReal_half_mul_profileWeight_le_nestedSum_on
    {State : ℕ → Type*} [∀ depth, Fintype (State depth)]
    {edge : NestedEdgeKernelENNReal State} {delta : ℝ}
    {n : ℕ} {m : Profile n}
    (hn : 3 ≤ n) (hm : IsConstrainedProfile delta m)
    (hdelta : delta ≤ 1)
    (hedge : ∀ depth a b g entrance next,
      edge depth a b g entrance next ≠ ⊤)
    (first a : ℕ) (rest : List ℕ)
    (hlist : profileList m = a :: rest)
    (hlower : ∀ depth, first ≤ depth →
      depth < first + rest.length →
      NestedEdgeLowerAtENNReal (1 / (n : ℝ) ^ 6) edge depth)
    (entrance : BoundaryVector State first a) :
    ENNReal.ofReal ((1 / 2 : ℝ) * profileWeight m) ≤
      ∑ chain : GapChain (a :: rest),
        nestedGapChainKernelENNReal edge first a rest entrance chain := by
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hepsilon1 : 1 / (n : ℝ) ^ 6 ≤ 1 := by
    exact (div_le_one (pow_pos hnPos 6)).2 (one_le_pow₀ hnOne)
  have hloss := one_half_le_one_sub_inv_pow_six_profileRadialWordLength
    hn hm hdelta
  have hreal :
      (1 / 2 : ℝ) * profileWeight m ≤
        (1 - 1 / (n : ℝ) ^ 6) ^ radialWordLength (profileList m) *
          profileWeight m :=
    mul_le_mul_of_nonneg_right hloss (profileWeight_nonneg m)
  exact (ENNReal.ofReal_le_ofReal hreal).trans
    (ofReal_one_sub_pow_profileRadialWordLength_mul_profileWeight_le_nestedSum_on
      hm hdelta hepsilon1 hedge first a rest hlist hlower entrance)

end

end Erdos1165.AnnularNestedProfileUniformLoss
