/-
Copyright 2026 The Lean-Proofs Authors.

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
import ErdosProblems.Erdos76.PippengerSpencerInnerSharp
import ErdosProblems.Erdos76.PippengerSpencerOuterIteration

/-! Compatibility from the two-sided inner marginal to the older lower-only
outer-iteration interface. -/

namespace Erdos76

noncomputable section

namespace FiniteHypergraph

universe uV uE

/-- Forgetting the upper marginal estimate recovers the original interface. -/
lemma TwoSidedFixedLengthInnerMarginalAt.toFixedLengthInnerMarginalAt
    {k : ℕ} {zeta eta : ℝ} {L D₀ : ℕ}
    (h : TwoSidedFixedLengthInnerMarginalAt.{uV, uE} k zeta eta L D₀) :
    FixedLengthInnerMarginalAt.{uV, uE} k zeta eta L D₀ := by
  intro V' E' _ _ _ H D hD hunif hlow hhigh hpair
  obtain ⟨prob, hp₀, hp₁, hmarg⟩ :=
    h V' E' H D hD hunif hlow hhigh hpair
  exact ⟨prob, hp₀, hp₁, fun e ↦ (hmarg e).1⟩

/-- The two-sided sharp theorem implies the lower-only sharp interface used
by the existing outer-iteration API. -/
lemma SharpTwoSidedFixedLengthInnerMarginal.toSharpFixedLengthInnerMarginal
    (h : SharpTwoSidedFixedLengthInnerMarginal) :
    SharpFixedLengthInnerMarginal := by
  intro k hk zeta hzeta hzeta1
  obtain ⟨eta, heta₀, heta₁, L, D₀, hD₀, hfixed⟩ :=
    h k hk zeta hzeta hzeta1
  exact ⟨eta, heta₀, heta₁, L, D₀, hD₀,
    hfixed.toFixedLengthInnerMarginalAt⟩

end FiniteHypergraph

end

end Erdos76
