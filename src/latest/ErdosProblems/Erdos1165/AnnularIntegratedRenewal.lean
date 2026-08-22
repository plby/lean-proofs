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

import ErdosProblems.Erdos1165.AnnularOffspringKernel

/-!
# Integrating a retained-endpoint renewal kernel

The valid Appendix-A.6 transition sums the spatial exit endpoint of each
fresh radial piece.  This module is the finite algebraic bridge from the
pointwise strong-Markov renewal identity to the stochastic row identity used
by `integratedMarkedOffspringKernel`.
-/

open scoped BigOperators

namespace Erdos1165.AnnularIntegratedRenewal

open AnnularOffspringKernel

noncomputable section

/-- Sum a finite retained-endpoint kernel over its endpoint. -/
def integratedExitRow {State Exit : Type*} [Fintype Exit]
    (kernel : State → Exit → ℝ) (u : State) : ℝ :=
  ∑ w, kernel u w

lemma integratedExitRow_nonneg
    {State Exit : Type*} [Fintype Exit]
    {kernel : State → Exit → ℝ}
    (hkernel : ∀ u w, 0 ≤ kernel u w) (u : State) :
    0 ≤ integratedExitRow kernel u := by
  exact Finset.sum_nonneg fun w _ ↦ hkernel u w

/-- Summing a pointwise renewal equation over a normalized exit boundary
produces the exact endpoint-integrated stochastic renewal row. -/
theorem isStochasticRenewalRow_of_isRenewalKernel_of_integratedExitRow_eq_one
    {State Exit : Type*} [Fintype State] [Fintype Exit]
    {cycle : State → State → ℝ}
    {escape unmarked : State → Exit → ℝ}
    (hrenewal : IsRenewalKernel cycle escape unmarked)
    (hunmarked : ∀ u, integratedExitRow unmarked u = 1) :
    IsStochasticRenewalRow cycle (integratedExitRow escape) := by
  intro u
  calc
    1 = ∑ w, unmarked u w := (hunmarked u).symm
    _ = ∑ w, (escape u w +
        kernelAction cycle (fun v ↦ unmarked v w) u) := by
      apply Finset.sum_congr rfl
      intro w _
      exact hrenewal u w
    _ = integratedExitRow escape u +
        ∑ w, ∑ v, cycle u v * unmarked v w := by
      rw [Finset.sum_add_distrib]
      rfl
    _ = integratedExitRow escape u +
        ∑ v, cycle u v * (∑ w, unmarked v w) := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
    _ = integratedExitRow escape u + ∑ v, cycle u v := by
      apply congrArg (integratedExitRow escape u + ·)
      apply Finset.sum_congr rfl
      intro v _
      have hv := hunmarked v
      change (∑ w, unmarked v w) = 1 at hv
      rw [hv, mul_one]

/-- A convenient specialization when the unmarked retained-endpoint kernel
is already presented as a probability row. -/
theorem isStochasticRenewalRow_of_isRenewalKernel_of_sum_eq_one
    {State Exit : Type*} [Fintype State] [Fintype Exit]
    {cycle : State → State → ℝ}
    {escape unmarked : State → Exit → ℝ}
    (hrenewal : IsRenewalKernel cycle escape unmarked)
    (hunmarked : ∀ u, ∑ w, unmarked u w = 1) :
    IsStochasticRenewalRow cycle (fun u ↦ ∑ w, escape u w) := by
  exact isStochasticRenewalRow_of_isRenewalKernel_of_integratedExitRow_eq_one
    hrenewal hunmarked

end

end Erdos1165.AnnularIntegratedRenewal
