/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Probability.Martingale.BorelCantelli

/-!
# Conditional Borel--Cantelli for Erdős Problem 1165

This module packages Lévy's conditional Borel--Cantelli lemma in the form
used by the lower-bound part of Hao--Li--Okada--Zheng's proof.  If `events n`
is measurable at time `n`, then visiting `events n` infinitely often is
almost surely equivalent to divergence of

`sum_{k < n} P(events (k + 1) | ℱ_k)`.

The substantive martingale argument is Mathlib's
`MeasureTheory.ae_mem_limsup_atTop_iff`.  The results below expose its two
forms needed by the random-walk development: an almost-everywhere
`Frequently` conclusion and a probability-one conclusion.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal ProbabilityTheory Topology

namespace Erdos1165.ConditionalBC

variable {Omega : Type*} {m0 : MeasurableSpace Omega} {mu : Measure Omega}
  {F : Filtration Nat m0} {events : Nat -> Set Omega}

/-- The partial sum of the conditional probabilities of the events at the
next time step.  The indexing agrees with Lévy's theorem: the summand at `k`
is the conditional probability of `events (k + 1)` given `F k`. -/
noncomputable def conditionalProbabilitySum
    (F : Filtration Nat m0) (mu : Measure Omega) (events : Nat -> Set Omega)
    (n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n,
    (mu[(events (k + 1)).indicator (1 : Omega -> Real) | F k]) omega

/-- Lévy's conditional Borel--Cantelli lemma, with the conditional sum named
explicitly.  This is the strongest reusable form: it is an almost-everywhere
equivalence, not only the forward implication used in Problem 1165. -/
theorem ae_mem_limsup_iff_conditionalProbabilitySum_tendsto
    [IsFiniteMeasure mu] (hmeas : ∀ n, MeasurableSet[F n] (events n)) :
    ∀ᵐ omega ∂mu, omega ∈ limsup events atTop ↔
      Tendsto (fun n => conditionalProbabilitySum F mu events n omega) atTop atTop := by
  simpa only [conditionalProbabilitySum] using
    (MeasureTheory.ae_mem_limsup_atTop_iff (ℱ := F) mu hmeas)

/-- If the conditional-probability partial sums diverge almost surely, then
the adapted events occur infinitely often almost surely. -/
theorem ae_frequently_mem_of_conditionalProbabilitySum_tendsto
    [IsFiniteMeasure mu] (hmeas : ∀ n, MeasurableSet[F n] (events n))
    (hdiv : ∀ᵐ omega ∂mu,
      Tendsto (fun n => conditionalProbabilitySum F mu events n omega) atTop atTop) :
    ∀ᵐ omega ∂mu, ∃ᶠ n in atTop, omega ∈ events n := by
  filter_upwards
    [ae_mem_limsup_iff_conditionalProbabilitySum_tendsto hmeas, hdiv]
    with omega hiff hsum
  exact mem_limsup_iff_frequently_mem.mp (hiff.mpr hsum)

/-- Probability-one formulation of conditional Borel--Cantelli. -/
theorem measure_limsup_eq_one_of_conditionalProbabilitySum_tendsto
    [IsProbabilityMeasure mu] (hmeas : ∀ n, MeasurableSet[F n] (events n))
    (hdiv : ∀ᵐ omega ∂mu,
      Tendsto (fun n => conditionalProbabilitySum F mu events n omega) atTop atTop) :
    mu (limsup events atTop) = 1 := by
  apply (mem_ae_iff_prob_eq_one ?_).mp
  · filter_upwards
      [ae_frequently_mem_of_conditionalProbabilitySum_tendsto hmeas hdiv]
      with omega homega
    exact mem_limsup_iff_frequently_mem.mpr homega
  · exact MeasurableSet.measurableSet_limsup fun n => F.le n _ (hmeas n)

end Erdos1165.ConditionalBC
