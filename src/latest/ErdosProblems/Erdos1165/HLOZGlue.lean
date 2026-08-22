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

import ErdosProblems.Erdos1165.Lower
import ErdosProblems.Erdos1165.Upper

/-!
# Final measure-theoretic glue for Erdős Problem 1165

This module combines the two exact almost-sure estimates proved in the
lower- and upper-bound parts of the Hao--Li--Okada--Zheng argument:

* at least three favorite sites occur frequently;
* at most three favorite sites occur eventually.

Their conjunction is the natural-valued form of the almost-sure statement
that the limsup of the number of favorite sites is three.  The remainder of
the file derives the probability-one result for three sites, the
probability-zero result for every fixed `r >= 4`, and the requested piecewise
answer for every `r >= 3`.
-/

open Filter MeasureTheory ProbabilityTheory Set

namespace Erdos1165

/-- The two HLOZ bounds combine pointwise almost surely into the complete
natural-valued limsup conclusion. -/
theorem hlozConclusion_ae_of_bounds
    (hlower : ∀ᵐ s ∂simpleRandomWalk,
      ∃ᶠ n in atTop, 3 ≤ favoriteCount s n)
    (hupper : ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3) :
    ∀ᵐ s ∂simpleRandomWalk, HLOZConclusion s := by
  filter_upwards [hlower, hupper] with s hsLower hsUpper
  exact ⟨hsLower, hsUpper⟩

/-- The lower and upper HLOZ bounds imply that exactly three favorite sites
occur infinitely often with probability one. -/
theorem favoriteEvent_three_measure_eq_one_of_bounds
    (hlower : ∀ᵐ s ∂simpleRandomWalk,
      ∃ᶠ n in atTop, 3 ≤ favoriteCount s n)
    (hupper : ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3) :
    simpleRandomWalk (favoriteEvent 3) = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_favoriteEvent 3)).mp
  filter_upwards [hlozConclusion_ae_of_bounds hlower hupper] with s hs
  exact hlozConclusion_three_frequently hs

/-- The eventual upper bound rules out every fixed cardinality `r >= 4`
infinitely often; the lower bound is retained in the interface so both
branches consume the same exact pair of HLOZ conclusions. -/
theorem favoriteEvent_measure_eq_zero_of_bounds
    (hlower : ∀ᵐ s ∂simpleRandomWalk,
      ∃ᶠ n in atTop, 3 ≤ favoriteCount s n)
    (hupper : ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3)
    (r : Nat) (hr : 4 ≤ r) :
    simpleRandomWalk (favoriteEvent r) = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hlozConclusion_ae_of_bounds hlower hupper] with s hs
  exact hlozConclusion_not_frequently_of_four_le hs hr

/-- The requested probability for every `r >= 3`, assuming precisely the
two canonical almost-sure bounds established by the analytic development. -/
theorem erdos_1165_of_bounds
    (hlower : ∀ᵐ s ∂simpleRandomWalk,
      ∃ᶠ n in atTop, 3 ≤ favoriteCount s n)
    (hupper : ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3)
    (r : Nat) (hr : 3 ≤ r) :
    simpleRandomWalk (favoriteEvent r) = if r = 3 then 1 else 0 := by
  by_cases hreq : r = 3
  · subst r
    simpa using favoriteEvent_three_measure_eq_one_of_bounds hlower hupper
  · rw [if_neg hreq]
    apply favoriteEvent_measure_eq_zero_of_bounds hlower hupper r
    omega

end Erdos1165
