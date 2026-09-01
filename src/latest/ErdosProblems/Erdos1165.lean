/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1165.
https://www.erdosproblems.com/forum/thread/1165

Informal authors:
- C. Hao
- X. Li
- Izumi Okada
- Y. Zheng

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1165.md
-/
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

import ErdosProblems.Erdos1165.Basic
import ErdosProblems.Erdos1165.AsymmetricCoarseRadialCompletionFamily
import ErdosProblems.Erdos1165.HLOZDirectSourceFinalAssembly
import ErdosProblems.Erdos1165.HLOZStructuralPastAdditiveRecurrence

/-!
# Erdős Problem 1165

For planar simple symmetric random walk, let `favoriteSites s n` be the sites
whose local time up to and including time `n` is maximal.  Hao, Li, Okada, and
Zheng proved that almost surely the limsup of the number of favorite sites is
three.  Consequently, exactly three favorite sites occur infinitely often with
probability one, while exactly `r` favorite sites occur infinitely often with
probability zero for every `r ≥ 4`.

The detailed mathematical proof, source audit, and declaration map are in
`tex/1165.tex`.  In particular, Tóth's 2001 theorem is one-dimensional; the
planar upper and lower bounds both come from Hao--Li--Okada--Zheng.

References:

* [Erdős Problem 1165](https://www.erdosproblems.com/1165)
* C. Hao, X. Li, I. Okada, and Y. Zheng,
  [Favorite Sites for Simple Random Walk in Two and More Dimensions]
  (https://arxiv.org/abs/2409.00995).
-/

open Filter MeasureTheory ProbabilityTheory Set

namespace Erdos1165

open HLOZStructuralPastAdditiveRecurrence

/-- The probability answer follows formally from the almost-sure planar limsup theorem. -/
theorem erdos_1165_of_hloz
    (hHLOZ : ∀ᵐ s ∂simpleRandomWalk, HLOZConclusion s)
    (r : ℕ) (hr : 3 ≤ r) :
    simpleRandomWalk (favoriteEvent r) = if r = 3 then 1 else 0 := by
  by_cases hreq : r = 3
  · subst r
    rw [if_pos rfl]
    apply (mem_ae_iff_prob_eq_one (measurableSet_favoriteEvent 3)).mp
    filter_upwards [hHLOZ] with s hs
    exact hlozConclusion_three_frequently hs
  · rw [if_neg hreq]
    rw [measure_eq_zero_iff_ae_notMem]
    have hr4 : 4 ≤ r := by omega
    filter_upwards [hHLOZ] with s hs
    exact hlozConclusion_not_frequently_of_four_le hs hr4

/-- For planar simple random walk, exactly three favorite sites occur
infinitely often almost surely, while no larger number does. -/
theorem erdos_1165 (r : ℕ) (hr : 3 ≤ r) :
    simpleRandomWalk (favoriteEvent r) = if r = 3 then 1 else 0 := by
  exact
    HLOZDirectSourceFinalAssembly.erdos_1165_of_asymmetricPairSource_and_upper
      (fun delta _hdelta ↦
        AsymmetricCoarseRadialCompletionFamily.eventually_nonempty_asymmetricPairSourceData
          delta)
      simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_lowerDeviation
      r hr

end Erdos1165
