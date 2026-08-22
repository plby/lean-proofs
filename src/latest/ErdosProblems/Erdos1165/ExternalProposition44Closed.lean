/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.ExternalHLOZOnePoint

/-!
# HLOZ Proposition 4.4 for the external walks

This module closes the last interface in `ExternalProposition44`.  The sharp
one-point local-time tail is supplied by `ExternalHLOZOnePoint`, whose proof
combines the exact external return-coefficient recurrence, the finite
Tauberian Green estimate, and quantitative renewal.  The Tonelli--Markov
candidate-count reduction then gives Proposition 4.4, with the exact HLOZ
cutoff, thick-site threshold, candidate budget, and exceptional rate.
-/

open Filter Set
open scoped ENNReal

namespace Erdos1165.ExternalProposition44Closed

open ExternalWalk LazyDecomposition
open ExternalProposition44

/-- HLOZ Proposition 4.4 for either fixed deletion orientation.  In the
repository's exact natural-valued convention, the probability that more
than `floor (exp (16 m^(5/16)))` external sites have local time strictly
above `15m/16 - m^(4/5)` is eventually strictly smaller than
`exp (-m^(5/16))`. -/
theorem eventually_hloz_externalThickCount_failure44 (o : Orientation) :
    ∀ᶠ m : ℕ in atTop,
      externalBlocks o {η |
          hlozSiteBudget44 m < externalThickCount o η
            (hlozCutoff44 m) (hlozThickLevel44 m)} <
        hlozFailureRate44 m :=
  ExternalProposition44.eventually_hloz_externalThickCount_failure44 o
    (ExternalHLOZOnePoint.hlozSharpExternalOnePointTail44 o)

/-- Simultaneous form of Proposition 4.4 for the two HLOZ deletion
orientations.  Finiteness of the orientation type lets the two eventual
bounds share one deterministic threshold in `m`. -/
theorem eventually_hloz_externalThickCount_failure44_allOrientations :
    ∀ᶠ m : ℕ in atTop, ∀ o : Orientation,
      externalBlocks o {η |
          hlozSiteBudget44 m < externalThickCount o η
            (hlozCutoff44 m) (hlozThickLevel44 m)} <
        hlozFailureRate44 m := by
  filter_upwards
      [eventually_hloz_externalThickCount_failure44 Orientation.even,
       eventually_hloz_externalThickCount_failure44 Orientation.shifted]
      with m heven hshifted
  intro o
  cases o with
  | even => exact heven
  | shifted => exact hshifted

end Erdos1165.ExternalProposition44Closed
