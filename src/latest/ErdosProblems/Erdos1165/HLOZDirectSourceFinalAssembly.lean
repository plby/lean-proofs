/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.AnnularOnePointProfileTransferDirect
import ErdosProblems.Erdos1165.AsymmetricLiteralPairEndpoint
import ErdosProblems.Erdos1165.Proposition13DirectTransferAssembly
import ErdosProblems.Erdos1165.HLOZGlue

/-!
# Final adapter from literal lower sources and the HLOZ upper theorem

The chronological one-point profile transfer is already constructed without
premises.  Consequently, the only remaining lower input is the eventual
asymmetric pair source.  This module packages that source with the one-point
construction, derives Proposition 1.3, feeds it to the upper theorem, and
then invokes the final measure-theoretic glue.

No probability estimate is assumed here: the upper input is deliberately a
function of the lower-deviation theorem that its proof uses.
-/

open Filter MeasureTheory

namespace Erdos1165.HLOZDirectSourceFinalAssembly

open AsymmetricLiteralPairEndpoint
open Erdos1165.AnnularOnePointProfileTransferDirect
open Proposition13DirectTransferAssembly

/-- The premise-free chronological one-point construction and an eventual
asymmetric pair source give the exact direct lower-data package. -/
theorem hasDirectAnnularScaleData_of_asymmetricPairSource
    (hpairSource : ∀ delta : ℝ, 0 < delta →
      ∀ᶠ n : ℕ in atTop, Nonempty (AsymmetricPairSourceData delta n)) :
    HasDirectAnnularScaleData := by
  apply hasDirectAnnularScaleData_of_eventually
  · intro delta hdelta
    exact eventually_nonempty_annularOnePointProfileTransfer hdelta
  · intro delta hdelta
    exact eventually_nonempty_literalPairData_of_source hdelta
      (hpairSource delta hdelta)

/-- The eventual asymmetric pair source supplies the planar maximum lower
deviation used by the source-correct HLOZ upper argument. -/
theorem hasPlanarMaximumLowerDeviation_of_asymmetricPairSource
    (hpairSource : ∀ delta : ℝ, 0 < delta →
      ∀ᶠ n : ℕ in atTop, Nonempty (AsymmetricPairSourceData delta n)) :
    HasPlanarMaximumLowerDeviation simpleRandomWalk :=
  hasPlanarMaximumLowerDeviation_of_directData
    (hasDirectAnnularScaleData_of_asymmetricPairSource hpairSource)

/-- Final probability answer once the concrete asymmetric pair source and the
upper theorem depending only on Proposition 1.3 have been constructed. -/
theorem erdos_1165_of_asymmetricPairSource_and_upper
    (hpairSource : ∀ delta : ℝ, 0 < delta →
      ∀ᶠ n : ℕ in atTop, Nonempty (AsymmetricPairSourceData delta n))
    (hupper : HasPlanarMaximumLowerDeviation simpleRandomWalk →
      ∀ᵐ s ∂simpleRandomWalk,
        ∀ᶠ n in atTop, favoriteCount s n ≤ 3)
    (r : ℕ) (hr : 3 ≤ r) :
    simpleRandomWalk (favoriteEvent r) = if r = 3 then 1 else 0 := by
  let hdirect := hasDirectAnnularScaleData_of_asymmetricPairSource hpairSource
  exact Erdos1165.erdos_1165_of_bounds
    (ae_frequently_favoriteCount_ge_three_of_directData hdirect)
    (hupper (hasPlanarMaximumLowerDeviation_of_directData hdirect)) r hr

end Erdos1165.HLOZDirectSourceFinalAssembly
