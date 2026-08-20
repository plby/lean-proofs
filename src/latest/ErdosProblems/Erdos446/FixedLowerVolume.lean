/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedLowerEnergyMoment
import ErdosProblems.Erdos446.FixedLowerSizeRetention

/-!
# Erdős Problem 446: unconditional fixed lower volume

This module combines the quantitative prefix-energy moment with the
independent product-size deletion.  It is the finite occupancy analogue of
Ford's equations (47a)--(47c): after imposing both cutoffs, an explicit
one-eighth of the natural one-slack volume remains.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The absolute first-moment constant furnished by the finite Smirnov--Abel
calculation. -/
noncomputable def fixedLowerMomentConstant : ℝ :=
  8000 * Real.exp 4

/-- The Markov cutoff used for the final lower-volume family. -/
noncomputable def fixedLowerEnergyCutoff : ℝ :=
  2 * fixedLowerMomentConstant

theorem fixedLowerMomentConstant_pos : 0 < fixedLowerMomentConstant := by
  dsimp [fixedLowerMomentConstant]
  positivity

/-- Unconditional finite lower-volume theorem.  Every vector counted on the
right satisfies the one-slack Smirnov barrier, Ford's forward cap, the
prefix-energy cutoff, and the construction-size cutoff. -/
theorem fixedLowerSizedRestrictedMass_eighth_scale
    {M k : ℕ} (hM : 1 ≤ M) (hk : 2 ≤ k) :
    (1 / 8 : ℝ) *
        ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) ≤
      fixedLowerSizedRestrictedMass M k fixedLowerEnergyCutoff := by
  have hmoment := fixedLowerPrefixEnergyMoment_le_scale
    (k := k) (by omega : 1 ≤ k)
  simpa [fixedLowerEnergyCutoff, fixedLowerMomentConstant] using
    fixedLowerSizedRestrictedMass_eighth_scale_of_moments
      hM hk fixedLowerMomentConstant_pos hmoment

/-- Direct transfer of the unconditional lower volume to the actual
size-truncated Ford-positive composition family. -/
theorem fordPositive_sized_mass_eighth_scale
    {M k : ℕ} {E Q : ℝ}
    (hM : 1 ≤ M) (hk : 2 ≤ k) (hQ : 0 ≤ Q)
    (hquality :
      Real.exp E * (1 + Q * fixedLowerEnergyCutoff) ≤ 13 / 10)
    (hQdef : Q = 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) :
    (1 / 8 : ℝ) *
        ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) ≤
      ∑ c ∈ (fordPositiveCompositions M k E).filter
          (fun c ↦ c ∈ sizedCappedCompositions M k),
        1 / compositionFactorial c := by
  exact fordPositive_sized_mass_lower_of_fixedLower
    hM hQ hquality hQdef
      (fixedLowerSizedRestrictedMass_eighth_scale hM hk)

end Erdos446
