/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.RawLogFreeDensity
import ErdosProblems.Erdos48.DetectorLowerCutoffGrowth

/-!
# Unconditional raw log-free density estimate

The fourth-power lower cutoff automatically dominates the height and the
square of the conductor.  This file removes those implementation-level side
conditions from the detector estimate.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

theorem exists_logFreeDensity_parameters :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda R delta eta₀ : ℝ,
        0 < lambda ∧ 0 < R ∧ 0 < delta ∧ delta ≤ 1 ∧
        0 < eta₀ ∧ eta₀ ≤ 1 / 8 ∧
        ∃ A : ℕ, 37 ≤ A ∧
        ∀ (Q T : ℕ), 2 ≤ Q →
          ∀ eta : ℝ, 0 < eta → eta ≤ eta₀ →
          eta * Real.log ((Q : ℝ) * ((T : ℝ) + 2)) ≤ lambda →
          let Y := zeroDetectorLowerCutoff
            ((Q : ℝ) * ((T : ℝ) + 2))
          let N := zeroDetectorCutoff R eta
          (primitiveHighZeroMass Q eta T : ℝ) *
              (delta * eta) * (1 / 96 : ℝ) ^ 2 ≤
            (32 * (Real.log 4 + 4) +
                (256 * (A : ℝ) / 3) * lambda) *
              ∑ j ∈ Finset.Icc L J,
                (2 * Real.exp 2 * (1 + 8 * Real.pi)) *
                  (((T + 1) + 1 : ℕ) : ℝ) *
                  ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 *
                  ((((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) * Real.log 2) ^
                    (2 * ((j - 1) + 1))) *
                  (((Y : ℝ) / 2) ^ (-(2 * eta))) := by
  obtain ⟨L, J, hL2, hLJ, lambda, R, delta, eta₀,
      hlambda, hR, hdelta, hdelta1, heta₀, heta₀8,
      A, hA, hraw⟩ := exists_raw_logFreeDensity_parameters
  refine ⟨L, J, hL2, hLJ, lambda, R, delta, eta₀,
    hlambda, hR, hdelta, hdelta1, heta₀, heta₀8, A, hA, ?_⟩
  intro Q T hQ eta heta hetaSmall hglobal
  apply hraw Q T hQ eta heta hetaSmall hglobal
  · exact detectorLowerCutoff_height_bound Q T hQ
  · exact detectorLowerCutoff_conductor_bound Q T hQ

end

end Erdos48
