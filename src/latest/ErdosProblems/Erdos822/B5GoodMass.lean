/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B5FirstMoment
import ErdosProblems.Erdos822.GoodCofactorMass

/-!
# Positive reciprocal mass after the B5 filter

The odd raw layer has logarithmic reciprocal mass.  The preceding first
moment is also logarithmic, so a fixed sufficiently large Markov cutoff
removes at most half of the available mass.
-/

namespace Erdos822

open scoped BigOperators

/-- After imposing the bounded shifted-prime-mass condition, a fixed
positive fraction of the logarithmic odd-cofactor mass remains. -/
theorem exists_eventually_massGoodOddCofactors_log_mass :
    ∃ S : ℕ, ∃ C₀ : ℝ, 101 ≤ S ∧ 0 < C₀ ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let y := Nat.nthRoot (4 * S) N
        (1 / 4000 : ℝ) * Real.log (N : ℝ) ≤
          ∑ m ∈ massGoodOddCofactors N 2 y C₀,
            (1 : ℝ) / m := by
  obtain ⟨S, D, hS, hD, hmoment⟩ :=
    exists_eventually_shiftedMassFirstMoment_slowCutoff_le
  let C₀ : ℝ := 8000 * (D + 1)
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    nlinarith
  refine ⟨S, C₀, hS, hC₀, ?_⟩
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (1 : ℝ))
  filter_upwards [hmoment, eventually_log_le_mul_reciprocalOddRawCofactorSum,
      hlog] with N hmomentN hraw hlogN
  change (1 : ℝ) ≤ Real.log (N : ℝ) at hlogN
  dsimp only at hmomentN ⊢
  let y := Nat.nthRoot (4 * S) N
  have hmoment' :
      ∑ m ∈ oddRawCofactors N,
          shiftedTotientReciprocalMass m 2 y / m ≤
        D * (1 + Real.log (N : ℝ)) := by
    simpa [shiftedMassFirstMoment, y] using hmomentN.2
  have hraw' :
      (1 / 2000 : ℝ) * Real.log (N : ℝ) ≤
        ∑ m ∈ oddRawCofactors N, (1 : ℝ) / m := by
    simpa [reciprocalOddRawCofactorSum] using hraw
  have hgood :=
    sum_inv_massGoodOddCofactors_ge_of_firstMoment
      N 2 y hC₀ hraw' hmoment'
  have hDratio : D / (D + 1) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (by nlinarith : 0 < D + 1)).2
    nlinarith
  have hbad :
      (D * (1 + Real.log (N : ℝ))) / C₀ ≤
        (1 / 4000 : ℝ) * Real.log (N : ℝ) := by
    calc
      (D * (1 + Real.log (N : ℝ))) / C₀ =
          (D / (D + 1)) *
            ((1 + Real.log (N : ℝ)) / 8000) := by
        dsimp [C₀]
        field_simp
      _ ≤ (1 : ℝ) *
          ((1 + Real.log (N : ℝ)) / 8000) := by
        exact mul_le_mul_of_nonneg_right hDratio (by
          have : 0 ≤ Real.log (N : ℝ) := by linarith
          positivity)
      _ ≤ (1 / 4000 : ℝ) * Real.log (N : ℝ) := by
        nlinarith
  calc
    (1 / 4000 : ℝ) * Real.log (N : ℝ) ≤
        (1 / 2000 : ℝ) * Real.log (N : ℝ) -
          (D * (1 + Real.log (N : ℝ))) / C₀ := by
      linarith
    _ ≤ ∑ m ∈ massGoodOddCofactors N 2 y C₀,
          (1 : ℝ) / m := hgood

end Erdos822
