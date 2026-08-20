/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.DirichletSeriesTail

/-!
# A finite Dirichlet-series zero detector

The exponentially damped tail estimate truncates the uniform weighted
`LSeries` detector at `ceil (exp (R/eta))`, losing only half of its lower
bound.  The result is the finite polynomial to which the hybrid large sieve
will be applied.
-/

namespace Erdos48

open Complex Metric LSeries
open BoundedGaps.Maynard

noncomputable section

/-- Natural cutoff used by the finite zero detector. -/
noncomputable def zeroDetectorCutoff (R eta : ℝ) : ℕ :=
  Nat.ceil (Real.exp (R / eta))

theorem zeroDetectorCutoff_pos (R eta : ℝ) :
    0 < zeroDetectorCutoff R eta := by
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

theorem exp_div_le_zeroDetectorCutoff (R eta : ℝ) :
    Real.exp (R / eta) ≤ (zeroDetectorCutoff R eta : ℝ) :=
  Nat.le_ceil _

/-- Every zero in the log-free region forces a large finite weighted
von Mangoldt Dirichlet polynomial, at one of finitely many fixed orders. -/
theorem exists_uniform_finite_series_detector :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda R : ℝ, 0 < lambda ∧ 0 < R ∧
        ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
          ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
            ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
              eta * Real.log ((q : ℝ) * (|t| + 2)) ≤ lambda →
                ∀ rho₀ : ℂ,
                  DirichletCharacter.LFunction chi rho₀ = 0 →
                  dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
                    ∃ j : ℕ,
                      L ≤ j ∧ j ≤ J ∧
                        (j - 1).factorial * (1 / 24 : ℝ) *
                            (2 * eta)⁻¹ ^ j <
                          ‖∑ n ∈ Finset.Icc 1 (zeroDetectorCutoff R eta),
                            LSeries.term (fun m : ℕ ↦
                              (Real.log m : ℂ) ^ (j - 1) * chi m *
                                (ArithmeticFunction.vonMangoldt m : ℂ))
                              (((1 + eta : ℝ) : ℂ) + t * I) n‖ := by
  obtain ⟨L, J, hL2, hLJ, lambda, hlambda, hdetector⟩ :=
    exists_uniform_weightedLSeries_detector
  obtain ⟨R, hR, htailBudget⟩ :=
    exists_weighted_vonMangoldt_tail_budget J
  refine ⟨L, J, hL2, hLJ, lambda, R, hlambda, hR, ?_⟩
  intro q _ hq chi hchi t eta heta0 heta8 hetalog rho₀ hzero hrho
  obtain ⟨j, hjL, hjJ, hjfull⟩ :=
    hdetector q hq chi hchi t eta heta0 heta8 hetalog rho₀ hzero hrho
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let c : ℕ → ℂ := fun m ↦
    (Real.log m : ℂ) ^ (j - 1) * chi m *
      (ArithmeticFunction.vonMangoldt m : ℂ)
  let N : ℕ := zeroDetectorCutoff R eta
  let P : ℂ := ∑ n ∈ Finset.Icc 1 N, LSeries.term c z n
  let B : ℝ := (j - 1).factorial * (1 / 24 : ℝ) *
    (2 * eta)⁻¹ ^ j
  have hNpos : 0 < N := by
    simpa only [N] using zeroDetectorCutoff_pos R eta
  have hNexp : Real.exp (R / eta) ≤ (N : ℝ) := by
    simpa only [N] using exp_div_le_zeroDetectorCutoff R eta
  have htailRaw := norm_weighted_vonMangoldt_LSeries_sub_sum_le
    chi eta R t heta0 (by linarith : eta ≤ 1) N (j - 1)
      hNpos hNexp
  have horder : j - 1 + 1 ≤ J := by omega
  have htailBudget' := htailBudget eta heta0 (by linarith : eta ≤ 1)
    (j - 1) horder
  have htail : ‖LSeries c z - P‖ ≤ B := by
    exact htailRaw.trans (by
      simpa only [c, z, N, P, B, show j - 1 + 1 = j by omega]
        using htailBudget')
  have hfull : 2 * B < ‖LSeries c z‖ := by
    have hBdouble : 2 * B =
        (j - 1).factorial * (1 / 12 : ℝ) * (2 * eta)⁻¹ ^ j := by
      dsimp [B]
      ring
    rw [hBdouble]
    simpa only [c, z] using hjfull
  have htri : ‖LSeries c z‖ ≤ ‖P‖ + ‖LSeries c z - P‖ := by
    calc
      ‖LSeries c z‖ = ‖P + (LSeries c z - P)‖ := by congr 1; ring
      _ ≤ ‖P‖ + ‖LSeries c z - P‖ := norm_add_le _ _
  refine ⟨j, hjL, hjJ, ?_⟩
  change B < ‖P‖
  linarith

end

end Erdos48
