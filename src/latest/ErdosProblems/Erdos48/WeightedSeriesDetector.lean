/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.UniformPointwiseZeroDetector

/-!
# The uniform detector as a weighted von Mangoldt series

On the half-plane to the right of one, the detected logarithmic derivative
is exactly a logarithmically weighted von Mangoldt `LSeries`.  This file
records the uniform finite-order lower bound in that form.
-/

namespace Erdos48

open Complex Metric LSeries
open BoundedGaps.Maynard

noncomputable section

/-- Uniform finite-order lower bound for the weighted von Mangoldt series
caused by a primitive Dirichlet `L`-function zero near one. -/
theorem exists_uniform_weightedLSeries_detector :
    ∃ L J : ℕ, 2 ≤ L ∧ L ≤ J ∧
      ∃ lambda : ℝ, 0 < lambda ∧
        ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
          ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
            ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
              eta * Real.log ((q : ℝ) * (|t| + 2)) ≤ lambda →
                ∀ rho₀ : ℂ,
                  DirichletCharacter.LFunction chi rho₀ = 0 →
                  dist rho₀ (((1 + eta : ℝ) : ℂ) + t * I) ≤ 2 * eta →
                    ∃ j : ℕ,
                      L ≤ j ∧ j ≤ J ∧
                        (j - 1).factorial * (1 / 12 : ℝ) *
                            (2 * eta)⁻¹ ^ j <
                          ‖LSeries (fun n : ℕ ↦
                              (Real.log n : ℂ) ^ (j - 1) * chi n *
                                (ArithmeticFunction.vonMangoldt n : ℂ))
                            (((1 + eta : ℝ) : ℂ) + t * I)‖ := by
  obtain ⟨L, J, hL2, hLJ, lambda, hlambda, hdetector⟩ :=
    exists_uniform_pointwise_zero_detector
  refine ⟨L, J, hL2, hLJ, lambda, hlambda, ?_⟩
  intro q _ hq chi hchi t eta heta0 heta8 hetalog rho₀ hzero hrho
  obtain ⟨j, hjL, hjJ, hjlarge⟩ :=
    hdetector q hq chi hchi t eta heta0 heta8 hetalog rho₀ hzero hrho
  refine ⟨j, hjL, hjJ, ?_⟩
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  have hzre : z.re = 1 + eta := by simp [z]
  have hz1 : 1 < z.re := by rw [hzre]; linarith
  have hid :=
    iteratedDeriv_neg_logDeriv_LFunction_eq_weighted_LSeries
      (k := j - 1) chi hz1
  rw [hid] at hjlarge
  simpa only [z, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul] using hjlarge

end

end Erdos48
