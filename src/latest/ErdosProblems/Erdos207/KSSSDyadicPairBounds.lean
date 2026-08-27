/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DyadicTrajectoryScaleBounds
import ErdosProblems.Erdos207.KSSSSourceNormalization
import ErdosProblems.Erdos207.KSSSEnvelopeLowerBounds

/-! # Applying the integer density/error hierarchy to the actual KSSS pair trajectory -/

namespace Erdos207

open Finset

noncomputable section

theorem ksssPoisson_exp_neg_ge_inverse_scale
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ t scale : ℝ)
    (ha : ∀ d ∈ orders, 0 ≤ a d) (hab : ∀ d ∈ orders, a d * E₀ ^ d ≤ b d)
    (ht : 0 ≤ t) (htE : t ≤ E₀) (hscale : Real.exp (∑ d ∈ orders, b d) ≤ scale) :
    1 / scale ≤ Real.exp (-ksssPoissonExponent orders a t) := by
  have hrho := ksssPoissonExponent_le_sum orders a b ha hab ht htE
  have hexp := (Real.exp_le_exp.mpr hrho).trans hscale
  simpa only [Real.exp_neg, one_div] using
    one_div_le_one_div_of_le (Real.exp_pos (ksssPoissonExponent orders a t)) hexp

theorem ksssPairTrajectory_dyadic_bounds
    (orders : Finset ℕ) (a coeff : ℕ → ℝ) (E₀ A₀ time N t : ℝ) (s b B : ℕ)
    (hE : 0 < E₀) (hA : 0 < A₀) (hTime : 0 ≤ time) (hclock : 3 * time < E₀)
    (ha : ∀ d ∈ orders, 0 ≤ a d) (hab : ∀ d ∈ orders, a d * E₀ ^ d ≤ coeff d)
    (hN : 0 ≤ N) (ht : 4 ≤ t)
    (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E₀ time)
    (hratio : N / t ^ b ≤ A₀ / E₀) (hexp : Real.exp (∑ d ∈ orders, coeff d) ≤ t)
    (hgap : b * B + 3 * b + 2 ≤ s) :
    N / t ^ (3 * b + 1) ≤ ksssPairTrajectory orders a E₀ A₀ time ∧
      ksssErrorEnvelope E₀ (N / t ^ s) B time ≤ ksssPairTrajectory orders a E₀ A₀ time / 4 := by
  have hp := ksssEdgeDensity_pos hE hclock
  have htpos : 0 < t := by linarith
  have hr := ksssPoisson_exp_neg_ge_inverse_scale orders a coeff E₀ time t ha hab hTime
    (by linarith) hexp
  have hid : ksssPairTrajectory orders a E₀ A₀ time =
      3 * (A₀ / E₀) * ksssEdgeDensity E₀ time ^ 2 * Real.exp (-ksssPoissonExponent orders a time) := by
    rw [ksssPairTrajectory_source orders a E₀ A₀ time hE.ne' hp.ne']
    ring
  rw [hid]
  constructor
  · exact pair_polynomial_power_lower N t _ _ _ b hN htpos hfloor hratio hr
  · exact dyadic_pair_error_le_quarter N t _ _ _ s b B hN ht hfloor hratio hr hgap

theorem ksssPairTrajectory_le_three_ratio
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ time : ℝ)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (hTime : 0 ≤ time) (hclock : 3 * time < E₀)
    (ha : ∀ d ∈ orders, 0 ≤ a d) :
    ksssPairTrajectory orders a E₀ A₀ time ≤ 3 * (A₀ / E₀) := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hp1 := ksssEdgeDensity_le_one hE hTime
  have hp2 : ksssEdgeDensity E₀ time ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hp.le hp1 2
  have he : Real.exp (-ksssPoissonExponent orders a time) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (ksssPoissonExponent_nonneg orders a ha hTime))
  rw [ksssPairTrajectory_source orders a E₀ A₀ time hE.ne' hp.ne']
  calc
    _ ≤ 1 * 1 * (3 * A₀ / E₀) := by gcongr
    _ = _ := by ring

end

end Erdos207
