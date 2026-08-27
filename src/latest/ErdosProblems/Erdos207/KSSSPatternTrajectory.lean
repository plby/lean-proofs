/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSIndexedThreat
import ErdosProblems.Erdos207.KSSSPoissonCurvature

/-! # The bounded-pattern extension target and its polynomial derivatives -/

namespace Erdos207

open Finset

noncomputable section

def ksssPatternTrajectory (orders : Finset ℕ) (a : ℕ → ℝ)
    (E M : ℝ) (h m : ℕ) (time : ℝ) : ℝ :=
  M * ksssEdgeDensity E time ^ h * Real.exp (-(m : ℝ) * ksssPoissonExponent orders a time)

def ksssPatternSlope (orders : Finset ℕ) (a : ℕ → ℝ)
    (E M : ℝ) (h m : ℕ) (time : ℝ) : ℝ :=
  M * Real.exp (-(m : ℝ) * ksssPoissonExponent orders a time) *
    (-(3 * (h : ℝ) / E) * ksssEdgeDensity E time ^ (h - 1) -
      (m : ℝ) * ksssEdgeDensity E time ^ h * ksssPoissonRate orders a time)

def ksssPatternCurvature (orders : Finset ℕ) (a : ℕ → ℝ)
    (E M : ℝ) (h m : ℕ) (time : ℝ) : ℝ :=
  M * Real.exp (-(m : ℝ) * ksssPoissonExponent orders a time) *
    (9 * (h : ℝ) * (h - 1 : ℕ) / E ^ 2 * ksssEdgeDensity E time ^ (h - 2) +
      6 * (h : ℝ) * (m : ℝ) / E * ksssEdgeDensity E time ^ (h - 1) * ksssPoissonRate orders a time +
      (m : ℝ) ^ 2 * ksssEdgeDensity E time ^ h * ksssPoissonRate orders a time ^ 2 -
      (m : ℝ) * ksssEdgeDensity E time ^ h * ksssPoissonCurvature orders a time)

theorem hasDerivAt_ksssPatternTrajectory
    (orders : Finset ℕ) (a : ℕ → ℝ) (E M : ℝ) (h m : ℕ) (time : ℝ) :
    HasDerivAt (ksssPatternTrajectory orders a E M h m)
      (ksssPatternSlope orders a E M h m time) time := by
  have hd := (((hasDerivAt_ksssEdgeDensity E time).pow h).const_mul M).mul
    (((hasDerivAt_ksssPoissonExponent orders a time).const_mul (-(m : ℝ))).exp)
  convert! hd using 1
  dsimp only [ksssPatternSlope, Pi.pow_apply, Pi.mul_apply]
  ring

theorem hasDerivAt_ksssPatternSlope
    (orders : Finset ℕ) (a : ℕ → ℝ) (E M : ℝ) (h m : ℕ) (time : ℝ) (hE : E ≠ 0) :
    HasDerivAt (ksssPatternSlope orders a E M h m)
      (ksssPatternCurvature orders a E M h m time) time := by
  have hp := hasDerivAt_ksssEdgeDensity E time
  have hr := hasDerivAt_ksssPoissonRate orders a time
  have he := ((hasDerivAt_ksssPoissonExponent orders a time).const_mul (-(m : ℝ))).exp
  have hd := (he.const_mul M).mul
    (((hp.pow (h - 1)).const_mul (-(3 * (h : ℝ) / E))).sub
      (((hp.pow h).const_mul (m : ℝ)).mul hr))
  convert! hd using 1
  dsimp only [ksssPatternCurvature, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply]
  simp only [Nat.sub_sub, show 1 + 1 = (2 : ℕ) from rfl]
  field_simp
  <;> ring

theorem ksss_terminal_trajectory_sum_eq_rate
    (q : ℕ) (a : ℕ → ℝ) (E A time : ℝ) :
    (∑ j ∈ Icc 4 q, ksssConfigurationTrajectory (ksssOrders q) a E A (j - 3) (j - 4) time) =
      ksssAvailableTrajectory (ksssOrders q) a E A time * ksssPoissonRate (ksssOrders q) a time := by
  have hv := ksssThreatTrajectory_vertexOrders q a E A time
  have hr := ksssThreatTrajectory_eq (ksssOrders q) a E A time
    (fun _ hd ↦ (mem_Icc.mp hd).1)
  linarith only [hv, hr]

theorem ksssPatternSlope_source
    (q : ℕ) (a : ℕ → ℝ) (E A M : ℝ) (h m : ℕ) (time : ℝ)
    (hE : E ≠ 0) (hp : ksssEdgeDensity E time ≠ 0)
    (hA : ksssAvailableTrajectory (ksssOrders q) a E A time ≠ 0) :
    ksssPatternSlope (ksssOrders q) a E M h m time =
      -ksssPatternTrajectory (ksssOrders q) a E M h m time *
        ((h : ℝ) * ksssPairTrajectory (ksssOrders q) a E A time +
          (m : ℝ) * ∑ j ∈ Icc 4 q,
            ksssConfigurationTrajectory (ksssOrders q) a E A (j - 3) (j - 4) time) /
        ksssAvailableTrajectory (ksssOrders q) a E A time := by
  rw [ksss_terminal_trajectory_sum_eq_rate]
  dsimp only [ksssPatternSlope, ksssPatternTrajectory, ksssPairTrajectory]
  cases h with
  | zero => simp only [Nat.cast_zero, zero_mul, zero_div, neg_zero, zero_sub, zero_add, pow_zero, mul_one]
            field_simp
            <;> ring
  | succ h =>
    simp only [Nat.add_sub_cancel, pow_succ, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring

end

end Erdos207
