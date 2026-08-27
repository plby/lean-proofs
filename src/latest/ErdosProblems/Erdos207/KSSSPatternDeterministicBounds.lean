/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPatternRelativeDrift
import ErdosProblems.Erdos207.PatternRelativePowerArithmetic

/-! # Discharging the deterministic next-target and Taylor requirements -/

namespace Erdos207

open Finset

noncomputable section

theorem ksssPatternTaylorCoefficient_nonneg
    (q : ℕ) (coeff : ℕ → ℝ) (h m : ℕ) (hb : ∀ d ∈ ksssOrders q, 0 ≤ coeff d) :
    0 ≤ ksssPatternTaylorCoefficient q coeff h m := by
  have hB₁ : 0 ≤ ∑ d ∈ ksssOrders q, (d : ℝ) * coeff d :=
    sum_nonneg fun d hd ↦ mul_nonneg (Nat.cast_nonneg d) (hb d hd)
  have hB₂ : 0 ≤ ∑ d ∈ ksssOrders q, (d : ℝ) * (d - 1 : ℕ) * coeff d :=
    sum_nonneg fun d hd ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg _)) (hb d hd)
  unfold ksssPatternTaylorCoefficient patternCurvatureBudget
  positivity

theorem ksssPatternTrajectory_relative_deterministic_bounds
    (q b B h m : ℕ) (a coeff : ℕ → ℝ) (E A M time t : ℝ)
    (hE : 0 < E) (hA : 0 < A) (hM : 0 < M) (ht : 1 ≤ t)
    (htime : 0 ≤ time) (hclock : 3 * (time + 1) < E)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hexp : Real.exp (∑ d ∈ ksssOrders q, coeff d) ≤ t)
    (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E time)
    (hscale : ksssPatternTaylorCoefficient q coeff h m * t ^ (b * h + m + ksssPowerErrorExponent b B) ≤ E)
    (hL : 2 * (3 * ksssPatternHazardCoefficient q coeff h m + 1) ≤ E * ksssEdgeDensity E time) :
    ksssPatternTrajectory (ksssOrders q) a E M h m time / 2 ≤
        ksssPatternTrajectory (ksssOrders q) a E M h m (time + 1) ∧
      |ksssPatternTrajectory (ksssOrders q) a E M h m (time + 1) -
        ksssPatternTrajectory (ksssOrders q) a E M h m time| /
        ksssPatternTrajectory (ksssOrders q) a E M h m time ≤
          (3 * ksssPatternHazardCoefficient q coeff h m + 1) / (E * ksssEdgeDensity E time) ∧
      4 * (M * ksssPatternTaylorCoefficient q coeff h m / E ^ 2) /
        ksssPatternTrajectory (ksssOrders q) a E M h m time ≤
          3 * relativePatternEnvelope E t (ksssPowerErrorExponent b B) B time / (E * ksssEdgeDensity E time) := by
  let f := ksssPatternTrajectory (ksssOrders q) a E M h m time
  let fp := ksssPatternTrajectory (ksssOrders q) a E M h m (time + 1)
  let L := E * ksssEdgeDensity E time
  let x := ksssPairTrajectory (ksssOrders q) a E A time
  let G := ksssPatternHazardCoefficient q coeff h m
  let H := ksssPatternHazardTrajectory q a E A h m time
  let tau := M * ksssPatternTaylorCoefficient q coeff h m / E ^ 2
  let z := relativePatternEnvelope E t (ksssPowerErrorExponent b B) B time
  have htpos : 0 < t := by linarith
  have hc : 3 * time < E := by linarith
  have hp := ksssEdgeDensity_pos hE hc
  have hp1 := ksssEdgeDensity_le_one hE htime
  have hLpos : 0 < L := mul_pos hE hp
  have hLE : L ≤ E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp1 hE.le
  have hx : 0 < x := ksssPairTrajectory_pos _ _ hE hA hc
  have hf : 0 < f := ksssPatternTrajectory_pos _ _ _ _ _ _ _ hM hp
  have hb : ∀ d ∈ ksssOrders q, 0 ≤ coeff d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have hC := ksssPatternTaylorCoefficient_nonneg q coeff h m hb
  have hfLower : M / t ^ (b * h + m) ≤ f := ksssPatternTrajectory_power_lower _ _ _ _ _ _ _ _ _ _
    hM.le htpos htime (by linarith) ha hab hexp hfloor
  have hrelative : tau / f ≤ 1 / (E * t ^ ksssPowerErrorExponent b B) :=
    pattern_taylor_relative_inverse_clock M f (ksssPatternTaylorCoefficient q coeff h m) E t
      (b * h + m) (ksssPowerErrorExponent b B) hM hf hC hE htpos hfLower hscale
  have hsmall : 4 * tau / f ≤ 3 * z / L ∧ tau / f ≤ 1 / L :=
    pattern_taylor_relative_envelope_budget tau f E L t z (ksssPowerErrorExponent b B) hE hLpos ht hLE
      hrelative (relativePatternEnvelope_taylor_cover E t time (ksssPowerErrorExponent b B) B hE ht htime hc)
  have hTaylor := ksssPatternTrajectory_unitStep_source_error q a coeff E A M time h m hE hA hM.le
    htime hclock ha hab
  have hH := (ksssPatternHazardTrajectory_bounds q a coeff E A time h m hE hA htime hc ha hab).2
  have hstep : |fp - f| / f ≤ (3 * G + 1) / L := by
    calc
      _ ≤ 3 * G / L + tau / f := pattern_target_step_relative_bound f fp H
        (ksssAvailableTrajectory (ksssOrders q) a E A time) L x G tau hf hLpos hx
        (ksssAvailableTrajectory_eq_clock_pair _ _ _ _ _ hE.ne' hp.ne') hH hTaylor
      _ ≤ 3 * G / L + 1 / L := add_le_add le_rfl hsmall.2
      _ = _ := by ring
  have hhalfRate : (3 * G + 1) / L ≤ 1 / 2 := by
    apply (div_le_iff₀ hLpos).mpr
    change 2 * (3 * G + 1) ≤ L at hL
    linarith only [hL]
  exact ⟨pattern_target_next_ge_half f fp _ hf hstep hhalfRate, hstep, hsmall.1⟩

end

end Erdos207
