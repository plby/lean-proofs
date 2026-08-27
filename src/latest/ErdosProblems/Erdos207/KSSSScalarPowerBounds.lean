/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPowerExponentChoice
import ErdosProblems.Erdos207.KSSSCoefficientChoice
import ErdosProblems.Erdos207.KSSSPowerCrudeBudgets
import ErdosProblems.Erdos207.DyadicAvailabilityFloor
import ErdosProblems.Erdos207.PowerSelectorBounds

/-! # All scalar active-state budgets from the fixed power hierarchy -/

namespace Erdos207

open Finset

noncomputable section

structure KSSSScalarPowerBounds (q b B k : ℕ) (a : ℕ → ℝ) (E A time N t : ℝ) : Prop where
  clock_strict : 3 * time < E
  clock_lower : N ^ 2 / t ^ (2 * b) ≤ E * ksssEdgeDensity E time
  pair_lower : N / t ^ (3 * b + 1) ≤ ksssPairTrajectory (ksssOrders q) a E A time
  pair_upper : ksssPairTrajectory (ksssOrders q) a E A time ≤ 3 * N
  error_small : ksssErrorEnvelope E (N / t ^ ksssPowerErrorExponent b B) B time ≤
    ksssPairTrajectory (ksssOrders q) a E A time / 4
  error_upper : ksssErrorEnvelope E (N / t ^ ksssPowerErrorExponent b B) B time ≤ N
  error_base : N / t ^ ksssPowerErrorExponent b B ≤
    ksssErrorEnvelope E (N / t ^ ksssPowerErrorExponent b B) B time
  overlap_error : t ^ (k + 1) ≤ ksssErrorEnvelope E (N / t ^ ksssPowerErrorExponent b B) B time
  error_two : 2 ≤ ksssErrorEnvelope E (N / t ^ ksssPowerErrorExponent b B) B time
  clock_base : t ≤ E * ksssEdgeDensity E time
  pair_clock_error : ksssPairTrajectory (ksssOrders q) a E A time ≤
    (E * ksssEdgeDensity E time) * ksssErrorEnvelope E (N / t ^ ksssPowerErrorExponent b B) B time
  taylor_size : A ≤ (N / t ^ ksssPowerErrorExponent b B) * E ^ 2
  unit_clock : 3 * time + 6 ≤ E
  target_floor : N ^ 3 / (6 * t ^ (5 * b + 1)) ≤ ksssAvailableTrajectory (ksssOrders q) a E A time
  configuration_scale_lower : N / t ^ (3 * b) ≤ ksssConfigurationScale E A time

theorem ksss_scalar_power_bounds
    (q b B k Rmin : ℕ) (a coeff : ℕ → ℝ) (E A time N t : ℝ)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hN : 1 ≤ N) (ht : 32 ≤ t)
    (hscale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ N)
    (hEfloor : N ^ 2 / t ^ b ≤ E)
    (hratioLower : N / t ^ b ≤ A / E) (hratioUpper : A / E ≤ N)
    (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E time)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hcoeff : KSSSPowerCoefficientBounds q coeff B t) :
    KSSSScalarPowerBounds q b B k a E A time N t := by
  let s := ksssPowerErrorExponent b B
  let R := ksssPowerDenominatorExponent q b B k Rmin
  let x := ksssPairTrajectory (ksssOrders q) a E A time
  let L := E * ksssEdgeDensity E time
  let e := ksssErrorEnvelope E (N / t ^ s) B time
  have htpos : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hNpos : 0 < N := by linarith
  have hp : 0 < ksssEdgeDensity E time := (by positivity : (0 : ℝ) < 1 / t ^ b).trans_le hfloor
  have hclock : 3 * time < E := by
    have hp' := (lt_div_iff₀ hE).mp hp
    linarith
  have hpair := ksssPairTrajectory_dyadic_bounds (ksssOrders q) a coeff E A time N t s b B
    hE hA htime hclock ha hab hNpos.le (by linarith) hfloor hratioLower hcoeff.poisson le_rfl
  have hxUpper : x ≤ 3 * N :=
    (ksssPairTrajectory_le_three_ratio (ksssOrders q) a E A time hE hA.le htime hclock ha).trans
      (mul_le_mul_of_nonneg_left hratioUpper (by norm_num))
  have heUpper : e ≤ N := by dsimp only [e, x] at *; linarith only [hpair.2, hxUpper, hN]
  have hbase : N / t ^ s ≤ e :=
    ksssErrorEnvelope_ge_scale E (N / t ^ s) time B hE (by positivity) htime hclock
  have hLlower : N ^ 2 / t ^ (2 * b) ≤ L :=
    residual_clock_power_lower N t E (ksssEdgeDensity E time) b htpos hEfloor hfloor
  obtain ⟨_, _, _, _, _, hclockGap, hoverlapGap, _, _, _⟩ :=
    ksss_power_exponent_hierarchy q b B k Rmin
  change s + 2 * b + 1 ≤ 2 * R at hclockGap
  change s + k + 1 ≤ R at hoverlapGap
  have hOverlap : t ^ (k + 1) ≤ e := power_crude_cutoff_le_error N t e R s (k + 1)
    ht1 hNpos.le hscale (by omega) hbase
  have htPow : t ≤ t ^ (k + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ ht1 (show 1 ≤ k + 1 by omega)
  have heTwo : 2 ≤ e := (show (2 : ℝ) ≤ t by linarith).trans (htPow.trans hOverlap)
  have hLbase : t ≤ L := power_residual_clock_ge_base N t L R b ht1 hNpos.le hscale
    (by omega) hLlower
  have hxe : x ≤ L * e := power_pair_le_clock_error N t L e x R s b
    (by linarith) hNpos.le hscale (by omega) hLlower hbase hxUpper
  have hsize : A ≤ (N / t ^ s) * E ^ 2 := power_initial_available_taylor_budget N t E A R s b
    ht1 hNpos.le hE hscale (by omega) hEfloor hratioUpper
  have hLid : L = E - 3 * time := by
    dsimp only [L]
    unfold ksssEdgeDensity
    field_simp
  have hunit : 3 * time + 6 ≤ E := by linarith only [hLid, hLbase, ht]
  have hxpos : 0 < x := ksssPairTrajectory_pos (ksssOrders q) a hE hA hclock
  have hLpos : 0 < L := mul_pos hE hp
  have hAvail : ksssAvailableTrajectory (ksssOrders q) a E A time = L * x / 3 := by
    dsimp only [L, x]
    unfold ksssPairTrajectory
    field_simp
  have hAvailLower : L * x / 6 ≤ ksssAvailableTrajectory (ksssOrders q) a E A time := by
    rw [hAvail]
    have hprod : 0 ≤ L * x := (mul_pos hLpos hxpos).le
    nlinarith only [hprod]
  have hTarget := selector_power_lower N t L x (ksssAvailableTrajectory (ksssOrders q) a E A time)
    b hNpos.le htpos hLlower hpair.1 hAvailLower
  have hConfigScale := ksssConfigurationScale_power_lower E A time N t b hE hclock hNpos.le htpos
    hfloor hratioLower
  exact ⟨hclock, hLlower, hpair.1, hxUpper, hpair.2, heUpper, hbase, hOverlap, heTwo,
    hLbase, hxe, hsize, hunit, hTarget, hConfigScale⟩

end

end Erdos207
