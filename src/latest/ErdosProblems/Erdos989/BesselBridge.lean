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

import ErdosProblems.Erdos989.FixedRadius
import ErdosProblems.Erdos232.Energy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Identification of the two local Bessel developments

`Erdos989.FixedRadius` defines `J₁` by the integer-order Schläfli integral.
The independently developed `Erdos232.Analytic` module defines `J₀` by an
angular integral and formalizes all of its derivatives.  This file proves
that the two normalizations agree: the first derivative of `J₀` is `-J₁`.

This lets the fixed-radius disk multiplier reuse the differentiability,
recurrence, Taylor, and certified interval machinery already available for
`Erdos232.besselDerivative`.
-/

namespace Erdos989
namespace BesselBridge

open MeasureTheory
open scoped Interval

noncomputable section

private def schlafliMain (x θ : ℝ) : ℝ :=
  Real.sin θ * Real.sin (x * Real.sin θ)

private def schlafliOddPart (x θ : ℝ) : ℝ :=
  Real.cos θ * Real.cos (x * Real.sin θ)

theorem integral_schlafliOddPart (x : ℝ) :
    ∫ θ in (0 : ℝ)..Real.pi, schlafliOddPart x θ = 0 := by
  let f : ℝ → ℝ := schlafliOddPart x
  have href := intervalIntegral.integral_comp_sub_left f Real.pi
    (a := (0 : ℝ)) (b := Real.pi)
  simp only [sub_self, sub_zero] at href
  have hpoint : ∀ θ : ℝ, f (Real.pi - θ) = -f θ := by
    intro θ
    dsimp [f, schlafliOddPart]
    rw [Real.cos_pi_sub, Real.sin_pi_sub]
    ring
  have hneg : (∫ θ in (0 : ℝ)..Real.pi, f (Real.pi - θ)) =
      -∫ θ in (0 : ℝ)..Real.pi, f θ := by
    calc
      (∫ θ in (0 : ℝ)..Real.pi, f (Real.pi - θ)) =
          ∫ θ in (0 : ℝ)..Real.pi, -f θ := by
            apply intervalIntegral.integral_congr
            intro θ _
            exact hpoint θ
      _ = -∫ θ in (0 : ℝ)..Real.pi, f θ :=
        intervalIntegral.integral_neg
  rw [href] at hneg
  linarith

theorem besselJOne_eq_schlafliMain (x : ℝ) :
    FixedRadius.besselJOne x = Real.pi⁻¹ *
      ∫ θ in (0 : ℝ)..Real.pi, schlafliMain x θ := by
  rw [FixedRadius.besselJOne]
  congr 1
  have hodd := integral_schlafliOddPart x
  rw [show (fun θ : ℝ ↦ Real.cos (θ - x * Real.sin θ)) =
      fun θ ↦ schlafliOddPart x θ + schlafliMain x θ by
        funext θ
        simp [schlafliOddPart, schlafliMain, Real.cos_sub]
    ]
  rw [intervalIntegral.integral_add]
  · rw [hodd, zero_add]
  · exact (by
      unfold schlafliOddPart
      fun_prop : Continuous (schlafliOddPart x)).intervalIntegrable _ _
  · exact (by
      unfold schlafliMain
      fun_prop : Continuous (schlafliMain x)).intervalIntegrable _ _

theorem schlafliMain_periodic (x : ℝ) :
    Function.Periodic (schlafliMain x) Real.pi := by
  intro θ
  dsimp [schlafliMain]
  rw [Real.sin_add_pi, show x * -Real.sin θ = -(x * Real.sin θ) by ring,
    Real.sin_neg]
  ring

theorem integral_schlafliMain_two_pi (x : ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, schlafliMain x θ) =
      2 * ∫ θ in (0 : ℝ)..Real.pi, schlafliMain x θ := by
  have hint : ∀ a b : ℝ,
      IntervalIntegrable (schlafliMain x) volume a b := by
    intro a b
    exact (by
      unfold schlafliMain
      fun_prop : Continuous (schlafliMain x)).intervalIntegrable _ _
  rw [show 2 * Real.pi = Real.pi + Real.pi by ring,
    ← intervalIntegral.integral_add_adjacent_intervals (hint 0 Real.pi)
      (hint Real.pi (Real.pi + Real.pi))]
  rw [(schlafliMain_periodic x).intervalIntegral_add_eq Real.pi 0]
  ring

theorem integral_besselDerivative_one (x : ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.sin (x * Real.cos θ) * Real.cos θ) =
      2 * ∫ θ in (0 : ℝ)..Real.pi, schlafliMain x θ := by
  let g : ℝ → ℝ := schlafliMain x
  have hshift : ∀ θ : ℝ,
      g (θ + Real.pi / 2) = Real.sin (x * Real.cos θ) * Real.cos θ := by
    intro θ
    dsimp [g, schlafliMain]
    rw [Real.sin_add_pi_div_two]
    ring
  calc
    (∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.sin (x * Real.cos θ) * Real.cos θ) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, g (θ + Real.pi / 2) := by
          apply intervalIntegral.integral_congr
          intro θ _
          exact (hshift θ).symm
    _ = ∫ θ in Real.pi / 2..2 * Real.pi + Real.pi / 2, g θ :=
      by simpa only [zero_add] using
        (intervalIntegral.integral_comp_add_right (a := (0 : ℝ))
          (b := 2 * Real.pi) g (Real.pi / 2))
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
      have hperiod2 : Function.Periodic g (2 * Real.pi) := by
        simpa [g, two_smul ℝ Real.pi] using
          (schlafliMain_periodic x).nsmul 2
      simpa only [zero_add, add_comm] using
        hperiod2.intervalIntegral_add_eq (Real.pi / 2) 0
    _ = 2 * ∫ θ in (0 : ℝ)..Real.pi, schlafliMain x θ :=
      integral_schlafliMain_two_pi x

/-- The Schläfli `J₁` is the negative first derivative of the angular `J₀`
kernel from `Erdos232`. -/
theorem besselJOne_eq_neg_besselDerivative_one (x : ℝ) :
    FixedRadius.besselJOne x = -Erdos232.besselDerivative 1 x := by
  rw [besselJOne_eq_schlafliMain, Erdos232.besselDerivative]
  norm_num only [Nat.cast_one, pow_one, one_mul]
  simp only [Real.cos_add_pi_div_two, neg_mul]
  rw [intervalIntegral.integral_neg, integral_besselDerivative_one]
  field_simp [Real.pi_ne_zero]

/-- The local `J₁` development inherits smoothness from the certified angular
kernel. -/
theorem hasDerivAt_besselJOne (x : ℝ) :
    HasDerivAt FixedRadius.besselJOne (-Erdos232.besselDerivative 2 x) x := by
  have hfun : FixedRadius.besselJOne =
      fun y : ℝ ↦ -Erdos232.besselDerivative 1 y := by
    funext y
    exact besselJOne_eq_neg_besselDerivative_one y
  rw [hfun]
  change HasDerivAt (-Erdos232.besselDerivative 1)
    (-Erdos232.besselDerivative 2 x) x
  exact (Erdos232.hasDerivAt_besselDerivative 1 x).neg

/-- A companion to `Erdos232.besselEnergy_controls`: the same Sonin energy
also controls the first derivative, hence `J₁`. -/
theorem besselEnergy_controls_one {x : ℝ} (hx : 0 < x) :
    x * Erdos232.besselDerivative 1 x ^ 2 / 4 ≤ Erdos232.besselEnergy x := by
  unfold Erdos232.besselEnergy
  have hs : 0 ≤
      (x * Erdos232.besselDerivative 1 x + Erdos232.besselDerivative 0 x) ^ 2 /
        (4 * x) := by positivity
  have ht : 0 ≤ x / 2 * Erdos232.besselDerivative 0 x ^ 2 := by positivity
  field_simp [ne_of_gt hx] at hs ht ⊢
  nlinarith

/-- Explicit square-root decay of the Schläfli `J₁` in the range covered by
the existing certified Sonin-energy estimate.  The rounded constant leaves
ample rational slack. -/
theorem abs_besselJOne_le_of_500_le {x : ℝ} (hx : 500 ≤ x) :
    |FixedRadius.besselJOne x| ≤ 51 / 1000 := by
  have hq : (3 * 157 / 50 : ℝ) ≤ x := by norm_num; linarith
  have hxpos : 0 < x := by linarith
  have hmono' := Erdos232.besselEnergy_antitoneOn
    (a := (3 * 157 / 50 : ℝ)) (by norm_num)
  have hmono : Erdos232.besselEnergy x ≤
      Erdos232.besselEnergy (3 * 157 / 50 : ℝ) :=
    hmono' (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hq) hq
  have hcontrol := besselEnergy_controls_one hxpos
  have hstart := Erdos232.besselEnergy_at_grid_start
  have hsquare : x * Erdos232.besselDerivative 1 x ^ 2 ≤ 32 / 25 := by
    nlinarith
  rw [besselJOne_eq_neg_besselDerivative_one, abs_neg]
  have habs : |Erdos232.besselDerivative 1 x| ^ 2 =
      Erdos232.besselDerivative 1 x ^ 2 := sq_abs _
  have hnonneg := abs_nonneg (Erdos232.besselDerivative 1 x)
  rw [← habs] at hsquare
  nlinarith [sq_nonneg (|Erdos232.besselDerivative 1 x| - 51 / 1000)]

/-- The certified tail estimate in a sign-symmetric form. -/
theorem abs_besselJOne_le_of_500_le_abs {x : ℝ} (hx : 500 ≤ |x|) :
    |FixedRadius.besselJOne x| ≤ 51 / 1000 := by
  rcases le_total 0 x with hxnonneg | hxnonpos
  · simpa [abs_of_nonneg hxnonneg] using
      (abs_besselJOne_le_of_500_le (x := x) (by simpa [abs_of_nonneg hxnonneg] using hx))
  · have hneg : 500 ≤ -x := by simpa [abs_of_nonpos hxnonpos] using hx
    simpa [FixedRadius.besselJOne_neg] using
      (abs_besselJOne_le_of_500_le (x := -x) hneg)

/-- The disk Fourier multiplier inherits the explicit `J₁` tail bound.
This controls high frequencies but, being an upper bound, does not by itself
remove the zeros of the prescribed-radius multiplier. -/
theorem abs_diskMultiplier_le_tail {r ρ : ℝ} (hρ : ρ ≠ 0)
    (htail : 500 ≤ |2 * Real.pi * r * ρ|) :
    |FixedRadius.diskMultiplier r ρ| ≤
      (51 / 1000) * (|r| / |ρ|) := by
  rw [FixedRadius.diskMultiplier_of_ne_zero hρ, abs_div, abs_mul]
  have hJ := abs_besselJOne_le_of_500_le_abs htail
  have hρnonneg : 0 ≤ |ρ| := abs_nonneg ρ
  calc
    |r| * |FixedRadius.besselJOne (2 * Real.pi * r * ρ)| / |ρ| ≤
        |r| * (51 / 1000) / |ρ| := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hJ (abs_nonneg r)) hρnonneg
    _ = (51 / 1000) * (|r| / |ρ|) := by ring

end

end BesselBridge
end Erdos989

#print axioms Erdos989.BesselBridge.besselJOne_eq_neg_besselDerivative_one
#print axioms Erdos989.BesselBridge.abs_besselJOne_le_of_500_le
#print axioms Erdos989.BesselBridge.abs_diskMultiplier_le_tail
