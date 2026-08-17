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

import ErdosProblems.Erdos444.FiniteLargeValue
import ErdosProblems.Erdos444.ScaleBounds

/-!
# Cofinal high-growth scales for Erdős Problem 444

This file packages the routine asymptotic and algebraic passage from the
finite large-value theorem to tail-unbounded power-normalized ratios.  The
only problem-specific hypothesis left is the existence of cofinally many
cutoffs at which the few-large-prime part has at most half of the reciprocal
mass.  The high-growth branch supplies exactly that retention estimate.
-/

open Filter

namespace Erdos444

/-- The base-four natural logarithm tends to infinity. -/
theorem tendsto_baseFourLog_atTop :
    Tendsto (fun X : ℕ ↦ Nat.log 4 X) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro J
  refine ⟨4 ^ J, ?_⟩
  intro X hX
  have hmono := Nat.log_mono_right (b := 4) hX
  simpa [Nat.log_pow (by norm_num : 1 < 4)] using hmono

theorem tendsto_baseFourLog_cast_atTop :
    Tendsto (fun X : ℕ ↦ (Nat.log 4 X : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_baseFourLog_atTop

/-- Every positive fixed power of the real-cast base-four logarithm tends
to infinity. -/
theorem tendsto_baseFourLog_cast_pow_atTop (d : ℕ) (hd : d ≠ 0) :
    Tendsto (fun X : ℕ ↦ (Nat.log 4 X : ℝ) ^ d) atTop atTop :=
  (tendsto_pow_atTop hd).comp tendsto_baseFourLog_cast_atTop

/-- The exact exponent identity used with moment order `m²` and
`q = 2*k+2`. -/
theorem baseFourScale_power_identity (m k : ℕ) :
    (m : ℝ) ^ 4 * (m : ℝ) ^ (4 * k) =
      (((m ^ 2 : ℕ) : ℝ) ^ (2 * k + 2)) := by
  norm_num only [Nat.cast_pow]
  rw [← pow_add, ← pow_mul]
  congr 1
  omega

/-- Abstract high-growth-scale transfer.

For `q = 2*k+2` and `b = q+2`, suppose the few-large-prime mass is retained
at cofinally many cutoffs.  The remaining hypotheses of `finite_large_value`
hold eventually by `ScaleBounds`.  Its numerator contributes `m^(4*k+4)`,
whereas the reciprocal mass at the product cutoff contributes at most
`m^(4*k)` to the denominator.  The spare factor `m^4` tends to infinity. -/
theorem tailUnbounded_ratioNat_of_cofinal_finite_large_value_retention
    (A : Set ℕ) (k : ℕ)
    (hdiv : tailUnbounded (reciprocalMassNat A))
    (hretain : ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧
      let m := Nat.log 4 X
      let q := 2 * k + 2
      let b := q + 2
      (∑ a ∈ fewRoughFactorsUpTo A X (m ^ 2) (8 * b), (a : ℝ)⁻¹) ≤
        reciprocalMassNat A (X + 1) / 2) :
    tailUnbounded (ratioNat A k) := by
  intro C Z
  by_cases hC : C < 0
  · exact ⟨Z, le_rfl, hC.trans_le (ratioNat_nonneg A k Z)⟩
  have hC0 : 0 ≤ C := le_of_not_gt hC
  obtain ⟨S, -, hS⟩ := hdiv 1 0
  have hpow : ∀ᶠ X : ℕ in atTop, C < (Nat.log 4 X : ℝ) ^ 4 :=
    (tendsto_baseFourLog_cast_pow_atTop 4 (by norm_num)).eventually_gt_atTop C
  have hevent : ∀ᶠ X : ℕ in atTop,
      2 ≤ Nat.log 4 X ∧
      (Nat.log 4 X) ^ 2 ≤ X ∧
      Erdos697.PrimeWindow.reciprocalMass ((Nat.log 4 X) ^ 2) X ≤
        (Nat.log 4 X : ℝ) ∧
      reciprocalMassNat A (X ^ ((Nat.log 4 X) ^ 2) + 1) ≤
        (Nat.log 4 X : ℝ) ^ 4 ∧
      Z ≤ X ∧ S ≤ X ∧ C < (Nat.log 4 X : ℝ) ^ 4 := by
    filter_upwards [eventually_two_le_baseFourLog,
      eventually_baseFourLog_sq_le,
      eventually_primeWindowMass_baseFourLog_sq_le,
      eventually_reciprocalMassNat_pow_baseFourLog_sq_le_four A,
      eventually_ge_atTop Z, eventually_ge_atTop S, hpow] with X hm hmX hwindow hmassY hZX hSX hCX
    exact ⟨hm, hmX, hwindow, hmassY, hZX, hSX, hCX⟩
  rw [eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  obtain ⟨X, hNX, hretained⟩ := hretain N
  have hdata := hN X hNX
  let m := Nat.log 4 X
  let q := 2 * k + 2
  let b := q + 2
  let Y := X ^ (m ^ 2) + 1
  have hm : 2 ≤ m := hdata.1
  have hmX : m ^ 2 ≤ X := hdata.2.1
  have hwindow : Erdos697.PrimeWindow.reciprocalMass (m ^ 2) X ≤ (m : ℝ) :=
    hdata.2.2.1
  have hmassY : reciprocalMassNat A Y ≤ (m : ℝ) ^ 4 := hdata.2.2.2.1
  have hZX : Z ≤ X := hdata.2.2.2.2.1
  have hSX : S ≤ X := hdata.2.2.2.2.2.1
  have hCX : C < (m : ℝ) ^ 4 := hdata.2.2.2.2.2.2
  have hXpos : 0 < X := by nlinarith
  have hXpow : X ≤ X ^ (m ^ 2) := by
    have hexp : 1 ≤ m ^ 2 := by nlinarith
    simpa using Nat.pow_le_pow_right hXpos hexp
  have hXY : X + 1 ≤ Y := Nat.add_le_add_right hXpow 1
  have hFone : 1 ≤ reciprocalMassNat A (X + 1) := by
    exact hS.le.trans ((reciprocalMassNat_mono A) (hSX.trans (Nat.le_succ X)))
  have hFpos : 0 < reciprocalMassNat A (X + 1) := zero_lt_one.trans_le hFone
  have hb : q + 2 ≤ b := le_rfl
  have hlarge : (((m ^ 2 : ℕ) : ℝ) ^ q) * reciprocalMassNat A (X + 1) ≤
      (maxDivisorCountNat A Y : ℝ) := by
    exact finite_large_value A X m b q hm hmX hb hwindow hretained hFpos
  have hmassYpos : 0 < reciprocalMassNat A Y :=
    hFpos.trans_le (reciprocalMassNat_mono A hXY)
  have hdenpos : 0 < reciprocalMassNat A Y ^ k := pow_pos hmassYpos k
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hdenle : reciprocalMassNat A Y ^ k ≤ (m : ℝ) ^ (4 * k) := by
    calc
      reciprocalMassNat A Y ^ k ≤ ((m : ℝ) ^ 4) ^ k :=
        pow_le_pow_left₀ (reciprocalMassNat_nonneg A Y) hmassY k
      _ = (m : ℝ) ^ (4 * k) := by rw [pow_mul]
  have hscale : C * reciprocalMassNat A Y ^ k < ((m ^ 2 : ℕ) : ℝ) ^ q := by
    calc
      C * reciprocalMassNat A Y ^ k ≤ C * (m : ℝ) ^ (4 * k) :=
        mul_le_mul_of_nonneg_left hdenle hC0
      _ < (m : ℝ) ^ 4 * (m : ℝ) ^ (4 * k) :=
        mul_lt_mul_of_pos_right hCX (pow_pos hm0 (4 * k))
      _ = ((m ^ 2 : ℕ) : ℝ) ^ q := by
        exact baseFourScale_power_identity m k
  have hnum : C * reciprocalMassNat A Y ^ k <
      (maxDivisorCountNat A Y : ℝ) := by
    calc
      C * reciprocalMassNat A Y ^ k < ((m ^ 2 : ℕ) : ℝ) ^ q := hscale
      _ ≤ ((m ^ 2 : ℕ) : ℝ) ^ q * reciprocalMassNat A (X + 1) := by
        exact le_mul_of_one_le_right (by positivity) hFone
      _ ≤ (maxDivisorCountNat A Y : ℝ) := hlarge
  refine ⟨Y, hZX.trans (hXpow.trans (Nat.le_succ _)), ?_⟩
  rw [ratioNat]
  exact (lt_div_iff₀ hdenpos).mpr hnum

/-- Failure of the shifted iterated-log bound gives the cofinal retention
hypothesis required by
`tailUnbounded_ratioNat_of_cofinal_finite_large_value_retention`.

The analytic few-factor bound has degree `t+1`, where
`t = 8 * ((2*k+2)+2)`.  Applying failure of the corresponding global bound
with coefficient twice the analytic constant makes the discarded mass at
most half of the full mass. -/
theorem cofinal_finite_large_value_retention_of_not_shifted_bound
    (A : Set ℕ) (k : ℕ)
    (hhigh : ¬ ∃ D : ℝ, 0 ≤ D ∧ ∃ U : ℕ, ∀ X : ℕ, U ≤ X →
      reciprocalMassNat A X ≤
        D * ((Nat.log 4 (Nat.log 4 X) : ℝ) + 1) ^
          (8 * ((2 * k + 2) + 2) + 1)) :
    ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧
      let m := Nat.log 4 X
      let q := 2 * k + 2
      let b := q + 2
      (∑ a ∈ fewRoughFactorsUpTo A X (m ^ 2) (8 * b), (a : ℝ)⁻¹) ≤
        reciprocalMassNat A (X + 1) / 2 := by
  let q := 2 * k + 2
  let b := q + 2
  let t := 8 * b
  obtain ⟨D, hD, U, hanalytic⟩ :=
    exists_smallPrimeEulerProduct_mul_truncatedPrimePowerExp_le_baseFourPow t
  have hfail : ∀ V : ℕ, ¬ ∀ X : ℕ, V ≤ X →
      reciprocalMassNat A X ≤
        (2 * D) * ((Nat.log 4 (Nat.log 4 X) : ℝ) + 1) ^ (t + 1) := by
    intro V hV
    apply hhigh
    refine ⟨2 * D, mul_nonneg (by norm_num) hD, V, ?_⟩
    simpa [q, b, t, Nat.cast_add, Nat.cast_one] using hV
  intro N
  have hnot := hfail (max N U)
  push Not at hnot
  obtain ⟨X, hX, hmass⟩ := hnot
  have hNX : N ≤ X := (le_max_left N U).trans hX
  have hUX : U ≤ X := (le_max_right N U).trans hX
  refine ⟨X, hNX, ?_⟩
  dsimp only
  have hfew := fewRoughFactorsUpTo_reciprocalMass_le
    A X ((Nat.log 4 X) ^ 2) t
  have han := hanalytic X hUX
  let s : ℝ := ((Nat.log 4 (Nat.log 4 X) + 1 : ℕ) : ℝ)
  have hdiscard :
      (∑ a ∈ fewRoughFactorsUpTo A X ((Nat.log 4 X) ^ 2) t, (a : ℝ)⁻¹) ≤
        D * s ^ (t + 1) := by
    simpa [one_div, s, Nat.cast_add, Nat.cast_one] using hfew.trans han
  have hmass' : 2 * D * s ^ (t + 1) < reciprocalMassNat A X := by
    simpa [s, Nat.cast_add, Nat.cast_one] using hmass
  have hmono : reciprocalMassNat A X ≤ reciprocalMassNat A (X + 1) :=
    reciprocalMassNat_mono A (Nat.le_succ X)
  change (∑ a ∈ fewRoughFactorsUpTo A X ((Nat.log 4 X) ^ 2)
      (8 * ((2 * k + 2) + 2)), (a : ℝ)⁻¹) ≤
    reciprocalMassNat A (X + 1) / 2
  dsimp [q, b, t] at hdiscard hmass' s ⊢
  exact hdiscard.trans (by linarith)

/-- High-growth branch in its final convenient form: failure of the one
fixed shifted iterated-log bound needed for moment order `2*k+2` implies
tail-unbounded ratios. -/
theorem tailUnbounded_ratioNat_of_not_shifted_iteratedLog_bound
    (A : Set ℕ) (k : ℕ)
    (hdiv : tailUnbounded (reciprocalMassNat A))
    (hhigh : ¬ ∃ D : ℝ, 0 ≤ D ∧ ∃ U : ℕ, ∀ X : ℕ, U ≤ X →
      reciprocalMassNat A X ≤
        D * ((Nat.log 4 (Nat.log 4 X) : ℝ) + 1) ^
          (8 * ((2 * k + 2) + 2) + 1)) :
    tailUnbounded (ratioNat A k) :=
  tailUnbounded_ratioNat_of_cofinal_finite_large_value_retention A k hdiv
    (cofinal_finite_large_value_retention_of_not_shifted_bound A k hhigh)

end Erdos444
