/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib

/-!
# Integral parameters for Hunter's construction

Hunter takes `rho = D⁻⁴`, `N = D^(D²/200)`, and a progression length
`X = N^(960200 / D)`.  Restricting to dimensions divisible by `200`
removes every floor and fractional exponent.  This is harmless for the
asymptotic argument and makes the finite construction substantially cleaner.
-/

namespace Erdos721.HunterParameters

open Filter Real
open scoped Topology

/-- The cofinal sequence of dimensions on which all Hunter exponents are
integral.  The offset keeps the dimension positive at every index. -/
def dimension (t : ℕ) : ℕ := 200 * (t + 1)

/-- Radius of the small Euclidean ball in the torus model. -/
noncomputable def rho (D : ℕ) : ℝ := (D : ℝ)⁻¹ ^ 4

/-- Number of random centers.  For `200 ∣ D`, this is
`rho^(-(1/4+1/100)D)`. -/
def centerCount (D : ℕ) : ℕ := D ^ (26 * D / 25)

/-- Number of independent center blocks. -/
def blockCount (D : ℕ) : ℕ := D ^ (D / 25)

/-- Size of one block of centers. -/
def blockSize (D : ℕ) : ℕ := D ^ D

/-- Ambient interval length. -/
def intervalLength (D : ℕ) : ℕ := D ^ (D ^ 2 / 200)

/-- The largest radial-shell index. -/
def shellCount (D : ℕ) : ℕ := D ^ (D / 50 - 4)

/-- Blue progression length in the final coloring. -/
def progressionLength (D : ℕ) : ℕ := D ^ (4801 * D)

@[simp] lemma dimension_pos (t : ℕ) : 0 < dimension t := by
  simp [dimension]

@[simp] lemma dimension_ne_zero (t : ℕ) : dimension t ≠ 0 :=
  (dimension_pos t).ne'

lemma dimension_dvd (t : ℕ) : 200 ∣ dimension t := by
  exact dvd_mul_right 200 (t + 1)

lemma twenty_five_dvd_dimension (t : ℕ) : 25 ∣ dimension t := by
  exact dvd_trans (by norm_num : 25 ∣ 200) (dimension_dvd t)

lemma fifty_dvd_dimension (t : ℕ) : 50 ∣ dimension t := by
  exact dvd_trans (by norm_num : 50 ∣ 200) (dimension_dvd t)

lemma dimension_sq_div_two_hundred (t : ℕ) :
    dimension t ^ 2 / 200 = 200 * (t + 1) ^ 2 := by
  rw [show dimension t ^ 2 = 200 * (200 * (t + 1) ^ 2) by
    simp only [dimension]
    ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

lemma dimension_div_twenty_five (t : ℕ) :
    dimension t / 25 = 8 * (t + 1) := by
  rw [show dimension t = 25 * (8 * (t + 1)) by
    simp only [dimension]
    ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

lemma dimension_div_fifty (t : ℕ) :
    dimension t / 50 = 4 * (t + 1) := by
  rw [show dimension t = 50 * (4 * (t + 1)) by
    simp only [dimension]
    ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

lemma center_exponent_dimension (t : ℕ) :
    26 * dimension t / 25 = 208 * (t + 1) := by
  rw [show 26 * dimension t = 25 * (208 * (t + 1)) by
    simp only [dimension]
    ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

lemma centerCount_eq_blocks (t : ℕ) :
    centerCount (dimension t) =
      blockCount (dimension t) * blockSize (dimension t) := by
  have hexponent :
      26 * dimension t / 25 = dimension t / 25 + dimension t := by
    rw [center_exponent_dimension, dimension_div_twenty_five]
    simp only [dimension]
    omega
  rw [centerCount, blockCount, blockSize, ← pow_add, hexponent]

lemma intervalLength_dimension (t : ℕ) :
    intervalLength (dimension t) =
      dimension t ^ (200 * (t + 1) ^ 2) := by
  rw [intervalLength, dimension_sq_div_two_hundred]

lemma progressionLength_dimension (t : ℕ) :
    progressionLength (dimension t) =
      dimension t ^ (960200 * (t + 1)) := by
  rw [progressionLength, show 4801 * dimension t = 960200 * (t + 1) by
    simp only [dimension]
    ring]

lemma shellCount_dimension (t : ℕ) :
    shellCount (dimension t) = dimension t ^ (4 * t) := by
  rw [shellCount, dimension_div_fifty]
  congr 1

lemma rho_pos {D : ℕ} (hD : 0 < D) : 0 < rho D := by
  exact pow_pos (inv_pos.mpr (by exact_mod_cast hD)) _

lemma rho_nonneg (D : ℕ) : 0 ≤ rho D := by
  exact pow_nonneg (inv_nonneg.mpr (by positivity)) _

lemma rho_le_one {D : ℕ} (hD : 1 ≤ D) : rho D ≤ 1 := by
  simp only [rho]
  have h : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hinv : (D : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by exact_mod_cast hD)).2 h
  exact pow_le_one₀ (by positivity) hinv

lemma progressionLength_pos {D : ℕ} (hD : 0 < D) :
    0 < progressionLength D := by
  exact pow_pos hD _

lemma intervalLength_pos {D : ℕ} (hD : 0 < D) :
    0 < intervalLength D := by
  exact pow_pos hD _

lemma blockCount_pos {D : ℕ} (hD : 0 < D) : 0 < blockCount D := by
  exact pow_pos hD _

lemma blockSize_pos {D : ℕ} (hD : 0 < D) : 0 < blockSize D := by
  exact pow_pos hD _

lemma centerCount_pos {D : ℕ} (hD : 0 < D) : 0 < centerCount D := by
  exact pow_pos hD _

/-- The chosen dimensions tend to infinity. -/
lemma tendsto_dimension : Tendsto dimension atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b, fun a ha ↦ ?_⟩
  dsimp only [dimension]
  omega

/-- The ambient interval lengths tend to infinity along the construction
dimensions. -/
lemma tendsto_intervalLength_dimension :
    Tendsto (fun t ↦ intervalLength (dimension t)) atTop atTop := by
  apply tendsto_atTop_mono'
    (f₁ := dimension)
    (f₂ := fun t ↦ intervalLength (dimension t))
  · filter_upwards [eventually_ge_atTop (0 : ℕ)] with t _
    rw [intervalLength_dimension]
    exact Nat.le_pow (by positivity)
  · exact tendsto_dimension

/-- The progression lengths tend to infinity along the construction
dimensions. -/
lemma tendsto_progressionLength_dimension :
    Tendsto (fun t ↦ progressionLength (dimension t)) atTop atTop := by
  apply tendsto_atTop_mono'
    (f₁ := dimension)
    (f₂ := fun t ↦ progressionLength (dimension t))
  · filter_upwards [eventually_ge_atTop (0 : ℕ)] with t _
    rw [progressionLength_dimension]
    exact Nat.le_pow (by positivity)
  · exact tendsto_dimension

end Erdos721.HunterParameters
