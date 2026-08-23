/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterNumerics

/-!
# Specialization of Hunter's finite construction

This file discharges the geometric and elementary positivity conditions for
the integral parameter family and invokes the abstract finite construction.
-/

namespace Erdos721.HunterSpecialization

open Real
open HunterParameters HunterAnnulus HunterNumerics
open HunterColoring HunterFiniteConstruction

lemma phaseRadius_pos_dimension (t : ℕ) :
    0 < phaseRadius (dimension t) := by
  unfold phaseRadius
  apply inv_pos.mpr
  exact_mod_cast Nat.mul_pos (by norm_num) (pow_pos (dimension_pos t) 5)

lemma two_phaseRadius_le_one (t : ℕ) :
    2 * phaseRadius (dimension t) ≤ 1 := by
  let D := dimension t
  have hden : (2 : ℝ) ≤ 100 * (D : ℝ) ^ 5 := by
    have hDnat : 1 ≤ D := by
      dsimp only [D]
      exact dimension_pos t
    have hD : (1 : ℝ) ≤ D := by exact_mod_cast hDnat
    have hp : (1 : ℝ) ≤ (D : ℝ) ^ 5 := one_le_pow₀ hD
    nlinarith
  simp only [phaseRadius]
  push_cast
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  simpa only [D] using hden

lemma resonanceThreshold_pos_dimension (t : ℕ) :
    0 < resonanceThreshold (dimension t) := by
  unfold resonanceThreshold
  apply inv_pos.mpr
  exact_mod_cast Nat.mul_pos (by norm_num)
    (pow_pos (dimension_pos t) (1000 * dimension t))

lemma two_resonanceThreshold_le_one (t : ℕ) :
    2 * resonanceThreshold (dimension t) ≤ 1 := by
  let D := dimension t
  have hden : (2 : ℝ) ≤ 2 * (D : ℝ) ^ (1000 * D) := by
    have hDnat : 1 ≤ D := by
      dsimp only [D]
      exact dimension_pos t
    have hD : (1 : ℝ) ≤ D := by exact_mod_cast hDnat
    have hp : (1 : ℝ) ≤ (D : ℝ) ^ (1000 * D) := one_le_pow₀ hD
    nlinarith
  simp only [resonanceThreshold]
  push_cast
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  exact hden

lemma two_stepThreshold_le_one (t : ℕ) :
    2 * stepThreshold (dimension t) ≤ 1 := by
  let D := dimension t
  have hden : (2 : ℝ) ≤ 2 * (D : ℝ) ^ (D / 100) := by
    have hDnat : 1 ≤ D := by
      dsimp only [D]
      exact dimension_pos t
    have hD : (1 : ℝ) ≤ D := by exact_mod_cast hDnat
    have hp : (1 : ℝ) ≤ (D : ℝ) ^ (D / 100) := one_le_pow₀ hD
    nlinarith
  simp only [stepThreshold]
  push_cast
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  exact hden

lemma rho_le_sixteenth (t : ℕ) :
    rho (dimension t) ≤ 1 / 16 := by
  let D := dimension t
  have hD : (2 : ℝ) ≤ D := by exact_mod_cast dimension_ge_two t
  have hpow : (16 : ℝ) ≤ (D : ℝ) ^ 4 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hD 4
    norm_num at hp
    exact hp
  change (D : ℝ)⁻¹ ^ 4 ≤ 1 / 16
  rw [inv_pow, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) hpow

lemma two_separationRadius_le_one (t : ℕ) :
    2 * separationRadius (dimension t) ≤ 1 := by
  unfold separationRadius
  have h := rho_le_sixteenth t
  nlinarith

lemma gridSize_ge_two (t : ℕ) : 2 ≤ gridSize (dimension t) := by
  unfold gridSize
  have hD := dimension_ge_two t
  exact hD.trans (Nat.le_pow (by norm_num))

lemma grid_mesh_le_phaseRadius (t : ℕ) :
    (gridSize (dimension t) : ℝ)⁻¹ ≤ phaseRadius (dimension t) := by
  let D := dimension t
  have hDpos : (0 : ℝ) < D := by exact_mod_cast dimension_pos t
  have hden : (100 : ℝ) * (D : ℝ) ^ 5 ≤ (D : ℝ) ^ 6 := by
    rw [show (D : ℝ) ^ 6 = (D : ℝ) ^ 5 * D by ring]
    have h100 : (100 : ℝ) ≤ D := by
      exact_mod_cast (show 100 ≤ D by
        have := dimension_ge_two_hundred t
        omega)
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left h100 (pow_nonneg hDpos.le 5))
  change (((D ^ 6 : ℕ) : ℝ)⁻¹) ≤
    (((100 * D ^ 5 : ℕ) : ℝ)⁻¹)
  push_cast
  exact (inv_le_inv₀ (pow_pos hDpos 6) (by positivity)).2 hden

lemma orbit_error_bound (t : ℕ) :
    2 * Real.sqrt (resonanceRank (dimension t)) *
          phaseRadius (dimension t) +
        Real.sqrt (dimension t) * phaseRadius (dimension t) ≤
      orbitError (dimension t) := by
  let D := dimension t
  let R := resonanceRank D
  let p := phaseRadius D
  have hRleD : R ≤ D := Nat.div_le_self _ _
  have hsqrtRD : Real.sqrt (R : ℝ) ≤ Real.sqrt (D : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hRleD)
  have hDoneNat : 1 ≤ D := by
    dsimp only [D]
    exact dimension_pos t
  have hDone : (1 : ℝ) ≤ D := by exact_mod_cast hDoneNat
  have hsqrtD : Real.sqrt (D : ℝ) ≤ D :=
    (Real.sqrt_le_self_iff).2 (Or.inr hDone)
  have hsqrtR : Real.sqrt (R : ℝ) ≤ D := hsqrtRD.trans hsqrtD
  have hp0 : 0 ≤ p := (phaseRadius_pos_dimension t).le
  have hfirst : 2 * Real.sqrt (R : ℝ) * p ≤ 2 * (D : ℝ) * p := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrtR (by norm_num)) hp0
  have hsecond : Real.sqrt (D : ℝ) * p ≤ (D : ℝ) * p :=
    mul_le_mul_of_nonneg_right hsqrtD hp0
  have hsum : 2 * Real.sqrt (R : ℝ) * p + Real.sqrt (D : ℝ) * p ≤
      3 * (D : ℝ) * p := by
    calc
      _ ≤ 2 * (D : ℝ) * p + (D : ℝ) * p := add_le_add hfirst hsecond
      _ = 3 * (D : ℝ) * p := by ring
  have hnumeric : 3 * (D : ℝ) * p ≤ orbitError D := by
    have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast dimension_ne_zero t
    dsimp only [p]
    simp only [phaseRadius, orbitError, rho]
    push_cast
    field_simp [hDne]
    norm_num
  simpa only [D, R, p] using hsum.trans hnumeric

lemma orbit_error_lt_shells (t : ℕ) :
    orbitError (dimension t) <
      (shellCount (dimension t) : ℝ) * shellWidth (dimension t) := by
  rw [shellCount_mul_shellWidth_eq_rho]
  unfold orbitError
  have hρ := rho_pos (dimension_pos t)
  linarith

lemma orbit_error_lt_half (t : ℕ) :
    orbitError (dimension t) < 1 / 2 := by
  have hρ := rho_le_sixteenth t
  unfold orbitError
  linarith

lemma orbitLength_ge_two (t : ℕ) : 2 ≤ orbitLength (dimension t) := by
  unfold orbitLength
  have hD := dimension_ge_two t
  exact hD.trans (Nat.le_pow (by positivity))

lemma shell_endpoint (t : ℕ) (k : Fin (shellCount (dimension t))) :
    ((k.val + 1 : ℕ) : ℝ) * shellWidth (dimension t) ≤
      rho (dimension t) := by
  have hk : (((k.val + 1 : ℕ) : ℝ)) ≤ shellCount (dimension t) := by
    exact_mod_cast k.isLt
  have hq0 := shellWidth_nonneg (dimension t)
  calc
    ((k.val + 1 : ℕ) : ℝ) * shellWidth (dimension t) ≤
        (shellCount (dimension t) : ℝ) * shellWidth (dimension t) :=
      mul_le_mul_of_nonneg_right hk hq0
    _ = rho (dimension t) := shellCount_mul_shellWidth_eq_rho t

lemma shell_outer_quarter (t : ℕ)
    (k : Fin (shellCount (dimension t))) :
    2 * (k.val : ℝ) * shellWidth (dimension t) +
        shellWidth (dimension t) ≤ 1 / 4 := by
  let q := shellWidth (dimension t)
  let K := shellCount (dimension t)
  have hq0 : 0 ≤ q := shellWidth_nonneg _
  have hkNat : k.val + 1 ≤ K := by exact k.isLt
  have hstep : 2 * (k.val : ℝ) + 1 ≤ 2 * (K : ℝ) := by
    exact_mod_cast (show 2 * k.val + 1 ≤ 2 * K by omega)
  have hρ := rho_le_sixteenth t
  calc
    2 * (k.val : ℝ) * q + q = (2 * (k.val : ℝ) + 1) * q := by ring
    _ ≤ (2 * (K : ℝ)) * q := mul_le_mul_of_nonneg_right hstep hq0
    _ = 2 * ((K : ℝ) * q) := by ring
    _ = 2 * rho (dimension t) := by
      rw [show (K : ℝ) * q = rho (dimension t) by
        simpa only [K, q] using shellCount_mul_shellWidth_eq_rho t]
    _ ≤ 1 / 4 := by linarith

/-- The unconditional finite Hunter coloring at the integral parameter
`dimension t`. -/
theorem exists_hunter_badSet_dimension (t : ℕ) :
    ∃ red : ℕ → Prop,
      ThreeAPFreeBelow (intervalLength (dimension t)) red ∧
        HitsEveryAP (intervalLength (dimension t))
          (2 * orbitLength (dimension t) - 1) red := by
  apply exists_hunter_badSet
      (D := dimension t)
      (H := frequencyBound (dimension t))
      (R := resonanceRank (dimension t))
      (Y := blockCount (dimension t))
      (S := blockSize (dimension t))
      (Q := gridSize (dimension t))
      (K := shellCount (dimension t))
      (N := intervalLength (dimension t))
      (L := orbitLength (dimension t))
      (phaseRadius := phaseRadius (dimension t))
      (cutoffRadius := phaseRadius (dimension t))
      (epsilon := resonanceThreshold (dimension t))
      (delta := separationRadius (dimension t))
      (q := shellWidth (dimension t))
      (rhoOuter := rho (dimension t))
      (tau := stepThreshold (dimension t))
      (error := orbitError (dimension t))
  · exact (phaseRadius_pos_dimension t).le
  · exact two_phaseRadius_le_one t
  · exact (mul_nonneg (by norm_num) (rho_nonneg _))
  · exact two_separationRadius_le_one t
  · exact gridSize_ge_two t
  · exact grid_mesh_le_phaseRadius t
  · exact center_union_small t
  · exact (resonanceThreshold_pos_dimension t).le
  · exact two_resonanceThreshold_le_one t
  · exact (stepThreshold_pos (dimension_pos t)).le
  · exact two_stepThreshold_le_one t
  · exact direction_union_small t
  · exact (phaseRadius_pos_dimension t).le
  · exact cutoff_decay t
  · exact resonanceThreshold_pos_dimension t
  · exact large_orbit_inequality t
  · exact shellWidth_pos (dimension_pos t)
  · exact orbit_error_bound t
  · exact orbit_error_lt_shells t
  · exact orbit_error_lt_half t
  · exact orbitLength_ge_two t
  · exact shellCount_pos t
  · exact label_miss_term_lt_one t
  · exact shell_endpoint t
  · exact shell_outer_quarter t
  · rfl
  · have hρ := rho_le_sixteenth t
    unfold separationRadius
    linarith
  · have hρ := rho_le_sixteenth t
    linarith
  · exact (sqrt_shellWidth_div_two_eq_stepThreshold t).le
  · have h := two_stepThreshold_le_one t
    linarith

end Erdos721.HunterSpecialization
