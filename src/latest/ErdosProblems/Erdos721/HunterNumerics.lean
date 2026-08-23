/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterFiniteConstruction

/-!
# Numerical estimates for Hunter's integral parameter family
-/

namespace Erdos721.HunterNumerics

open Filter Real
open scoped ENNReal Topology

open HunterParameters HunterAnnulus
open HunterDistributedCenters

/-- Repeating `M` independent trials in each of `B` groups reduces a miss
probability with success chance at least `1/M` to at most `2^{-B}`. -/
lemma one_sub_inv_pow_mul_le_half_pow (M B : ℕ) (hM : 0 < M) :
    (1 - (M : ℝ≥0∞)⁻¹) ^ (M * B) ≤ (1 / 2 : ℝ≥0∞) ^ B := by
  apply (ENNReal.toReal_le_toReal (by simp) (by simp)).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_pow]
  have hMinv : (M : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]
    exact_mod_cast hM
  rw [ENNReal.toReal_sub_of_le hMinv (by simp)]
  simp only [ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    one_div]
  norm_num only [ENNReal.toReal_ofNat]
  rw [pow_mul]
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hbase0 : 0 ≤ 1 - ((M : ℝ)⁻¹) := by
    rw [sub_nonneg, inv_le_one₀ hMreal]
    exact_mod_cast hM
  have htrial : (1 - ((M : ℝ)⁻¹)) ^ M ≤ Real.exp (-1) := by
    simpa [div_eq_mul_inv] using
      (Real.one_sub_div_pow_le_exp_neg (n := M) (t := 1)
        (by exact_mod_cast hM))
  calc
    ((1 - (M : ℝ)⁻¹) ^ M) ^ B ≤ (Real.exp (-1)) ^ B := by
      exact pow_le_pow_left₀ (pow_nonneg hbase0 M) htrial B
    _ ≤ (1 / 2 : ℝ) ^ B := by
      exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_half.le B

/-- A factor bounded by `2^a` is killed by more than `a` factors of one
half. -/
lemma mul_half_pow_lt_one_of_le_pow_two {A : ℝ≥0∞} {a B : ℕ}
    (hA : A ≤ 2 ^ a) (haB : a < B) :
    A * (1 / 2 : ℝ≥0∞) ^ B < 1 := by
  have hAtop : A ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) hA
  apply (ENNReal.toReal_lt_toReal
    (ENNReal.mul_ne_top hAtop (by simp)) (by simp)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow]
  simp only [ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    OfNat.ofNat_ne_zero, not_false_eq_true]
  have hAreal : A.toReal ≤ (2 : ℝ) ^ a := by
    exact ENNReal.toReal_mono (by simp) hA
  calc
    A.toReal * (1 / 2 : ℝ) ^ B ≤
        (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ B := by gcongr
    _ = (1 / 2 : ℝ) ^ (B - a) := by
      rw [show B = a + (B - a) by omega, pow_add]
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

lemma mul_half_pow_le_half_of_le_pow_two {A : ℝ≥0∞} {a B : ℕ}
    (hA : A ≤ 2 ^ a) (haB : a < B) :
    A * (1 / 2 : ℝ≥0∞) ^ B ≤ 1 / 2 := by
  have htop : A * (1 / 2 : ℝ≥0∞) ^ B ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ne_top_of_le_ne_top (by simp) hA
    · simp
  apply (ENNReal.toReal_le_toReal htop (by simp)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div]
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat]
  have hAreal : A.toReal ≤ (2 : ℝ) ^ a :=
    ENNReal.toReal_mono (by simp) hA
  calc
    A.toReal * (1 / 2 : ℝ) ^ B ≤
        (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ B := by gcongr
    _ = (1 / 2 : ℝ) ^ (B - a) := by
      rw [show B = a + (B - a) by omega, pow_add]
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ ≤ 1 / 2 := by
      rw [show B - a = 1 + (B - a - 1) by omega, pow_add]
      have hp : (1 / 2 : ℝ) ^ (B - a - 1) ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      simpa using
        (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 1 / 2))

lemma natCast_mul_inv_lt_half {A B : ℕ} (hB : 0 < B)
    (h : 2 * A < B) :
    (A : ℝ≥0∞) * (B : ℝ≥0∞)⁻¹ < 1 / 2 := by
  have htop : (A : ℝ≥0∞) * (B : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.natCast_ne_top A
    · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hB.ne')
  apply (ENNReal.toReal_lt_toReal htop (by simp)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat]
  rw [← div_eq_mul_inv,
    div_lt_iff₀ (by exact_mod_cast hB : (0 : ℝ) < B)]
  have hr : 2 * (A : ℝ) < B := by exact_mod_cast h
  nlinarith only [hr]

lemma natCast_mul_inv_le_half {A B : ℕ} (hB : 0 < B)
    (h : 2 * A ≤ B) :
    (A : ℝ≥0∞) * (B : ℝ≥0∞)⁻¹ ≤ 1 / 2 := by
  have htop : (A : ℝ≥0∞) * (B : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.natCast_ne_top A
    · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hB.ne')
  apply (ENNReal.toReal_le_toReal htop (by simp)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat]
  rw [← div_eq_mul_inv,
    div_le_iff₀ (by exact_mod_cast hB : (0 : ℝ) < B)]
  have hr : 2 * (A : ℝ) ≤ B := by exact_mod_cast h
  nlinarith only [hr]

lemma two_mul_pow_lt_pow {D a b : ℕ} (hD : 2 < D)
    (hab : a + 1 ≤ b) : 2 * D ^ a < D ^ b := by
  calc
    2 * D ^ a < D * D ^ a :=
      Nat.mul_lt_mul_of_pos_right hD (pow_pos (by omega) _)
    _ = D ^ (a + 1) := by rw [pow_succ]; ring
    _ ≤ D ^ b := Nat.pow_le_pow_right (by omega) hab

lemma two_mul_pow_le_pow {D a b : ℕ} (hD : 2 ≤ D)
    (hab : a + 1 ≤ b) : 2 * D ^ a ≤ D ^ b := by
  calc
    2 * D ^ a ≤ D * D ^ a := Nat.mul_le_mul_right _ hD
    _ = D ^ (a + 1) := by rw [pow_succ]; ring
    _ ≤ D ^ b := Nat.pow_le_pow_right (by omega) hab

/-- If the one-trial success probability is at least `1/M`, the preceding
grouping estimate remains valid. -/
lemma one_sub_pow_le_half_pow_of_inv_le
    {p : ℝ≥0∞} {S M B : ℕ} (hp : (M : ℝ≥0∞)⁻¹ ≤ p)
    (hp1 : p ≤ 1) (hS : S = M * B) (hM : 0 < M) :
    (1 - p) ^ S ≤ (1 / 2 : ℝ≥0∞) ^ B := by
  rw [hS]
  exact (pow_le_pow_left' (tsub_le_tsub_left hp 1) _).trans
    (one_sub_inv_pow_mul_le_half_pow M B hM)

/-- Frequency cutoff in the specialization. -/
def frequencyBound (D : ℕ) : ℕ := D ^ 20

/-- Rank threshold for bounded resonances. -/
def resonanceRank (D : ℕ) : ℕ := D / 100

/-- Phase-grid denominator. -/
def gridSize (D : ℕ) : ℕ := D ^ 6

/-- Half-length used by the signed orbit-difference argument. -/
def orbitLength (D : ℕ) : ℕ := D ^ (4800 * D)

/-- Very small character threshold. -/
noncomputable def resonanceThreshold (D : ℕ) : ℝ :=
  ((2 * D ^ (1000 * D) : ℕ) : ℝ)⁻¹

/-- Radius used both for phase distribution and for the Fourier cutoff. -/
noncomputable def phaseRadius (D : ℕ) : ℝ :=
  ((100 * D ^ 5 : ℕ) : ℝ)⁻¹

/-- Affine-separation radius. -/
noncomputable def separationRadius (D : ℕ) : ℝ := 4 * rho D

/-- Convenient upper bound for the orbit-hit displacement. -/
noncomputable def orbitError (D : ℕ) : ℝ := rho D / 10

/-- Number of trials used to group the phase-distribution miss event. -/
def phaseTrialGroup (D : ℕ) : ℕ := D ^ (3 * D / 50)

/-- Number of phase-distribution trial groups. -/
def phaseGroupCount (D : ℕ) : ℕ := D ^ (47 * D / 50)

/-- Number of shell-label trial groups. -/
def labelGroupCount (D : ℕ) : ℕ := D ^ (D / 50 + 4)

lemma dimension_ge_two (t : ℕ) : 2 ≤ dimension t := by
  simp only [dimension]
  omega

lemma dimension_ge_two_hundred (t : ℕ) : 200 ≤ dimension t := by
  simp only [dimension]
  omega

lemma resonanceRank_dimension (t : ℕ) :
    resonanceRank (dimension t) = 2 * (t + 1) := by
  rw [resonanceRank, show dimension t = 100 * (2 * (t + 1)) by
    simp only [dimension]; ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

lemma phaseTrial_exponent_dimension (t : ℕ) :
    3 * dimension t / 50 = 12 * (t + 1) := by
  rw [show 3 * dimension t = 50 * (12 * (t + 1)) by
    simp [dimension]; ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

lemma phaseGroup_exponent_dimension (t : ℕ) :
    47 * dimension t / 50 = 188 * (t + 1) := by
  rw [show 47 * dimension t = 50 * (188 * (t + 1)) by
    simp [dimension]; ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

lemma blockSize_eq_phase_groups (t : ℕ) :
    blockSize (dimension t) =
      phaseTrialGroup (dimension t) * phaseGroupCount (dimension t) := by
  rw [blockSize, phaseTrialGroup, phaseGroupCount, ← pow_add,
    phaseTrial_exponent_dimension, phaseGroup_exponent_dimension]
  rw [show dimension t = 12 * (t + 1) + 188 * (t + 1) by
    simp only [dimension]; ring]

lemma labelGroup_exponent_dimension (t : ℕ) :
    dimension t / 50 + 4 = 4 * t + 8 := by
  rw [dimension_div_fifty]
  omega

lemma blockCount_eq_label_groups (t : ℕ) :
    blockCount (dimension t) =
      shellCount (dimension t) * labelGroupCount (dimension t) := by
  rw [blockCount, shellCount, labelGroupCount, ← pow_add]
  rw [dimension_div_twenty_five, dimension_div_fifty]
  congr 1
  omega

lemma shellCount_mul_shellWidth_eq_rho (t : ℕ) :
    (shellCount (dimension t) : ℝ) * shellWidth (dimension t) =
      rho (dimension t) := by
  let D := dimension t
  have hDnat : 0 < D := by
    dsimp only [D]
    exact dimension_pos t
  have hD : (D : ℝ) ≠ 0 := by exact_mod_cast hDnat.ne'
  rw [shellCount_dimension, shellWidth, dimension_div_fifty, rho]
  push_cast
  rw [inv_pow]
  field_simp [hD]
  rw [← pow_add]
  congr 1

lemma sqrt_shellWidth_div_two_eq_stepThreshold (t : ℕ) :
    Real.sqrt (shellWidth (dimension t)) / 2 =
      stepThreshold (dimension t) := by
  have hq0 : 0 ≤ shellWidth (dimension t) := shellWidth_nonneg _
  have ht0 : 0 ≤ stepThreshold (dimension t) :=
    (stepThreshold_pos (dimension_pos t)).le
  have hsqrt0 : 0 ≤ Real.sqrt (shellWidth (dimension t)) :=
    Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (shellWidth (dimension t)) / 2) ^ 2 =
      shellWidth (dimension t) / 4 := by
    rw [div_pow, Real.sq_sqrt hq0]
    norm_num
  have htSq := stepThreshold_sq (dimension_pos t)
    (dvd_trans (by norm_num : 100 ∣ 200) (dimension_dvd t))
  nlinarith

lemma nat_pow_le_two_pow_mul (D e : ℕ) : D ^ e ≤ 2 ^ (D * e) := by
  calc
    D ^ e ≤ (2 ^ D) ^ e :=
      Nat.pow_le_pow_left (Nat.le_of_lt D.lt_two_pow_self) e
    _ = 2 ^ (D * e) := by rw [pow_mul]

lemma two_frequencyBound_add_one_le (t : ℕ) :
    2 * frequencyBound (dimension t) + 1 ≤ dimension t ^ 22 := by
  let D := dimension t
  have hD : 2 ≤ D := by simpa [D] using dimension_ge_two t
  have hD20 : 1 ≤ D ^ 20 := one_le_pow₀ (by omega)
  have hD2 : 3 ≤ D ^ 2 := by nlinarith [sq_nonneg (D - 2)]
  change 2 * D ^ 20 + 1 ≤ D ^ 22
  rw [show 22 = 20 + 2 by omega, pow_add]
  nlinarith

lemma card_phaseRequest_le_dimension_sq (t : ℕ) :
    Fintype.card (PhaseRequest (dimension t)
      (frequencyBound (dimension t)) (resonanceRank (dimension t))
      (gridSize (dimension t))) ≤ dimension t ^ (dimension t ^ 2) := by
  let D := dimension t
  let R := resonanceRank D
  have hQ : 1 ≤ gridSize D := by
    simp only [gridSize]
    exact one_le_pow₀ (by have := dimension_ge_two t; omega)
  have hraw := card_phaseRequest_le D (frequencyBound D) R (gridSize D) hQ
  have hfreq : 2 * frequencyBound D + 1 ≤ D ^ 22 := by
    simpa [D] using two_frequencyBound_add_one_le t
  have hgrid : gridSize D ≤ D ^ 6 := by rfl
  have hbound :
      ((2 * frequencyBound D + 1) ^ D) ^ R * gridSize D ^ R ≤
        D ^ (22 * D * R + 6 * R) := by
    calc
      _ ≤ ((D ^ 22) ^ D) ^ R * (D ^ 6) ^ R := by gcongr
      _ = D ^ (22 * D * R + 6 * R) := by
        simp only [← pow_mul, ← pow_add]
  have hexp : 22 * D * R + 6 * R ≤ D ^ 2 := by
    rw [show R = 2 * (t + 1) by
      simpa [R, D] using resonanceRank_dimension t]
    simp only [D, dimension]
    nlinarith [sq_nonneg (t + 1)]
  exact hraw.trans (hbound.trans (Nat.pow_le_pow_right (dimension_pos t) hexp))

lemma phaseGroupCount_gt_two_cube (t : ℕ) :
    2 * dimension t ^ 3 < phaseGroupCount (dimension t) := by
  let D := dimension t
  have hD : 200 ≤ D := by simpa [D] using dimension_ge_two_hundred t
  have hexp : 4 ≤ 47 * D / 50 := by
    rw [show 47 * D / 50 = 188 * (t + 1) by
      simpa [D] using phaseGroup_exponent_dimension t]
    omega
  have hpow : D ^ 4 ≤ phaseGroupCount D := by
    exact Nat.pow_le_pow_right (by omega) hexp
  have hcube : 2 * D ^ 3 < D ^ 4 := by
    rw [show D ^ 4 = D ^ 3 * D by ring]
    have hpos : 0 < D ^ 3 := pow_pos (by omega) _
    nlinarith
  exact hcube.trans_le hpow

lemma labelGroupCount_gt_cube (t : ℕ) :
    dimension t ^ 3 < labelGroupCount (dimension t) := by
  let D := dimension t
  have hD : 200 ≤ D := by simpa [D] using dimension_ge_two_hundred t
  have hexp : 4 ≤ D / 50 + 4 := by omega
  have hpow : D ^ 4 ≤ labelGroupCount D :=
    Nat.pow_le_pow_right (by omega) hexp
  have hcube : D ^ 3 < D ^ 4 := by
    rw [show D ^ 4 = D ^ 3 * D by ring]
    have hpos : 0 < D ^ 3 := pow_pos (by omega) _
    nlinarith
  exact hcube.trans_le hpow

lemma phaseTrialGroup_eq_pow_six_rank (t : ℕ) :
    phaseTrialGroup (dimension t) =
      (dimension t ^ 6) ^ resonanceRank (dimension t) := by
  rw [phaseTrialGroup, ← pow_mul]
  congr 1
  rw [phaseTrial_exponent_dimension, resonanceRank_dimension]
  ring

lemma ofReal_two_mul_phaseRadius (t : ℕ) :
    ENNReal.ofReal (2 * phaseRadius (dimension t)) =
      ((50 * dimension t ^ 5 : ℕ) : ℝ≥0∞)⁻¹ := by
  let D := dimension t
  have hDpos : 0 < D := by simpa [D] using dimension_pos t
  have hdenNat : 0 < 50 * D ^ 5 :=
    Nat.mul_pos (by norm_num) (pow_pos hDpos _)
  have hden : (0 : ℝ) < (50 * D ^ 5 : ℕ) := by exact_mod_cast hdenNat
  have heq : 2 * phaseRadius D = ((50 * D ^ 5 : ℕ) : ℝ)⁻¹ := by
    rw [phaseRadius]
    push_cast
    field_simp
    ring
  rw [show dimension t = D by rfl, heq,
    ENNReal.ofReal_inv_of_pos hden, ENNReal.ofReal_natCast]

lemma phaseTrialGroup_inv_le_success (t : ℕ) :
    (phaseTrialGroup (dimension t) : ℝ≥0∞)⁻¹ ≤
      ENNReal.ofReal (2 * phaseRadius (dimension t)) ^
        resonanceRank (dimension t) := by
  let D := dimension t
  let R := resonanceRank D
  have hden : 50 * D ^ 5 ≤ D ^ 6 := by
    rw [show D ^ 6 = D ^ 5 * D by ring]
    have hpow : 0 < D ^ 5 := pow_pos (dimension_pos t) _
    have hD : 50 ≤ D := by
      have := dimension_ge_two_hundred t
      omega
    simpa [mul_comm] using Nat.mul_le_mul_left (D ^ 5) hD
  have hbase : ((D ^ 6 : ℕ) : ℝ≥0∞)⁻¹ ≤
      ((50 * D ^ 5 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.inv_le_inv]
    exact_mod_cast hden
  rw [show phaseTrialGroup (dimension t) = (D ^ 6) ^ R by
      simpa [D, R] using phaseTrialGroup_eq_pow_six_rank t,
    show ENNReal.ofReal (2 * phaseRadius (dimension t)) =
        ((50 * D ^ 5 : ℕ) : ℝ≥0∞)⁻¹ by
      simpa [D] using ofReal_two_mul_phaseRadius t]
  push_cast
  change (((D : ℝ≥0∞) ^ 6) ^ R)⁻¹ ≤
    ((50 * (D : ℝ≥0∞) ^ 5)⁻¹) ^ R
  rw [ENNReal.inv_pow]
  have hbase' : ((D : ℝ≥0∞) ^ 6)⁻¹ ≤
      (50 * (D : ℝ≥0∞) ^ 5)⁻¹ := by
    simpa using hbase
  exact pow_le_pow_left' hbase' R

lemma phase_success_le_one (t : ℕ) :
    ENNReal.ofReal (2 * phaseRadius (dimension t)) ^
      resonanceRank (dimension t) ≤ 1 := by
  rw [ofReal_two_mul_phaseRadius]
  apply pow_le_one₀
  · positivity
  · rw [ENNReal.inv_le_one]
    norm_cast
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ (dimension_ne_zero t)))

lemma phase_request_mul_blockCount_le_two_pow (t : ℕ) :
    (Fintype.card (PhaseRequest (dimension t)
        (frequencyBound (dimension t)) (resonanceRank (dimension t))
        (gridSize (dimension t))) * blockCount (dimension t) : ℕ) ≤
      2 ^ (2 * dimension t ^ 3) := by
  let D := dimension t
  have hcard := card_phaseRequest_le_dimension_sq t
  have hY : blockCount D ≤ D ^ (D ^ 2) := by
    rw [blockCount]
    apply Nat.pow_le_pow_right (dimension_pos t)
    have hD : D / 25 ≤ D := Nat.div_le_self _ _
    exact hD.trans (Nat.le_pow (by omega))
  calc
    _ ≤ D ^ (D ^ 2) * D ^ (D ^ 2) := Nat.mul_le_mul hcard hY
    _ = D ^ (2 * D ^ 2) := by
      rw [← pow_add, show D ^ 2 + D ^ 2 = 2 * D ^ 2 by ring]
    _ ≤ 2 ^ (D * (2 * D ^ 2)) := nat_pow_le_two_pow_mul D _
    _ = 2 ^ (2 * D ^ 3) := by
      rw [show D * (2 * D ^ 2) = 2 * D ^ 3 by ring]

lemma phase_miss_term_lt_one (t : ℕ) :
    (Fintype.card (PhaseRequest (dimension t)
        (frequencyBound (dimension t)) (resonanceRank (dimension t))
        (gridSize (dimension t))) * blockCount (dimension t) : ℕ) *
      (1 - ENNReal.ofReal (2 * phaseRadius (dimension t)) ^
        resonanceRank (dimension t)) ^ blockSize (dimension t) < 1 := by
  let D := dimension t
  let M := phaseTrialGroup D
  let B := phaseGroupCount D
  have hmiss :
      (1 - ENNReal.ofReal (2 * phaseRadius D) ^ resonanceRank D) ^
          blockSize D ≤ (1 / 2 : ℝ≥0∞) ^ B := by
    apply one_sub_pow_le_half_pow_of_inv_le
      (phaseTrialGroup_inv_le_success t) (phase_success_le_one t)
    · simpa [D, M, B] using blockSize_eq_phase_groups t
    · dsimp only [M, phaseTrialGroup]
      exact pow_pos (dimension_pos t) _
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hmiss (by positivity))
  apply mul_half_pow_lt_one_of_le_pow_two
  · norm_cast
    exact phase_request_mul_blockCount_le_two_pow t
  · simpa [D, B] using phaseGroupCount_gt_two_cube t

lemma phase_miss_term_le_half (t : ℕ) :
    (Fintype.card (PhaseRequest (dimension t)
        (frequencyBound (dimension t)) (resonanceRank (dimension t))
        (gridSize (dimension t))) * blockCount (dimension t) : ℕ) *
      (1 - ENNReal.ofReal (2 * phaseRadius (dimension t)) ^
        resonanceRank (dimension t)) ^ blockSize (dimension t) ≤ 1 / 2 := by
  let D := dimension t
  let M := phaseTrialGroup D
  let B := phaseGroupCount D
  have hmiss :
      (1 - ENNReal.ofReal (2 * phaseRadius D) ^ resonanceRank D) ^
          blockSize D ≤ (1 / 2 : ℝ≥0∞) ^ B := by
    apply one_sub_pow_le_half_pow_of_inv_le
      (phaseTrialGroup_inv_le_success t) (phase_success_le_one t)
    · simpa [D, M, B] using blockSize_eq_phase_groups t
    · dsimp only [M, phaseTrialGroup]
      exact pow_pos (dimension_pos t) _
  apply (mul_le_mul_of_nonneg_left hmiss (by positivity)).trans
  apply mul_half_pow_le_half_of_le_pow_two
  · norm_cast
    exact phase_request_mul_blockCount_le_two_pow t
  · simpa [D, B] using phaseGroupCount_gt_two_cube t

lemma ofReal_two_mul_separationRadius (t : ℕ) :
    ENNReal.ofReal (2 * separationRadius (dimension t)) =
      8 * (dimension t : ℝ≥0∞)⁻¹ ^ 4 := by
  let D := dimension t
  have hD : (0 : ℝ) < D := by exact_mod_cast dimension_pos t
  have heq : 2 * separationRadius D = 8 * ((D : ℝ)⁻¹) ^ 4 := by
    simp only [separationRadius, rho]
    ring
  rw [show dimension t = D by rfl, heq,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
    ENNReal.ofReal_ofNat,
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (D : ℝ)⁻¹),
    ENNReal.ofReal_inv_of_pos hD, ENNReal.ofReal_natCast]

lemma center_product_cube_mul_eight_pow_lt (t : ℕ) :
    2 * (blockCount (dimension t) * blockSize (dimension t)) ^ 3 *
        8 ^ dimension t <
      dimension t ^ (4 * dimension t) := by
  let D := dimension t
  have hD : 200 ≤ D := by simpa [D] using dimension_ge_two_hundred t
  have hcenter : blockCount D * blockSize D = centerCount D := by
    simpa [D] using (centerCount_eq_blocks t).symm
  have heven : D = 2 * (D / 2) := by
    dsimp only [D, dimension]
    omega
  have heighth : 8 ^ D ≤ D ^ (D / 2) := by
    have heq8 : 8 ^ D = (8 ^ 2) ^ (D / 2) := by
      have hpowEq : 8 ^ D = 8 ^ (2 * (D / 2)) :=
        congrArg (fun n : ℕ ↦ 8 ^ n) heven
      calc
        8 ^ D = 8 ^ (2 * (D / 2)) := hpowEq
        _ = (8 ^ 2) ^ (D / 2) := by rw [pow_mul]
    rw [heq8]
    exact Nat.pow_le_pow_left (by norm_num; omega) _
  have hexp : 3 * (26 * D / 25) + D / 2 + 1 ≤ 4 * D := by
    rw [show 26 * D / 25 = 208 * (t + 1) by
      simpa [D] using center_exponent_dimension t]
    dsimp only [D, dimension]
    omega
  rw [hcenter, centerCount]
  let A := (D ^ (26 * D / 25)) ^ 3
  let C := D ^ (D / 2)
  have hACpos : 0 < A * C :=
    Nat.mul_pos (pow_pos (pow_pos (by omega) _) _) (pow_pos (by omega) _)
  calc
    2 * A * 8 ^ D ≤ 2 * A * C := Nat.mul_le_mul_left _ heighth
    _ = 2 * (A * C) := by ring
    _ < D * (A * C) := Nat.mul_lt_mul_of_pos_right (by omega) hACpos
    _ = D * (D ^ (26 * D / 25)) ^ 3 * D ^ (D / 2) := by
      dsimp only [A, C]
      ring
    _ = D ^ (3 * (26 * D / 25) + D / 2 + 1) := by
      let e := 26 * D / 25
      let f := D / 2
      have hpow : D * (D ^ e) ^ 3 * D ^ f =
          D ^ (3 * e + f + 1) := by
        calc
          D * (D ^ e) ^ 3 * D ^ f =
              D ^ 1 * D ^ (e * 3) * D ^ f := by
                rw [pow_one, pow_mul]
          _ = D ^ (1 + e * 3 + f) := by
                rw [pow_add, pow_add]
          _ = D ^ (3 * e + f + 1) := by
                rw [show 1 + e * 3 + f = 3 * e + f + 1 by omega]
      simpa only [e, f] using hpow
    _ ≤ D ^ (4 * D) := Nat.pow_le_pow_right (by omega) hexp

lemma separation_term_lt_half (t : ℕ) :
    (blockCount (dimension t) * blockSize (dimension t)) ^ 3 *
      ENNReal.ofReal (2 * separationRadius (dimension t)) ^
        dimension t < 1 / 2 := by
  let D := dimension t
  have hDpos : (0 : ℝ) < D := by exact_mod_cast dimension_pos t
  have hnumNat := center_product_cube_mul_eight_pow_lt t
  have hnum :
      2 * ((blockCount D * blockSize D : ℕ) : ℝ) ^ 3 * 8 ^ D <
        (D : ℝ) ^ (4 * D) := by
    have hcast : ((2 * (blockCount D * blockSize D) ^ 3 * 8 ^ D : ℕ) : ℝ) <
        ((D ^ (4 * D) : ℕ) : ℝ) := Nat.cast_lt.mpr hnumNat
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast
    simpa only [Nat.cast_mul] using hcast
  rw [ofReal_two_mul_separationRadius, show dimension t = D by rfl]
  have hDneENN : (D : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show D ≠ 0 by simpa [D] using dimension_ne_zero t)
  have htop :
      (blockCount D * blockSize D : ℝ≥0∞) ^ 3 *
          (8 * (D : ℝ≥0∞)⁻¹ ^ 4) ^ D ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.pow_ne_top
      exact ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top (blockCount D))
        (ENNReal.natCast_ne_top (blockSize D))
    · apply ENNReal.pow_ne_top
      apply ENNReal.mul_ne_top
      · norm_num
      · apply ENNReal.pow_ne_top
        exact ENNReal.inv_ne_top.mpr hDneENN
  apply (ENNReal.toReal_lt_toReal htop (by simp)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, ENNReal.toReal_inv, ENNReal.toReal_div,
    ENNReal.toReal_one]
  norm_num only
  rw [show (8 * ((D : ℝ)⁻¹) ^ 4) ^ D =
      8 ^ D * (((D : ℝ)⁻¹) ^ 4) ^ D by rw [mul_pow]]
  have hden : 0 < (D : ℝ) ^ (4 * D) := pow_pos hDpos _
  rw [show ((D : ℝ)⁻¹ ^ 4) ^ D =
      ((D : ℝ) ^ (4 * D))⁻¹ by
    rw [← pow_mul, inv_pow]]
  rw [← div_eq_mul_inv, ← mul_div_assoc]
  let x : ℝ := ((blockCount D : ℝ) * blockSize D) ^ 3 * 8 ^ D
  let z : ℝ := (D : ℝ) ^ (4 * D)
  change x / z < 1 / 2
  have hz : 0 < z := by simpa only [z] using hden
  apply (div_lt_iff₀ hz).2
  have hx : 2 * x < z := by
    rw [Nat.cast_mul] at hnum
    simpa only [x, z, mul_assoc] using hnum
  nlinarith only [hx]

lemma center_union_small (t : ℕ) :
    (Fintype.card (PhaseRequest (dimension t)
        (frequencyBound (dimension t)) (resonanceRank (dimension t))
        (gridSize (dimension t))) * blockCount (dimension t) : ℕ) *
        (1 - ENNReal.ofReal (2 * phaseRadius (dimension t)) ^
          resonanceRank (dimension t)) ^ blockSize (dimension t) +
      (blockCount (dimension t) * blockSize (dimension t)) ^ 3 *
        ENNReal.ofReal (2 * separationRadius (dimension t)) ^
          dimension t < 1 := by
  let A : ℝ≥0∞ :=
    (Fintype.card (PhaseRequest (dimension t)
        (frequencyBound (dimension t)) (resonanceRank (dimension t))
        (gridSize (dimension t))) * blockCount (dimension t) : ℕ) *
      (1 - ENNReal.ofReal (2 * phaseRadius (dimension t)) ^
        resonanceRank (dimension t)) ^ blockSize (dimension t)
  let B : ℝ≥0∞ :=
    (blockCount (dimension t) * blockSize (dimension t)) ^ 3 *
      ENNReal.ofReal (2 * separationRadius (dimension t)) ^ dimension t
  change A + B < 1
  have hA : A ≤ 1 / 2 := by
    simpa only [A] using phase_miss_term_le_half t
  have hB : B < 1 / 2 := by
    simpa only [B] using separation_term_lt_half t
  have hstrict : (1 / 2 : ℝ≥0∞) + B < 1 / 2 + 1 / 2 :=
    (ENNReal.add_lt_add_iff_left (by simp)).2 hB
  exact (add_le_add_left hA B).trans_lt
    (hstrict.trans_eq (ENNReal.add_halves 1))

lemma intervalLength_sq_le_two_pow_cube (t : ℕ) :
    intervalLength (dimension t) ^ 2 ≤ 2 ^ (dimension t ^ 3) := by
  let D := dimension t
  let e := D ^ 2 / 200
  have hD : 0 < D := by simpa [D] using dimension_pos t
  have he : e + e ≤ D ^ 2 := by
    dsimp only [e]
    have hdiv : D ^ 2 / 200 ≤ D ^ 2 := Nat.div_le_self _ _
    omega
  calc
    intervalLength (dimension t) ^ 2 = D ^ (e + e) := by
      simp only [intervalLength, D, e, pow_two, ← pow_add]
    _ ≤ D ^ (D ^ 2) := Nat.pow_le_pow_right hD he
    _ ≤ 2 ^ (D * D ^ 2) := nat_pow_le_two_pow_mul D (D ^ 2)
    _ = 2 ^ (dimension t ^ 3) := by
      rw [show D * D ^ 2 = D ^ 3 by ring]

lemma shellCount_pos (t : ℕ) : 0 < shellCount (dimension t) := by
  rw [shellCount_dimension]
  exact pow_pos (dimension_pos t) _

lemma label_miss_term_lt_one (t : ℕ) :
    (intervalLength (dimension t) ^ 2 : ℕ) *
      (1 - (shellCount (dimension t) : ℝ≥0∞)⁻¹) ^
        blockCount (dimension t) < 1 := by
  let D := dimension t
  let K := shellCount D
  let B := labelGroupCount D
  have hmiss :
      (1 - (K : ℝ≥0∞)⁻¹) ^ blockCount D ≤
        (1 / 2 : ℝ≥0∞) ^ B := by
    apply one_sub_inv_pow_mul_le_half_pow K B
      (by simpa [D, K] using shellCount_pos t) |>.trans'
    rw [show blockCount D = K * B by
      simpa [D, K, B] using blockCount_eq_label_groups t]
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hmiss (by positivity))
  apply mul_half_pow_lt_one_of_le_pow_two
  · norm_cast
    exact intervalLength_sq_le_two_pow_cube t
  · simpa [D, B] using labelGroupCount_gt_cube t

lemma direction_coefficient_le_dimension_sq (t : ℕ) :
    intervalLength (dimension t) *
        ((2 * frequencyBound (dimension t) + 1) ^ dimension t) ^
          resonanceRank (dimension t) ≤
      dimension t ^ (dimension t ^ 2) := by
  let D := dimension t
  let R := resonanceRank D
  let e := D ^ 2 / 200
  have hD : 0 < D := by simpa [D] using dimension_pos t
  have hfreq : 2 * frequencyBound D + 1 ≤ D ^ 22 := by
    simpa [D] using two_frequencyBound_add_one_le t
  have hexp : e + 22 * D * R ≤ D ^ 2 := by
    rw [show e = 200 * (t + 1) ^ 2 by
      simpa [e, D] using dimension_sq_div_two_hundred t,
      show R = 2 * (t + 1) by
        simpa [R, D] using resonanceRank_dimension t]
    dsimp only [D, dimension]
    nlinarith [sq_nonneg (t + 1)]
  calc
    intervalLength (dimension t) *
        ((2 * frequencyBound (dimension t) + 1) ^ dimension t) ^
          resonanceRank (dimension t) =
        D ^ e * ((2 * frequencyBound D + 1) ^ D) ^ R := by rfl
    _ ≤ D ^ e * ((D ^ 22) ^ D) ^ R := by gcongr
    _ = D ^ (e + 22 * D * R) := by
      simp only [← pow_mul, ← pow_add]
    _ ≤ D ^ (D ^ 2) := Nat.pow_le_pow_right hD hexp

lemma ofReal_two_mul_resonanceThreshold (t : ℕ) :
    ENNReal.ofReal (2 * resonanceThreshold (dimension t)) =
      ((dimension t ^ (1000 * dimension t) : ℕ) : ℝ≥0∞)⁻¹ := by
  let D := dimension t
  have hD : (0 : ℝ) < D := by exact_mod_cast dimension_pos t
  have hP : (0 : ℝ) < (D ^ (1000 * D) : ℕ) := by
    exact_mod_cast pow_pos (dimension_pos t) (1000 * D)
  have heq : 2 * resonanceThreshold D =
      ((D ^ (1000 * D) : ℕ) : ℝ)⁻¹ := by
    simp only [resonanceThreshold]
    push_cast
    field_simp
  rw [show dimension t = D by rfl, heq,
    ENNReal.ofReal_inv_of_pos hP, ENNReal.ofReal_natCast]

lemma direction_resonance_term_lt_half (t : ℕ) :
    (intervalLength (dimension t) *
        ((2 * frequencyBound (dimension t) + 1) ^ dimension t) ^
          resonanceRank (dimension t) : ℕ) *
      ENNReal.ofReal (2 * resonanceThreshold (dimension t)) ^
        resonanceRank (dimension t) < 1 / 2 := by
  let D := dimension t
  let R := resonanceRank D
  have hD : 2 < D := by
    have := dimension_ge_two_hundred t
    omega
  have hcoef := direction_coefficient_le_dimension_sq t
  have hexp : D ^ 2 + 1 ≤ 1000 * D * R := by
    rw [show R = 2 * (t + 1) by
      simpa [R, D] using resonanceRank_dimension t]
    dsimp only [D, dimension]
    nlinarith [sq_nonneg (t + 1)]
  rw [ofReal_two_mul_resonanceThreshold]
  calc
    _ ≤ (D ^ (D ^ 2) : ℕ) *
        (((D ^ (1000 * D) : ℕ) : ℝ≥0∞)⁻¹) ^ R := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcoef
      · positivity
    _ = (D ^ (D ^ 2) : ℕ) *
        ((D ^ (1000 * D * R) : ℕ) : ℝ≥0∞)⁻¹ := by
      push_cast
      rw [← ENNReal.inv_pow, ← pow_mul]
    _ < 1 / 2 := by
      apply natCast_mul_inv_lt_half (pow_pos (dimension_pos t) _)
      exact two_mul_pow_lt_pow hD hexp

lemma ofReal_two_mul_stepThreshold (t : ℕ) :
    ENNReal.ofReal (2 * stepThreshold (dimension t)) =
      ((dimension t ^ (dimension t / 100) : ℕ) : ℝ≥0∞)⁻¹ := by
  let D := dimension t
  have hP : (0 : ℝ) < (D ^ (D / 100) : ℕ) := by
    exact_mod_cast pow_pos (dimension_pos t) (D / 100)
  have heq : 2 * stepThreshold D =
      ((D ^ (D / 100) : ℕ) : ℝ)⁻¹ := by
    simp only [stepThreshold]
    push_cast
    field_simp
  rw [show dimension t = D by rfl, heq,
    ENNReal.ofReal_inv_of_pos hP, ENNReal.ofReal_natCast]

lemma direction_step_term_le_half (t : ℕ) :
    (intervalLength (dimension t) : ℕ) *
      ENNReal.ofReal (2 * stepThreshold (dimension t)) ^ dimension t ≤
        1 / 2 := by
  let D := dimension t
  let e := D ^ 2 / 200
  have hD : 2 ≤ D := by simpa [D] using dimension_ge_two t
  have hexp : e + 1 ≤ (D / 100) * D := by
    rw [show e = 200 * (t + 1) ^ 2 by
      simpa [e, D] using dimension_sq_div_two_hundred t]
    dsimp only [D, dimension]
    rw [show 200 * (t + 1) / 100 = 2 * (t + 1) by omega]
    nlinarith [sq_nonneg (t + 1)]
  rw [ofReal_two_mul_stepThreshold]
  calc
    _ = (D ^ e : ℕ) *
        ((D ^ ((D / 100) * D) : ℕ) : ℝ≥0∞)⁻¹ := by
      change ((D ^ e : ℕ) : ℝ≥0∞) *
          (((D ^ (D / 100) : ℕ) : ℝ≥0∞)⁻¹) ^ D = _
      push_cast
      rw [← ENNReal.inv_pow, pow_mul]
    _ ≤ 1 / 2 := by
      apply natCast_mul_inv_le_half (pow_pos (dimension_pos t) _)
      exact two_mul_pow_le_pow hD hexp

lemma direction_union_small (t : ℕ) :
    (intervalLength (dimension t) *
        ((2 * frequencyBound (dimension t) + 1) ^ dimension t) ^
          resonanceRank (dimension t) : ℕ) *
        ENNReal.ofReal (2 * resonanceThreshold (dimension t)) ^
          resonanceRank (dimension t) +
      intervalLength (dimension t) *
        ENNReal.ofReal (2 * stepThreshold (dimension t)) ^ dimension t < 1 := by
  let A : ℝ≥0∞ :=
    (intervalLength (dimension t) *
        ((2 * frequencyBound (dimension t) + 1) ^ dimension t) ^
          resonanceRank (dimension t) : ℕ) *
      ENNReal.ofReal (2 * resonanceThreshold (dimension t)) ^
        resonanceRank (dimension t)
  let B : ℝ≥0∞ :=
    intervalLength (dimension t) *
      ENNReal.ofReal (2 * stepThreshold (dimension t)) ^ dimension t
  change A + B < 1
  have hA : A < 1 / 2 := by
    simpa only [A] using direction_resonance_term_lt_half t
  have hB : B ≤ 1 / 2 := by
    simpa only [B] using direction_step_term_le_half t
  have hstrict : A + (1 / 2 : ℝ≥0∞) < 1 / 2 + 1 / 2 :=
    (ENNReal.add_lt_add_iff_right (by simp)).2 hA
  exact (add_le_add_right hB A).trans_lt
    (hstrict.trans_eq (ENNReal.add_halves 1))

lemma four_mul_frequency_phase_sq (t : ℕ) :
    4 * (frequencyBound (dimension t) : ℝ) *
        phaseRadius (dimension t) ^ 2 =
      (dimension t : ℝ) ^ 10 / 2500 := by
  let D := dimension t
  have hD : (D : ℝ) ≠ 0 := by exact_mod_cast dimension_ne_zero t
  simp only [frequencyBound, phaseRadius]
  push_cast
  field_simp [hD]
  ring

lemma cutoff_log_bound (t : ℕ) :
    Real.log
        (2 * (2 * frequencyBound (dimension t) + 1 : ℝ) ^ dimension t) ≤
      (dimension t : ℝ) ^ 10 / 2500 := by
  let D := dimension t
  have hDnat : 200 ≤ D := by simpa [D] using dimension_ge_two_hundred t
  have hD : (200 : ℝ) ≤ D := by exact_mod_cast hDnat
  have hDpos : (0 : ℝ) < D := by positivity
  have hfreqNat : 2 * frequencyBound D + 1 ≤ D ^ 22 := by
    simpa [D] using two_frequencyBound_add_one_le t
  have hfreq : (2 * frequencyBound D + 1 : ℝ) ≤ (D : ℝ) ^ 22 := by
    exact_mod_cast hfreqNat
  let A : ℝ := 2 * (2 * frequencyBound D + 1 : ℝ) ^ D
  let B : ℝ := 2 * (D : ℝ) ^ (22 * D)
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hfreq
  have hbasepos : (0 : ℝ) < 2 * (frequencyBound D : ℝ) + 1 := by
    have hf : (0 : ℝ) ≤ frequencyBound D := by
      exact_mod_cast Nat.zero_le (frequencyBound D)
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) hf) zero_lt_one
  have hApos : 0 < A := by
    dsimp only [A]
    exact mul_pos (by norm_num) (pow_pos hbasepos _)
  have hBpos : 0 < B := by
    dsimp only [B]
    exact mul_pos (by norm_num) (pow_pos hDpos _)
  have hAB : A ≤ B := by
    dsimp only [A, B]
    have hp : (2 * (frequencyBound D : ℝ) + 1) ^ D ≤
        ((D : ℝ) ^ 22) ^ D :=
      pow_le_pow_left₀ hbasepos.le hfreq D
    calc
      2 * (2 * frequencyBound D + 1 : ℝ) ^ D ≤
          2 * ((D : ℝ) ^ 22) ^ D :=
        mul_le_mul_of_nonneg_left hp (by norm_num)
      _ = 2 * (D : ℝ) ^ (22 * D) := by rw [pow_mul]
  have hlogD : Real.log (D : ℝ) ≤ D := Real.log_le_self hDpos.le
  have hlogB : Real.log B =
      Real.log 2 + (22 * (D : ℝ)) * Real.log (D : ℝ) := by
    dsimp only [B]
    rw [Real.log_mul (by norm_num) (pow_pos hDpos _).ne', Real.log_pow]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  have hlogBbound : Real.log B ≤ 1 + 22 * (D : ℝ) ^ 2 := by
    rw [hlogB]
    have hlog2 : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
    have hmul : (22 * D : ℝ) * Real.log (D : ℝ) ≤ 22 * D ^ 2 := by
      have hcoef : (0 : ℝ) ≤ 22 * (D : ℝ) :=
        mul_nonneg (by norm_num) hDpos.le
      have hmul' := mul_le_mul_of_nonneg_left hlogD hcoef
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      calc
        22 * (D : ℝ) * Real.log (D : ℝ) ≤
            22 * (D : ℝ) * (D : ℝ) := hmul'
        _ = 22 * (D : ℝ) ^ 2 := by ring
    exact add_le_add hlog2 hmul
  have hD8 : (57500 : ℝ) ≤ (D : ℝ) ^ 8 := by
    calc
      (57500 : ℝ) ≤ 200 ^ 8 := by norm_num
      _ ≤ (D : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) hD 8
  have hDsq : (1 : ℝ) ≤ (D : ℝ) ^ 2 := by
    exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ D)
  have hpoly : 1 + 22 * (D : ℝ) ^ 2 ≤ (D : ℝ) ^ 10 / 2500 := by
    have hsmall : 2500 * (1 + 22 * (D : ℝ) ^ 2) ≤
        57500 * (D : ℝ) ^ 2 := by
      have h2500 : (2500 : ℝ) ≤ 2500 * (D : ℝ) ^ 2 := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hDsq (show (0 : ℝ) ≤ 2500 by norm_num))
      calc
        2500 * (1 + 22 * (D : ℝ) ^ 2) =
            2500 + 55000 * (D : ℝ) ^ 2 := by ring
        _ ≤ 2500 * (D : ℝ) ^ 2 + 55000 * (D : ℝ) ^ 2 := by
          exact add_le_add h2500 (le_refl _)
        _ = 57500 * (D : ℝ) ^ 2 := by ring
    have hmul := mul_le_mul_of_nonneg_left hD8 (sq_nonneg (D : ℝ))
    have htotal : 2500 * (1 + 22 * (D : ℝ) ^ 2) ≤
        (D : ℝ) ^ 10 := by
      calc
        _ ≤ 57500 * (D : ℝ) ^ 2 := hsmall
        _ ≤ (D : ℝ) ^ 2 * (D : ℝ) ^ 8 := by
          simpa only [mul_comm] using hmul
        _ = (D : ℝ) ^ 10 := by ring
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2500)]
    simpa only [mul_comm] using htotal
  change Real.log A ≤ (D : ℝ) ^ 10 / 2500
  exact (Real.log_le_log hApos hAB).trans (hlogBbound.trans hpoly)

lemma cutoff_decay (t : ℕ) :
    2 * (2 * frequencyBound (dimension t) + 1) ^ dimension t *
      Real.exp (-4 * frequencyBound (dimension t) *
        phaseRadius (dimension t) ^ 2) ≤ 1 := by
  let D := dimension t
  let A : ℝ := 2 * (2 * frequencyBound D + 1 : ℝ) ^ D
  let X : ℝ := (D : ℝ) ^ 10 / 2500
  have hbasepos : (0 : ℝ) < 2 * (frequencyBound D : ℝ) + 1 := by
    have hf : (0 : ℝ) ≤ frequencyBound D := by
      exact_mod_cast Nat.zero_le (frequencyBound D)
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) hf) zero_lt_one
  have hApos : 0 < A := by
    dsimp only [A]
    exact mul_pos (by norm_num) (pow_pos hbasepos _)
  have hlog : Real.log A ≤ X := by
    simpa only [A, X, D] using cutoff_log_bound t
  have hAexp : A ≤ Real.exp X :=
    (Real.log_le_iff_le_exp hApos).mp hlog
  have hX : 4 * (frequencyBound (dimension t) : ℝ) *
      phaseRadius (dimension t) ^ 2 = X := by
    simpa only [X, D] using four_mul_frequency_phase_sq t
  have hneg : (-4 : ℝ) * frequencyBound (dimension t) *
      phaseRadius (dimension t) ^ 2 = -X := by
    calc
      (-4 : ℝ) * frequencyBound (dimension t) *
          phaseRadius (dimension t) ^ 2 =
        -(4 * frequencyBound (dimension t) *
          phaseRadius (dimension t) ^ 2) := by ring
      _ = -X := congrArg Neg.neg hX
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  change A * Real.exp ((-4 : ℝ) * frequencyBound (dimension t) *
      phaseRadius (dimension t) ^ 2) ≤ 1
  rw [hneg]
  calc
    A * Real.exp (-X) ≤ Real.exp X * Real.exp (-X) := by gcongr
    _ = 1 := by rw [← Real.exp_add]; simp

lemma large_orbit_inequality (t : ℕ) :
    (2 * (2 * frequencyBound (dimension t) + 1) ^ dimension t : ℝ) *
        (2 * resonanceThreshold (dimension t))⁻¹ ^ 2 <
      (orbitLength (dimension t) : ℝ) ^ 2 := by
  let D := dimension t
  have hD : 2 < D := by
    have := dimension_ge_two_hundred t
    omega
  have hfreq : 2 * frequencyBound D + 1 ≤ D ^ 22 := by
    simpa [D] using two_frequencyBound_add_one_le t
  have heps : 2 * resonanceThreshold D =
      ((D ^ (1000 * D) : ℕ) : ℝ)⁻¹ := by
    simp only [resonanceThreshold]
    push_cast
    field_simp
  have hNat :
      2 * (2 * frequencyBound D + 1) ^ D *
          (D ^ (1000 * D)) ^ 2 <
        (D ^ (4800 * D)) ^ 2 := by
    calc
      _ ≤ 2 * (D ^ 22) ^ D * (D ^ (1000 * D)) ^ 2 := by gcongr
      _ = 2 * D ^ (2022 * D) := by
        rw [← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
        rw [show 22 * D + 1000 * D * 2 = 2022 * D by omega]
      _ < D ^ (9600 * D) := by
        apply two_mul_pow_lt_pow hD
        omega
      _ = D ^ (4800 * D * 2) := by
        rw [show 9600 * D = 4800 * D * 2 by omega]
      _ = (D ^ (4800 * D)) ^ 2 := pow_mul D (4800 * D) 2
  rw [show dimension t = D by rfl, heps, inv_inv]
  simp only [orbitLength]
  exact_mod_cast hNat

end Erdos721.HunterNumerics
