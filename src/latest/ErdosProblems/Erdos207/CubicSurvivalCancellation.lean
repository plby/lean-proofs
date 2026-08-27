/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedSharpScheduleEstimates

/-!
# Telescoping and cubic cancellation for the initial schedule

The retrospective point-selection term contains the cube of the survival
product.  These lemmas isolate the two purely scalar steps used in the power
hierarchy: a one-step ratio estimate telescopes, and a quadratic initial
pair count turns a cubic ratio into the required inverse ambient scale.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

lemma le_five_mul_div_three {x : ℕ} (hx : 3 ≤ x) :
    x ≤ 5 * (x / 3) := by omega

/-- Losing at most half of the upper availability in one effective deletion
keeps the sharp survival factor uniformly above one half. -/
lemma half_le_boundedSharpSurvivalTheta
    {M d K : ℕ} (hM : 0 < M) (hhalf : 2 * (d - K) ≤ M) :
    (2 : ℝ≥0)⁻¹ ≤ boundedSharpSurvivalTheta M d K := by
  rw [← NNReal.coe_le_coe]
  simp only [boundedSharpSurvivalTheta, NNReal.coe_inv, NNReal.coe_ofNat,
    NNReal.coe_mul, NNReal.coe_natCast]
  have heff : d - K ≤ M := by omega
  have hhalf' : (2 : ℝ) * (d - K : ℕ) ≤ M := by exact_mod_cast hhalf
  rw [Nat.cast_sub heff]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  field_simp
  nlinarith

/-- Consequently the reciprocal of any fixed power of the factor is bounded
by the corresponding power of two. -/
lemma inv_pow_boundedSharpSurvivalTheta_le
    {M d K r : ℕ} (hM : 0 < M) (hhalf : 2 * (d - K) ≤ M) :
    (boundedSharpSurvivalTheta M d K ^ r)⁻¹ ≤ (2 : ℝ≥0) ^ r := by
  rw [← inv_pow]
  apply pow_le_pow_left'
  have hhalfPos : (0 : ℝ≥0) < (2 : ℝ≥0)⁻¹ := by positivity
  have hthetaPos : 0 < boundedSharpSurvivalTheta M d K :=
    hhalfPos.trans_le (half_le_boundedSharpSurvivalTheta hM hhalf)
  rw [inv_le_iff_one_le_mul₀ hthetaPos]
  calc
    1 = (2 : ℝ≥0) * (2 : ℝ≥0)⁻¹ := by norm_num
    _ ≤ (2 : ℝ≥0) * boundedSharpSurvivalTheta M d K := by
      exact mul_le_mul_of_nonneg_left
        (half_le_boundedSharpSurvivalTheta hM hhalf) zero_le

/-- A linearly decreasing nonnegative real envelope. -/
def affineSurvivalEnvelope (R0 slope : ℝ≥0) (i : ℕ) : ℝ≥0 :=
  R0 - (i : ℝ≥0) * slope

lemma affineSurvivalEnvelope_pos
    {R0 slope : ℝ≥0} {n i : ℕ}
    (hpos : (n : ℝ≥0) * slope < R0) (hi : i ≤ n) :
    0 < affineSurvivalEnvelope R0 slope i := by
  unfold affineSurvivalEnvelope
  rw [tsub_pos_iff_lt]
  have hmul : (i : ℝ≥0) * slope ≤ (n : ℝ≥0) * slope := by
    simpa only [mul_comm] using
      mul_le_mul_right (by exact_mod_cast hi : (i : ℝ≥0) ≤ n) slope
  exact hmul.trans_lt hpos

lemma affineSurvivalEnvelope_antitone
    (R0 slope : ℝ≥0) : Antitone (affineSurvivalEnvelope R0 slope) := by
  intro i j hij
  unfold affineSurvivalEnvelope
  apply tsub_le_tsub_left
  simpa only [mul_comm] using
    mul_le_mul_right (by exact_mod_cast hij : (i : ℝ≥0) ≤ j) slope

/-- Before the envelope reaches zero, its exact one-step decrement is the
chosen slope. -/
lemma affineSurvivalEnvelope_sub_succ
    {R0 slope : ℝ≥0} {n i : ℕ}
    (hpos : (n : ℝ≥0) * slope ≤ R0) (hi : i < n) :
    affineSurvivalEnvelope R0 slope i -
        affineSurvivalEnvelope R0 slope (i + 1) = slope := by
  have hi1 : i + 1 ≤ n := by omega
  have hileMul : ((i + 1 : ℕ) : ℝ≥0) * slope ≤
      (n : ℝ≥0) * slope := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using mul_le_mul_right (by exact_mod_cast
      hi1 : ((i + 1 : ℕ) : ℝ≥0) ≤ n) slope
  have hile : ((i + 1 : ℕ) : ℝ≥0) * slope ≤ R0 := hileMul.trans hpos
  have hi0Mul : (i : ℝ≥0) * slope ≤ ((i + 1 : ℕ) : ℝ≥0) * slope := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using mul_le_mul_right (by exact_mod_cast
      (Nat.le_succ i) : (i : ℝ≥0) ≤ i + 1) slope
  have hi0 : (i : ℝ≥0) * slope ≤ R0 := hi0Mul.trans hile
  apply NNReal.eq
  rw [NNReal.coe_sub (affineSurvivalEnvelope_antitone R0 slope
    (Nat.le_succ i))]
  simp only [affineSurvivalEnvelope, NNReal.coe_sub hi0,
    NNReal.coe_sub hile, NNReal.coe_mul, NNReal.coe_natCast]
  push_cast
  ring

/-- The affine-envelope loss inequality follows from the exact
three-pairs-per-triangle availability bound and a lower/upper pair-star
ratio.  This is the form produced by `outerSharpUpperFormula`. -/
theorem affineEnvelope_loss_of_three_mul
    {P M d u K : ℕ} {R slope : ℝ≥0}
    (hPR : (P : ℝ≥0) ≤ R)
    (hM : 3 * M ≤ P * u)
    (hratio : slope * (u : ℕ) ≤ 3 * (d - K : ℕ)) :
    slope * (M : ℕ) ≤ R * (d - K : ℕ) := by
  have hM' : (3 : ℝ≥0) * M ≤ (P : ℝ≥0) * u := by exact_mod_cast hM
  have hratio' : slope * (u : ℕ) ≤
      (3 : ℝ≥0) * (d - K : ℕ) := hratio
  calc
    slope * (M : ℕ) =
        ((3 : ℝ≥0) * M) * slope / 3 := by norm_num; ring
    _ ≤ ((P : ℝ≥0) * u) * slope / 3 := by gcongr
    _ = (P : ℝ≥0) * (slope * u) / 3 := by ring
    _ ≤ (P : ℝ≥0) * (3 * (d - K : ℕ)) / 3 := by gcongr
    _ = (P : ℝ≥0) * (d - K : ℕ) := by norm_num; ring
    _ ≤ R * (d - K : ℕ) := by gcongr

/-- A convenient cross-multiplied criterion for one sharp survival factor
to be bounded by an envelope ratio.  It keeps all rounding in `ℕ`: the
amount by which the envelope is allowed to fall, times the upper
availability bound, is paid by the effective pair-star floor. -/
theorem boundedSharpSurvivalTheta_le_ratio
    (M d K R Rnext : ℕ)
    (hM : 0 < M) (hR : 0 < R) (hnext : Rnext ≤ R)
    (hloss : (R - Rnext) * M ≤ R * (d - K)) :
    boundedSharpSurvivalTheta M d K ≤
      (Rnext : ℝ≥0) / (R : ℝ≥0) := by
  have hM' : (0 : ℝ≥0) < M := by exact_mod_cast hM
  have hR' : (0 : ℝ≥0) < R := by exact_mod_cast hR
  rw [boundedSharpSurvivalTheta, ← div_eq_mul_inv]
  rw [div_le_div_iff₀ hM' hR']
  by_cases heff : d - K ≤ M
  · rw [← NNReal.coe_le_coe]
    simp only [NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_sub heff]
    have hloss' : (((R - Rnext) * M : ℕ) : ℝ) ≤
        ((R * (d - K) : ℕ) : ℝ) := by exact_mod_cast hloss
    push_cast [Nat.cast_sub hnext] at hloss'
    have hnext' : (Rnext : ℝ) ≤ R := by exact_mod_cast hnext
    have heff' : ((d - K : ℕ) : ℝ) ≤ M := by exact_mod_cast heff
    nlinarith
  · have hz : M - (d - K) = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge heff)
    simp only [hz, Nat.cast_zero, zero_mul]
    exact zero_le

/-- `NNReal` envelope version, allowing the per-step envelope decrement to
be fractional.  This is essential when a power-vortex step loses only a
small relative amount in its lower/upper pair-star comparison. -/
theorem boundedSharpSurvivalTheta_le_nnreal_ratio
    (M d K : ℕ) (R Rnext : ℝ≥0)
    (hM : 0 < M) (hR : 0 < R) (hnext : Rnext ≤ R)
    (hloss : (R - Rnext) * (M : ℕ) ≤ R * (d - K : ℕ)) :
    boundedSharpSurvivalTheta M d K ≤ Rnext / R := by
  have hM' : (0 : ℝ≥0) < M := by exact_mod_cast hM
  rw [boundedSharpSurvivalTheta, ← div_eq_mul_inv]
  rw [div_le_div_iff₀ hM' hR]
  by_cases heff : d - K ≤ M
  · rw [← NNReal.coe_le_coe]
    simp only [NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_sub heff]
    have hloss' : ((R - Rnext : ℝ≥0) : ℝ) * (M : ℝ) ≤
        (R : ℝ) * ((d - K : ℕ) : ℝ) := by exact_mod_cast hloss
    rw [NNReal.coe_sub hnext] at hloss'
    have hnext' : (Rnext : ℝ) ≤ R := by exact_mod_cast hnext
    have heff' : ((d - K : ℕ) : ℝ) ≤ M := by exact_mod_cast heff
    nlinarith
  · have hz : M - (d - K) = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge heff)
    simp only [hz, Nat.cast_zero, zero_mul]
    exact zero_le

/-- Scheduled form of the fractional-envelope criterion. -/
theorem boundedSharpSurvivalSchedule_le_nnreal_envelope_ratio
    {n : ℕ} (M d : ℕ → ℕ) (K : ℕ) (R : ℕ → ℝ≥0)
    (hM : ∀ i, i < n → 0 < M i)
    (hR : ∀ i, i ≤ n → 0 < R i)
    (hnext : ∀ i, i < n → R (i + 1) ≤ R i)
    (hloss : ∀ i, i < n →
      (R i - R (i + 1)) * (M i : ℕ) ≤ R i * (d i - K : ℕ)) :
    ∀ i, i < n →
      boundedSharpSurvivalSchedule n M d K i ≤ R (i + 1) / R i := by
  intro i hi
  simp only [boundedSharpSurvivalSchedule, if_pos hi]
  exact boundedSharpSurvivalTheta_le_nnreal_ratio (M i) (d i) K
    (R i) (R (i + 1)) (hM i hi) (hR i (Nat.le_of_lt hi))
      (hnext i hi) (hloss i hi)

/-- Time-indexed version of `boundedSharpSurvivalTheta_le_ratio`. -/
theorem boundedSharpSurvivalSchedule_le_envelope_ratio
    {n : ℕ} (M d : ℕ → ℕ) (K : ℕ) (R : ℕ → ℕ)
    (hM : ∀ i, i < n → 0 < M i)
    (hR : ∀ i, i ≤ n → 0 < R i)
    (hnext : ∀ i, i < n → R (i + 1) ≤ R i)
    (hloss : ∀ i, i < n →
      (R i - R (i + 1)) * M i ≤ R i * (d i - K)) :
    ∀ i, i < n →
      boundedSharpSurvivalSchedule n M d K i ≤
        (R (i + 1) : ℝ≥0) / (R i : ℝ≥0) := by
  intro i hi
  simp only [boundedSharpSurvivalSchedule, if_pos hi]
  exact boundedSharpSurvivalTheta_le_ratio (M i) (d i) K
    (R i) (R (i + 1)) (hM i hi) (hR i (Nat.le_of_lt hi))
      (hnext i hi) (hloss i hi)

/-- If every survival factor is at most the corresponding ratio of a
positive envelope, their cumulative product telescopes. -/
theorem cumulativeSurvival_le_envelope_ratio
    {n : ℕ} (theta R : ℕ → ℝ≥0)
    (hR : ∀ i, i ≤ n → 0 < R i)
    (htheta : ∀ i, i < n → theta i ≤ R (i + 1) / R i) :
    ∀ i, i ≤ n → cumulativeSurvival theta i ≤ R i / R 0 := by
  intro i hi
  induction i with
  | zero =>
      rw [cumulativeSurvival]
      simp only [range_zero, prod_empty]
      rw [div_self (hR 0 (Nat.zero_le n)).ne']
  | succ i ih =>
      have hi' : i < n := Nat.lt_of_succ_le hi
      have hRi : R i ≠ 0 := (hR i (Nat.le_of_lt hi')).ne'
      have hR0 : R 0 ≠ 0 := (hR 0 (Nat.zero_le n)).ne'
      rw [cumulativeSurvival, prod_range_succ]
      calc
        (∏ j ∈ range i, theta j) * theta i ≤
            (R i / R 0) * (R (i + 1) / R i) :=
          mul_le_mul (ih (Nat.le_of_lt hi')) (htheta i hi') zero_le zero_le
        _ = R (i + 1) / R 0 := by
          field_simp

/-- Abstract form of the cubic cancellation.  `R 0` is the initial eligible
pair count (quadratic in `N`), while `D i` is the available-triangle floor.
The hypothesis `D⁻¹ R³ ≤ B N³` is the local schedule estimate; after
normalization by `R 0`, its contribution is only `O(N⁻³)`. -/
theorem inv_mul_envelopeRatio_cubed_le
    {N A B D R0 Ri : ℝ≥0}
    (hN : 0 < N) (hR0 : 0 < R0)
    (hquadratic : N ^ 2 ≤ A * R0)
    (hlocal : D⁻¹ * Ri ^ 3 ≤ B * N ^ 3) :
    D⁻¹ * (Ri / R0) ^ 3 ≤ A ^ 3 * B * N⁻¹ ^ 3 := by
  have hN2 : 0 < N ^ 2 := pow_pos hN 2
  have hR0inv : R0⁻¹ ≤ A * (N ^ 2)⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hR0]
    calc
      1 = N ^ 2 * (N ^ 2)⁻¹ := by
        exact (mul_inv_cancel₀ hN2.ne').symm
      _ ≤ (A * R0) * (N ^ 2)⁻¹ := by gcongr
      _ = (A * (N ^ 2)⁻¹) * R0 := by ring
  calc
    D⁻¹ * (Ri / R0) ^ 3 = (D⁻¹ * Ri ^ 3) * R0⁻¹ ^ 3 := by
      rw [div_pow, inv_pow]
      ring
    _ ≤ (B * N ^ 3) * (A * (N ^ 2)⁻¹) ^ 3 := by
      exact mul_le_mul hlocal (pow_le_pow_left' hR0inv 3) zero_le zero_le
    _ = A ^ 3 * B * N⁻¹ ^ 3 := by
      have hN0 : N ≠ 0 := hN.ne'
      field_simp

/-- The local cubic estimate follows from the two elementary scale facts
present in the vortex schedule: the available-family floor is at least a
constant fraction of `R*d`, and the eligible-pair envelope is at most a
constant times `N*d`. -/
theorem inv_mul_cube_le_of_pair_availability
    {N A C D R d : ℝ≥0}
    (hd : 0 < d) (hD : 0 < D)
    (havailability : R * d ≤ C * D)
    (hpairScale : R ≤ A * N * d)
    (hdN : d ≤ N) :
    D⁻¹ * R ^ 3 ≤ C * A ^ 2 * N ^ 3 := by
  have hratio : R / D ≤ C / d := by
    rw [div_le_div_iff₀ hD hd]
    simpa only [mul_comm] using havailability
  calc
    D⁻¹ * R ^ 3 = (R / D) * R ^ 2 := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ (C / d) * (A * N * d) ^ 2 := by
      exact mul_le_mul hratio (pow_le_pow_left' hpairScale 2) zero_le zero_le
    _ = C * A ^ 2 * N ^ 2 * d := by
      have hd0 : d ≠ 0 := hd.ne'
      field_simp
    _ ≤ C * A ^ 2 * N ^ 2 * N := by gcongr
    _ = C * A ^ 2 * N ^ 3 := by ring

/-- A version adapted to the triangle-removal scaling
`P² ≲ N³ d`: `P` is the remaining eligible-pair count, `d` the pair-star
floor, and the fractional survival envelope is within a constant of `P`. -/
theorem inv_mul_cube_le_of_quadratic_pairScale
    {N A B C D R P d : ℝ≥0}
    (hd : 0 < d) (hD : 0 < D)
    (havailability : P * d ≤ C * D)
    (henvelope : R ≤ A * P)
    (hpairScale : P ^ 2 ≤ B * N ^ 3 * d) :
    D⁻¹ * R ^ 3 ≤ C * A ^ 3 * B * N ^ 3 := by
  have hratio : P / D ≤ C / d := by
    rw [div_le_div_iff₀ hD hd]
    simpa only [mul_comm] using havailability
  calc
    D⁻¹ * R ^ 3 ≤ D⁻¹ * (A * P) ^ 3 := by gcongr
    _ = A ^ 3 * (P / D) * P ^ 2 := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ A ^ 3 * (C / d) * (B * N ^ 3 * d) := by gcongr
    _ = C * A ^ 3 * B * N ^ 3 := by
      have hd0 : d ≠ 0 := hd.ne'
      field_simp

/-- The telescoping estimate and the local cubic estimate combine directly
into the normalized hypothesis of
`transferPointWeight_boundedSharp_le_of_cubic_normalized`. -/
theorem inv_mul_cumulativeSurvival_cubed_le
    {n i : ℕ} {N A B : ℝ≥0}
    (theta R D : ℕ → ℝ≥0)
    (hi : i ≤ n)
    (hN : 0 < N)
    (hR : ∀ j, j ≤ n → 0 < R j)
    (htheta : ∀ j, j < n → theta j ≤ R (j + 1) / R j)
    (hquadratic : N ^ 2 ≤ A * R 0)
    (hlocal : (D i)⁻¹ * (R i) ^ 3 ≤ B * N ^ 3) :
    (D i)⁻¹ * cumulativeSurvival theta i ^ 3 ≤
      A ^ 3 * B * N⁻¹ ^ 3 := by
  have htel := cumulativeSurvival_le_envelope_ratio theta R hR htheta i hi
  calc
    (D i)⁻¹ * cumulativeSurvival theta i ^ 3 ≤
        (D i)⁻¹ * (R i / R 0) ^ 3 := by
      gcongr
    _ ≤ A ^ 3 * B * N⁻¹ ^ 3 :=
      inv_mul_envelopeRatio_cubed_le hN (hR 0 (Nat.zero_le n))
        hquadratic hlocal

/-- Ready-to-use form for the sharp initial product theorem.  All analytic
content of the retrospective cancellation is reduced to natural envelope
inequalities and the local cubic bound. -/
theorem transferPointWeight_boundedSharp_le_of_envelope
    {n N K : ℕ} {D M d : ℕ → ℕ} {R : ℕ → ℝ≥0}
    {Cfactor Q L : ℝ≥0}
    (hN : 0 < N) (hn : n ≤ N ^ 2)
    (hfactor : ∀ i, i < n →
      (boundedSharpSurvivalTheta (M i) (d i) K ^ K)⁻¹ ≤ Cfactor)
    (hM : ∀ i, i < n → 0 < M i)
    (hR : ∀ i, i ≤ n → 0 < R i)
    (hnext : ∀ i, i < n → R (i + 1) ≤ R i)
    (hloss : ∀ i, i < n →
      (R i - R (i + 1)) * (M i : ℕ) ≤ R i * (d i - K : ℕ))
    (hquadratic : (N : ℝ≥0) ^ 2 ≤ Q * R 0)
    (hlocal : ∀ i, i < n →
      (D i : ℝ≥0)⁻¹ * (R i) ^ 3 ≤ L * (N : ℝ≥0) ^ 3) :
    transferPointWeight
        (boundedSharpSurvivalSchedule n M d K)
        (boundedSharpTransferSchedule n D M d K) n ≤
      (Cfactor * (Q ^ 3 * L)) * (N : ℝ≥0)⁻¹ := by
  have htheta : ∀ i, i < n →
      boundedSharpSurvivalSchedule n M d K i ≤
        R (i + 1) / R i :=
    boundedSharpSurvivalSchedule_le_nnreal_envelope_ratio M d K R
      hM hR hnext hloss
  apply transferPointWeight_boundedSharp_le_of_cubic_normalized hN hn
    hfactor
  intro i hi
  simpa only [mul_assoc] using
    inv_mul_cumulativeSurvival_cubed_le
      (boundedSharpSurvivalSchedule n M d K)
      R (fun j ↦ (D j : ℝ≥0))
      (Nat.le_of_lt hi) (by exact_mod_cast hN) hR htheta hquadratic
        (hlocal i hi)

/-- Affine-envelope specialization used by each power-vortex phase. -/
theorem transferPointWeight_boundedSharp_le_of_affineEnvelope
    {n N K : ℕ} {D M d : ℕ → ℕ}
    {R0 slope Cfactor Q L : ℝ≥0}
    (hN : 0 < N) (hn : n ≤ N ^ 2)
    (hfactor : ∀ i, i < n →
      (boundedSharpSurvivalTheta (M i) (d i) K ^ K)⁻¹ ≤ Cfactor)
    (hM : ∀ i, i < n → 0 < M i)
    (henvelopePos : (n : ℝ≥0) * slope < R0)
    (hloss : ∀ i, i < n →
      slope * (M i : ℕ) ≤
        affineSurvivalEnvelope R0 slope i * (d i - K : ℕ))
    (hquadratic : (N : ℝ≥0) ^ 2 ≤ Q * R0)
    (hlocal : ∀ i, i < n →
      (D i : ℝ≥0)⁻¹ * (affineSurvivalEnvelope R0 slope i) ^ 3 ≤
        L * (N : ℝ≥0) ^ 3) :
    transferPointWeight
        (boundedSharpSurvivalSchedule n M d K)
        (boundedSharpTransferSchedule n D M d K) n ≤
      (Cfactor * (Q ^ 3 * L)) * (N : ℝ≥0)⁻¹ := by
  apply transferPointWeight_boundedSharp_le_of_envelope hN hn hfactor hM
  · intro i hi
    exact affineSurvivalEnvelope_pos henvelopePos hi
  · intro i hi
    exact affineSurvivalEnvelope_antitone R0 slope (Nat.le_succ i)
  · intro i hi
    rw [affineSurvivalEnvelope_sub_succ (le_of_lt henvelopePos) hi]
    exact hloss i hi
  · simpa only [affineSurvivalEnvelope, Nat.cast_zero, zero_mul,
      tsub_zero] using hquadratic
  · exact hlocal

end

end Erdos207
