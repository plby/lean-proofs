/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpScheduledPairTrajectories

/-!
# Algebra for coupled outer pair trajectories

Independent fixed-width upper and lower quadratic barriers cannot control the
long outer phase: the conservative upper drift uses the lower trajectory and
the conservative lower drift uses the upper trajectory.  The error window
must therefore widen as the eligible-pair clock decreases.  This file
isolates the two elementary polynomial estimates used in that coupled
comparison.
-/

namespace Erdos207

noncomputable section

/-- The lower estimate for the upper-trajectory drift.  The deliberately
generous constant `100` absorbs both endpoint errors and the two-unit loss in
`3d - 2 - u`. -/
lemma coupledOuter_upper_polynomial_margin
    {z : ℝ} (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 100) :
    (6 - 100 * z) * (1 + 2 * z) ≤
      3 * (1 - 2 * z) * (2 - 9 * z) := by
  nlinarith [sq_nonneg z]

/-- The upper estimate for the lower-trajectory drift.  Besides the endpoint
errors, the extra `z` in the left side is the normalized aggregate
two-away-incidence term. -/
lemma coupledOuter_lower_polynomial_margin
    {z : ℝ} (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 100) :
    3 * (2 * (1 + 2 * z) ^ 2 + z) ≤
      (6 + 100 * z) * (1 - z) * (1 - 2 * z) := by
  nlinarith [sq_nonneg z, sq_nonneg (1 - 2 * z)]

/-- A real cross-multiplied form of the upper scheduled-rate estimate.

`M` is an upper availability denominator, `d` and `u` are the current lower
and upper pair-degree schedules, `y` is the central quadratic trajectory,
and `z` is its relative error.  The assumptions are exactly the estimates
that survive integer floor/ceiling conversion. -/
lemma coupledOuter_upper_rate_crossmul
    {E M d u y z : ℝ}
    (hE : 0 < E) (hM : 0 < M) (hy : 0 ≤ y)
    (hdnonneg : 0 ≤ d) (hunonneg : 0 ≤ u)
    (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 100)
    (hMupper : 3 * M ≤ E * u)
    (hd : y * (1 - 2 * z) ≤ d)
    (hu : u ≤ y * (1 + 2 * z))
    (hround : 2 ≤ z * y) :
    (6 - 100 * z) * y / E ≤ d * (3 * d - 2 - u) / M := by
  have hzcoef : 0 ≤ 6 - 100 * z := by nlinarith
  have hone : 0 ≤ 1 - 2 * z := by nlinarith
  have htwopos : 0 ≤ 2 - 9 * z := by nlinarith
  have htwo : y * (2 - 9 * z) ≤ 3 * d - 2 - u := by
    calc
      y * (2 - 9 * z) =
          3 * (y * (1 - 2 * z)) - z * y - y * (1 + 2 * z) := by ring
      _ ≤ 3 * d - 2 - u := by nlinarith
  have hmargin := coupledOuter_upper_polynomial_margin hz hzsmall
  have htarget :
      (6 - 100 * z) * y * u ≤ 3 * d * (3 * d - 2 - u) := by
    calc
      (6 - 100 * z) * y * u ≤
          (6 - 100 * z) * y * (y * (1 + 2 * z)) := by
        gcongr
      _ ≤ 3 * (y * (1 - 2 * z)) * (y * (2 - 9 * z)) := by
        have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
        nlinarith
      _ ≤ 3 * d * (3 * d - 2 - u) := by
        gcongr
  rw [div_le_div_iff₀ hE hM]
  have hMdiv : M ≤ E * u / 3 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    simpa only [mul_comm] using hMupper
  calc
    (6 - 100 * z) * y * M ≤
        ((6 - 100 * z) * y * (E * u)) / 3 := by
      calc
        (6 - 100 * z) * y * M ≤
            (6 - 100 * z) * y * (E * u / 3) := by gcongr
        _ = ((6 - 100 * z) * y * (E * u)) / 3 := by ring
    _ ≤ E * (d * (3 * d - 2 - u)) := by
      nlinarith
    _ = d * (3 * d - 2 - u) * E := by ring

/-- A real cross-multiplied form of the lower scheduled-rate estimate.

The denominator lower bound includes the loss from subtracting the current
upper pair degree.  `K ≤ z y²` is the normalized aggregate-incidence input.
-/
lemma coupledOuter_lower_rate_crossmul
    {E R d u K y z : ℝ}
    (hE : 0 < E) (hR : 0 < R) (hy : 0 < y)
    (hdnonneg : 0 ≤ d) (hunonneg : 0 ≤ u)
    (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 100)
    (hRlower : (1 - z) * E * d ≤ 3 * R)
    (hd : y * (1 - 2 * z) ≤ d)
    (hu : u ≤ y * (1 + 2 * z))
    (hK : K ≤ z * y ^ 2)
    (hKnonneg : 0 ≤ K) :
    (2 * u ^ 2 + K) / R ≤ (6 + 100 * z) * y / E := by
  have hone : 0 ≤ 1 - z := by nlinarith
  have htwo : 0 ≤ 1 - 2 * z := by nlinarith
  have hmargin := coupledOuter_lower_polynomial_margin hz hzsmall
  have hnum : 3 * (2 * u ^ 2 + K) ≤
      (6 + 100 * z) * y * ((1 - z) * d) := by
    calc
      3 * (2 * u ^ 2 + K) ≤
          3 * (2 * (y * (1 + 2 * z)) ^ 2 + z * y ^ 2) := by
        have huupper : 0 ≤ y * (1 + 2 * z) := by positivity
        have husq : u ^ 2 ≤ (y * (1 + 2 * z)) ^ 2 :=
          pow_le_pow_left₀ hunonneg hu 2
        nlinarith
      _ ≤ (6 + 100 * z) * y *
          ((1 - z) * (y * (1 - 2 * z))) := by
        nlinarith [sq_nonneg y]
      _ ≤ (6 + 100 * z) * y * ((1 - z) * d) := by
        gcongr
  rw [div_le_div_iff₀ hR hE]
  calc
    (2 * u ^ 2 + K) * E ≤
        ((6 + 100 * z) * y * ((1 - z) * d)) * E / 3 := by
      nlinarith
    _ ≤ (6 + 100 * z) * y * R := by
      have hcoeff : 0 ≤ (6 + 100 * z) * y := by positivity
      nlinarith

end

/-- Natural-number specialization of
`coupledOuter_upper_rate_crossmul`.  The subtraction hypothesis records that
the `Nat` expression `3*d - 2 - u` is not truncated. -/
lemma sharpScheduledPairUpperRate_ge_coupled
    {E d u : ℕ} {y z : ℝ}
    (hE : 0 < E) (hM : 0 < E * u / 3)
    (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 100)
    (hd : y * (1 - 2 * z) ≤ d)
    (hu : (u : ℝ) ≤ y * (1 + 2 * z))
    (hround : 2 ≤ z * y) (hsub : u + 2 ≤ 3 * d) :
    (6 - 100 * z) * y / E ≤
      sharpScheduledPairUpperRate (E * u / 3) d u := by
  have hMupper : 3 * (E * u / 3) ≤ E * u := Nat.mul_div_le _ _
  have hsubTwo : 2 ≤ 3 * d := by omega
  have hsubU : u ≤ 3 * d - 2 := by omega
  unfold sharpScheduledPairUpperRate
  rw [Nat.cast_sub hsubU, Nat.cast_sub hsubTwo]
  have hrate := coupledOuter_upper_rate_crossmul
      (E := (E : ℝ)) (M := (E * u / 3 : ℕ))
      (d := (d : ℝ)) (u := (u : ℝ)) (by exact_mod_cast hE)
      (by exact_mod_cast hM) hy (by positivity) (by positivity) hz hzsmall
      (by exact_mod_cast hMupper) hd hu hround
  convert hrate using 1 <;> push_cast <;> ring

/-- Natural-number specialization of
`coupledOuter_lower_rate_crossmul`.  The denominator inequality is kept
explicit because it is where division rounding and the subtraction of the
current upper degree are charged in the coupled induction. -/
lemma sharpScheduledPairLowerRate_le_coupled
    {E D d u K : ℕ} {y z : ℝ}
    (hE : 0 < E) (hgap : u < D)
    (hy : 0 < y)
    (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 100)
    (hdenom : (1 - z) * E * d ≤ 3 * (D - u : ℕ))
    (hd : y * (1 - 2 * z) ≤ d)
    (hu : (u : ℝ) ≤ y * (1 + 2 * z))
    (hK : (K : ℝ) ≤ z * y ^ 2) :
    sharpScheduledPairLowerRate D u K ≤ (6 + 100 * z) * y / E := by
  unfold sharpScheduledPairLowerRate
  rw [Nat.cast_sub hgap.le]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  have hrate := coupledOuter_lower_rate_crossmul
      (E := (E : ℝ)) (R := ((D - u : ℕ) : ℝ))
      (d := (d : ℝ)) (u := (u : ℝ)) (K := (K : ℝ))
      (by exact_mod_cast hE) (by exact_mod_cast Nat.sub_pos_of_lt hgap)
      hy
      (by positivity) (by positivity) hz hzsmall hdenom hd hu hK (by positivity)
  simp only [Nat.cast_sub hgap.le, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat, div_eq_mul_inv] at hrate
  convert hrate using 1 <;> ring_nf

end Erdos207
