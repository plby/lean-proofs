/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.Numerics

/-!
# Numerical closure of the two branches in PZ Lemma 1

This file contains no geometry.  It records the exact algebra needed after
the geometric argument has produced a cell occupancy `K`, a real grid scale
`m`, a graph-window width `u`, and the logarithmic loss `L`.

The low-occupancy branch uses
`etaLow = C * K * L * u^(d-1) / m^(d+1)`, while the high-occupancy branch uses
`etaHigh = C * u^(d-1) / m^d`.

The last section computes the six positive powers of `delta` which absorb the
fixed constants and powers of `log (1 / delta)` when
`m = delta ^ (-3 / (10 * (d+1)))` and
`u = c0 * delta ^ (epsilon/10)`.
-/

open Filter Set
open scoped Topology

namespace Erdos186.PZ.ConvexDensity

noncomputable section

/-! ## Branch quantities -/

/-- The real exponent `d - 1`. -/
def boundaryDimension (d : ℕ) : ℝ :=
  (d : ℝ) - 1

/-- The lower bound for the proportion of points captured by either branch. -/
def capturedFraction (d : ℕ) (c u K m L : ℝ) : ℝ :=
  c * u ^ boundaryDimension d * K / (m ^ boundaryDimension d * L)

/-- The volume parameter in the low-occupancy branch. -/
def etaLow (d : ℕ) (C u K m L : ℝ) : ℝ :=
  C * K * L * u ^ boundaryDimension d / m ^ ((d : ℝ) + 1)

/-- The volume parameter in the high-occupancy branch. -/
def etaHigh (d : ℕ) (C u m : ℝ) : ℝ :=
  C * u ^ boundaryDimension d / m ^ (d : ℝ)

/-- The lower comparison quantity for `etaLow`, obtained from `cK ≤ K*L`. -/
def etaLowBaseline (d : ℕ) (C cK u m : ℝ) : ℝ :=
  C * cK * u ^ boundaryDimension d / m ^ ((d : ℝ) + 1)

/-- The upper comparison quantity for `etaLow`, obtained from `K ≤ m^alpha`. -/
def etaLowEnvelope (d : ℕ) (C u m L : ℝ) : ℝ :=
  C * m ^ alpha d * L * u ^ boundaryDimension d / m ^ ((d : ℝ) + 1)

theorem boundaryDimension_add_two (d : ℕ) :
    boundaryDimension d + 2 = (d : ℝ) + 1 := by
  simp [boundaryDimension]
  ring

theorem boundaryDimension_add_one (d : ℕ) :
    boundaryDimension d + 1 = (d : ℝ) := by
  simp [boundaryDimension]

theorem boundaryDimension_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < boundaryDimension d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  simp only [boundaryDimension]
  linarith

/-! ## Abstract low- and high-occupancy closure -/

/-- The baseline produced by `cK ≤ K*L` is at most `etaLow`. -/
theorem etaLowBaseline_le_etaLow {d : ℕ} {C cK u K m L : ℝ}
    (hC : 0 ≤ C) (hu : 0 ≤ u) (hm : 0 < m)
    (hcK : cK ≤ K * L) :
    etaLowBaseline d C cK u m ≤ etaLow d C u K m L := by
  have huD : 0 ≤ u ^ boundaryDimension d := Real.rpow_nonneg hu _
  have hmD : 0 < m ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hm _
  rw [etaLowBaseline, etaLow]
  apply (div_le_div_iff_of_pos_right hmD).2
  nlinarith [mul_nonneg hC huD]

/-- The upper occupancy range gives the advertised envelope for `etaLow`. -/
theorem etaLow_le_envelope {d : ℕ} {C u K m L : ℝ}
    (hC : 0 ≤ C) (hu : 0 ≤ u) (hL : 0 ≤ L) (hm : 0 < m)
    (hK : K ≤ m ^ alpha d) :
    etaLow d C u K m L ≤ etaLowEnvelope d C u m L := by
  have huD : 0 ≤ u ^ boundaryDimension d := Real.rpow_nonneg hu _
  have hmD : 0 < m ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hm _
  rw [etaLow, etaLowEnvelope]
  apply (div_le_div_iff_of_pos_right hmD).2
  have h₁ : C * K ≤ C * m ^ alpha d :=
    mul_le_mul_of_nonneg_left hK hC
  have h₂ : C * K * L ≤ C * m ^ alpha d * L :=
    mul_le_mul_of_nonneg_right h₁ hL
  exact mul_le_mul_of_nonneg_right h₂ huD

/-- Algebraic density conclusion in the low-occupancy branch.

The displayed logarithmic hypothesis is exactly what remains after cancelling
the common factors in `etaLow ^ q ≤ capturedFraction`. -/
theorem low_branch_density {d : ℕ} {q c C cK u K m L : ℝ}
    (_hq0 : 0 < q) (hq1 : q ≤ 1)
    (hc : 0 < c) (hC : 0 < C) (hcK0 : 0 < cK)
    (hu : 0 < u) (hK : 0 < K) (hm : 0 < m) (hL : 0 < L)
    (hcK : cK ≤ K * L)
    (hlog :
      C * L ^ (2 : ℕ) *
          (etaLowBaseline d C cK u m) ^ (q - 1) ≤ c * m ^ (2 : ℕ)) :
    (etaLow d C u K m L) ^ q ≤ capturedFraction d c u K m L := by
  have hbasePos : 0 < etaLowBaseline d C cK u m := by
    simp only [etaLowBaseline]
    positivity
  have hetaPos : 0 < etaLow d C u K m L := by
    simp only [etaLow]
    positivity
  have hbase : etaLowBaseline d C cK u m ≤ etaLow d C u K m L :=
    etaLowBaseline_le_etaLow hC.le hu.le hm hcK
  have hneg :
      (etaLow d C u K m L) ^ (q - 1) ≤
        (etaLowBaseline d C cK u m) ^ (q - 1) := by
    exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith))
      hbasePos hetaPos hbase
  have hratio :
      C * L ^ (2 : ℕ) *
          (etaLowBaseline d C cK u m) ^ (q - 1) /
            (c * m ^ (2 : ℕ)) ≤ 1 := by
    rw [div_le_one (mul_pos hc (by positivity))]
    exact hlog
  have heq :
      etaLow d C u K m L *
          (etaLowBaseline d C cK u m) ^ (q - 1) =
        (C * L ^ (2 : ℕ) *
            (etaLowBaseline d C cK u m) ^ (q - 1) /
              (c * m ^ (2 : ℕ))) * capturedFraction d c u K m L := by
    rw [etaLow, capturedFraction]
    rw [← boundaryDimension_add_two d, Real.rpow_add hm]
    rw [Real.rpow_two]
    field_simp
  calc
    (etaLow d C u K m L) ^ q =
        etaLow d C u K m L * (etaLow d C u K m L) ^ (q - 1) := by
      calc
        (etaLow d C u K m L) ^ q =
            (etaLow d C u K m L) ^ (1 + (q - 1)) := by ring_nf
        _ = etaLow d C u K m L *
            (etaLow d C u K m L) ^ (q - 1) := by
          rw [Real.rpow_add hetaPos, Real.rpow_one]
    _ ≤ etaLow d C u K m L *
        (etaLowBaseline d C cK u m) ^ (q - 1) :=
      mul_le_mul_of_nonneg_left hneg hetaPos.le
    _ = (C * L ^ (2 : ℕ) *
            (etaLowBaseline d C cK u m) ^ (q - 1) /
              (c * m ^ (2 : ℕ))) * capturedFraction d c u K m L := heq
    _ ≤ capturedFraction d c u K m L := by
      have hcaptured : 0 ≤ capturedFraction d c u K m L := by
        simp only [capturedFraction]
        positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio hcaptured

/-- Algebraic density conclusion in the high-occupancy branch. -/
theorem high_branch_density {d : ℕ} {q c C u K m L : ℝ}
    (_hq0 : 0 < q) (_hq1 : q ≤ 1)
    (hc : 0 < c) (hC : 0 < C) (hu : 0 < u)
    (hK : 0 < K) (hm : 0 < m) (hL : 0 < L)
    (hKlarge : m ^ alpha d ≤ K)
    (hlog :
      C * L * (etaHigh d C u m) ^ (q - 1) ≤
        c * m ^ (alpha d + 1)) :
    (etaHigh d C u m) ^ q ≤ capturedFraction d c u K m L := by
  have hetaPos : 0 < etaHigh d C u m := by
    simp only [etaHigh]
    positivity
  have hscale : c * m ^ (alpha d + 1) ≤ c * K * m := by
    rw [Real.rpow_add hm (alpha d) 1, Real.rpow_one]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hKlarge hc.le) hm.le
  have hratio :
      C * L * (etaHigh d C u m) ^ (q - 1) / (c * K * m) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hlog.trans hscale
  have heq :
      etaHigh d C u m * (etaHigh d C u m) ^ (q - 1) =
        (C * L * (etaHigh d C u m) ^ (q - 1) / (c * K * m)) *
          capturedFraction d c u K m L := by
    rw [etaHigh, capturedFraction]
    rw [← boundaryDimension_add_one d, Real.rpow_add hm]
    rw [Real.rpow_one]
    field_simp
  calc
    (etaHigh d C u m) ^ q =
        etaHigh d C u m * (etaHigh d C u m) ^ (q - 1) := by
      calc
        (etaHigh d C u m) ^ q =
            (etaHigh d C u m) ^ (1 + (q - 1)) := by ring_nf
        _ = etaHigh d C u m * (etaHigh d C u m) ^ (q - 1) := by
          rw [Real.rpow_add hetaPos, Real.rpow_one]
    _ = (C * L * (etaHigh d C u m) ^ (q - 1) / (c * K * m)) *
          capturedFraction d c u K m L := heq
    _ ≤ capturedFraction d c u K m L := by
      have hcaptured : 0 ≤ capturedFraction d c u K m L := by
        simp only [capturedFraction]
        positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio hcaptured

/-- Complete abstract closure of the low-occupancy branch. -/
theorem low_branch_closure {d : ℕ} {epsilon delta c C cK u K m L : ℝ}
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / ((d : ℝ) + 1))
    (_hdelta : 0 < delta) (_hdelta_one : delta ≤ 1)
    (hc : 0 < c) (hC : 0 < C) (hcK0 : 0 < cK)
    (hu : 0 < u) (hK : 0 < K) (hm : 0 < m) (hL : 0 < L)
    (hcK : cK ≤ K * L) (hKsmall : K ≤ m ^ alpha d)
    (hlower : delta ≤ etaLowBaseline d C cK u m)
    (hupper : etaLowEnvelope d C u m L ≤ delta ^ tau epsilon)
    (hlog :
      C * L ^ (2 : ℕ) *
          (etaLowBaseline d C cK u m) ^ (alpha d + epsilon - 1) ≤
        c * m ^ (2 : ℕ)) :
    etaLow d C u K m L ∈ Icc delta (delta ^ tau epsilon) ∧
      (etaLow d C u K m L) ^ (alpha d + epsilon) ≤
        capturedFraction d c u K m L := by
  have hq1 : alpha d + epsilon ≤ 1 :=
    (alpha_add_epsilon_lt_one (by omega : 1 ≤ d) hepsilon_le).le
  refine ⟨⟨hlower.trans (etaLowBaseline_le_etaLow hC.le hu.le hm hcK),
    (etaLow_le_envelope hC.le hu.le hL.le hm hKsmall).trans hupper⟩, ?_⟩
  exact low_branch_density (by
    have := alpha_nonneg (by omega : 1 ≤ d)
    linarith) hq1 hc hC hcK0 hu hK hm hL hcK hlog

/-- Complete abstract closure of the high-occupancy branch. -/
theorem high_branch_closure {d : ℕ} {epsilon delta c C u K m L : ℝ}
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / ((d : ℝ) + 1))
    (hc : 0 < c) (hC : 0 < C) (hu : 0 < u)
    (hK : 0 < K) (hm : 0 < m) (hL : 0 < L)
    (hKlarge : m ^ alpha d ≤ K)
    (hlower : delta ≤ etaHigh d C u m)
    (hupper : etaHigh d C u m ≤ delta ^ tau epsilon)
    (hlog :
      C * L * (etaHigh d C u m) ^ (alpha d + epsilon - 1) ≤
        c * m ^ (alpha d + 1)) :
    etaHigh d C u m ∈ Icc delta (delta ^ tau epsilon) ∧
      (etaHigh d C u m) ^ (alpha d + epsilon) ≤
        capturedFraction d c u K m L := by
  have hq1 : alpha d + epsilon ≤ 1 :=
    (alpha_add_epsilon_lt_one (by omega : 1 ≤ d) hepsilon_le).le
  refine ⟨⟨hlower, hupper⟩, ?_⟩
  exact high_branch_density (by
    have := alpha_nonneg (by omega : 1 ≤ d)
    linarith) hq1 hc hC hu hK hm hL hKlarge hlog

/-! ## Exact real scales and their saving exponents -/

/-- The exponent `3 / (10(d+1))` in the real grid scale. -/
def gridRate (d : ℕ) : ℝ :=
  3 / (10 * ((d : ℝ) + 1))

/-- The real-valued version of the paper's grid parameter. -/
def realGridScale (d : ℕ) (delta : ℝ) : ℝ :=
  delta ^ (-gridRate d)

/-- The graph-window width, including its fixed multiplicative constant. -/
def graphWidth (epsilon c0 delta : ℝ) : ℝ :=
  c0 * delta ^ tau epsilon

theorem realGridScale_pos (d : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    0 < realGridScale d delta := by
  exact Real.rpow_pos_of_pos hdelta _

theorem one_le_realGridScale (d : ℕ) {delta : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    1 ≤ realGridScale d delta := by
  rw [realGridScale]
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta_one
    (neg_nonpos.mpr (by simp only [gridRate]; positivity))

theorem graphWidth_pos {epsilon c0 delta : ℝ}
    (hc0 : 0 < c0) (hdelta : 0 < delta) :
    0 < graphWidth epsilon c0 delta := by
  simp only [graphWidth]
  positivity

/-- Power of `delta` in `etaLowBaseline`, before fixed constants. -/
def lowBaseRate (d : ℕ) (epsilon : ℝ) : ℝ :=
  tau epsilon * boundaryDimension d + gridRate d * ((d : ℝ) + 1)

/-- Power of `delta` in `etaHigh`, before fixed constants. -/
def highBaseRate (d : ℕ) (epsilon : ℝ) : ℝ :=
  tau epsilon * boundaryDimension d + gridRate d * (d : ℝ)

/-- Saving which absorbs the two logarithms in the low-occupancy density
comparison. -/
def lowDensitySaving (d : ℕ) (epsilon : ℝ) : ℝ :=
  2 * gridRate d +
    lowBaseRate d epsilon * (alpha d + epsilon - 1)

/-- Saving which absorbs the logarithm in the high-occupancy density
comparison. -/
def highDensitySaving (d : ℕ) (epsilon : ℝ) : ℝ :=
  gridRate d * (alpha d + 1) +
    highBaseRate d epsilon * (alpha d + epsilon - 1)

/-- Saving in the upper bound `etaLow ≤ delta^tau`. -/
def lowUpperSaving (d : ℕ) (epsilon : ℝ) : ℝ :=
  lowBaseRate d epsilon - gridRate d * alpha d - tau epsilon

/-- Saving in the upper bound `etaHigh ≤ delta^tau`. -/
def highUpperSaving (d : ℕ) (epsilon : ℝ) : ℝ :=
  highBaseRate d epsilon - tau epsilon

/-- Saving in the lower bound `delta ≤ etaLow`. -/
def lowLowerSaving (d : ℕ) (epsilon : ℝ) : ℝ :=
  1 - lowBaseRate d epsilon

/-- Saving in the lower bound `delta ≤ etaHigh`. -/
def highLowerSaving (d : ℕ) (epsilon : ℝ) : ℝ :=
  1 - highBaseRate d epsilon

theorem gridRate_pos (d : ℕ) : 0 < gridRate d := by
  simp only [gridRate]
  positivity

/-- All six powers which occur in the two branches are strictly positive. -/
theorem branchSavingExponents_pos {d : ℕ} {epsilon : ℝ}
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / ((d : ℝ) + 1)) :
    0 < lowDensitySaving d epsilon ∧
    0 < highDensitySaving d epsilon ∧
    0 < lowUpperSaving d epsilon ∧
    0 < highUpperSaving d epsilon ∧
    0 < lowLowerSaving d epsilon ∧
    0 < highLowerSaving d epsilon := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have heMul : epsilon * ((d : ℝ) + 1) ≤ 1 := by
    calc
      epsilon * ((d : ℝ) + 1)
          ≤ (1 / ((d : ℝ) + 1)) * ((d : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hepsilon_le hden.le
      _ = 1 := by field_simp
  simp only [lowDensitySaving, highDensitySaving, lowUpperSaving,
    highUpperSaving, lowLowerSaving, highLowerSaving, lowBaseRate,
    highBaseRate, gridRate, tau, alpha, boundaryDimension]
  constructor
  · field_simp
    nlinarith [mul_pos hepsilon (sub_pos.mpr (show (1 : ℝ) < d by linarith))]
  constructor
  · have hD : 0 < (d : ℝ) - 1 := by linarith
    have hfrac : 0 < ((d : ℝ) + 2) / ((d : ℝ) + 1) := by
      exact div_pos (by linarith) hden
    have hsimple :
        0 < epsilon / 10 *
          (((d : ℝ) + 2) / ((d : ℝ) + 1) + epsilon * ((d : ℝ) - 1)) := by
      exact mul_pos (by positivity) (add_pos hfrac (mul_pos hepsilon hD))
    convert hsimple using 1 <;> field_simp
    all_goals ring
  constructor
  · have hD0 : 0 ≤ (d : ℝ) - 2 := by linarith
    have hdiff :
        0 < ((d : ℝ) + 1) - ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
      rw [sub_pos, div_lt_iff₀ hden]
      nlinarith [sq_nonneg ((d : ℝ) + 1)]
    have hsimple :
        0 < epsilon / 10 * ((d : ℝ) - 2) +
          3 / (10 * ((d : ℝ) + 1)) *
            (((d : ℝ) + 1) - ((d : ℝ) - 1) / ((d : ℝ) + 1)) := by
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (by positivity) hD0)
        (mul_pos (by positivity) hdiff)
    convert hsimple using 1 <;> field_simp
    all_goals ring
  constructor
  · have hD0 : 0 ≤ (d : ℝ) - 2 := by linarith
    have hsimple :
        0 < epsilon / 10 * ((d : ℝ) - 2) +
          3 / (10 * ((d : ℝ) + 1)) * (d : ℝ) := by
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (by positivity) hD0)
        (mul_pos (by positivity) (by linarith))
    convert hsimple using 1 <;> field_simp
    all_goals ring
  constructor <;> field_simp <;> nlinarith

/-! ## A simultaneous sufficiently-small cutoff -/

/-- The six normalized costs left after substituting the exact real scales.
Each is a fixed constant times a power of `log (1/delta)` times a positive
power of `delta`. -/
def BranchPowerBounds (d : ℕ)
    (epsilon A₁ A₂ A₃ A₄ A₅ A₆ delta : ℝ) : Prop :=
  A₁ * (Real.log (1 / delta)) ^ (2 : ℕ) *
      delta ^ lowDensitySaving d epsilon ≤ 1 ∧
  A₂ * Real.log (1 / delta) * delta ^ highDensitySaving d epsilon ≤ 1 ∧
  A₃ * Real.log (1 / delta) * delta ^ lowUpperSaving d epsilon ≤ 1 ∧
  A₄ * delta ^ highUpperSaving d epsilon ≤ 1 ∧
  A₅ * delta ^ lowLowerSaving d epsilon ≤ 1 ∧
  A₆ * delta ^ highLowerSaving d epsilon ≤ 1

/-- One positive cutoff below one makes every normalized low- and high-branch
cost at most one. -/
theorem exists_deltaZero_branchPowerBounds {d : ℕ} {epsilon : ℝ}
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / ((d : ℝ) + 1))
    (A₁ A₂ A₃ A₄ A₅ A₆ : ℝ) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta < deltaZero →
        BranchPowerBounds d epsilon A₁ A₂ A₃ A₄ A₅ A₆ delta := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    branchSavingExponents_pos hd hepsilon hepsilon_le
  have H₁ := eventually_const_mul_log_one_div_pow_mul_rpow_le
    A₁ 2 h₁ zero_lt_one
  have H₂ := eventually_const_mul_log_one_div_pow_mul_rpow_le
    A₂ 1 h₂ zero_lt_one
  have H₃ := eventually_const_mul_log_one_div_pow_mul_rpow_le
    A₃ 1 h₃ zero_lt_one
  have H₄ := eventually_const_mul_log_one_div_pow_mul_rpow_le
    A₄ 0 h₄ zero_lt_one
  have H₅ := eventually_const_mul_log_one_div_pow_mul_rpow_le
    A₅ 0 h₅ zero_lt_one
  have H₆ := eventually_const_mul_log_one_div_pow_mul_rpow_le
    A₆ 0 h₆ zero_lt_one
  have H :
      ∀ᶠ delta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        BranchPowerBounds d epsilon A₁ A₂ A₃ A₄ A₅ A₆ delta := by
    filter_upwards [H₁, H₂, H₃, H₄, H₅, H₆]
      with delta hdelta₁ hdelta₂ hdelta₃ hdelta₄ hdelta₅ hdelta₆
    exact ⟨hdelta₁, by simpa using hdelta₂, by simpa using hdelta₃,
      by simpa using hdelta₄, by simpa using hdelta₅, by simpa using hdelta₆⟩
  obtain ⟨r, hr, hrH⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp H
  refine ⟨min r (1 / 2), by positivity, by
    calc
      min r (1 / 2) ≤ 1 / 2 := min_le_right _ _
      _ < 1 := by norm_num, ?_⟩
  intro delta hdelta hdeltaCutoff
  exact hrH ⟨hdelta, hdeltaCutoff.trans_le (min_le_left _ _)⟩

/-! The fixed coefficients obtained by substituting
`m = delta^(-gridRate d)` and `u = c0 * delta^tau` into the normalized branch
inequalities. -/

def lowDensityCoefficient (d : ℕ) (epsilon c C cK c0 : ℝ) : ℝ :=
  (C / c) *
    (C * cK * c0 ^ boundaryDimension d) ^ (alpha d + epsilon - 1)

def highDensityCoefficient (d : ℕ) (epsilon c C c0 : ℝ) : ℝ :=
  (C / c) *
    (C * c0 ^ boundaryDimension d) ^ (alpha d + epsilon - 1)

def etaUpperCoefficient (d : ℕ) (C c0 : ℝ) : ℝ :=
  C * c0 ^ boundaryDimension d

def lowEtaLowerCoefficient (d : ℕ) (C cK c0 : ℝ) : ℝ :=
  (C * cK * c0 ^ boundaryDimension d)⁻¹

def highEtaLowerCoefficient (d : ℕ) (C c0 : ℝ) : ℝ :=
  (C * c0 ^ boundaryDimension d)⁻¹

/-- Fully specialized simultaneous cutoff for the constants in the low- and
high-occupancy branches. -/
theorem exists_deltaZero_pzBranchPowerBounds {d : ℕ} {epsilon : ℝ}
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / ((d : ℝ) + 1))
    (c C cK c0 : ℝ) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta < deltaZero →
        BranchPowerBounds d epsilon
          (lowDensityCoefficient d epsilon c C cK c0)
          (highDensityCoefficient d epsilon c C c0)
          (etaUpperCoefficient d C c0)
          (etaUpperCoefficient d C c0)
          (lowEtaLowerCoefficient d C cK c0)
          (highEtaLowerCoefficient d C c0) delta := by
  exact exists_deltaZero_branchPowerBounds hd hepsilon hepsilon_le _ _ _ _ _ _

/-! ## Initial grid and cutoff arithmetic -/

/-- The initial mesh diameter in Section 2 of Pham--Zakharov. -/
def initialRadius (d : ℕ) (delta : ℝ) : ℝ :=
  16 * delta ^ (1 / (d : ℝ))

/-- Number of one-dimensional grid positions meeting the normalized box. -/
def initialAxisCount (d : ℕ) (delta : ℝ) : ℕ :=
  Nat.ceil (2 / initialRadius d delta) + 1

/-- The product bound for the number of candidate `d`-cells. -/
def initialCandidateCount (d : ℕ) (delta : ℝ) : ℕ :=
  (initialAxisCount d delta) ^ d

/-- Cells with fewer than this many points are discarded. -/
def initialOccupancyCutoff (delta : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (2 * delta * (n : ℝ))

/-- An explicit input-size threshold which absorbs the additive `+1` in the
occupancy ceiling. -/
def initialLargeEnough (delta : ℝ) : ℕ :=
  Nat.ceil (1 / (2 * delta))

/-- A convenient explicit smallness threshold which implies `r ≤ 1`. -/
def initialRadiusDeltaZero (d : ℕ) : ℝ :=
  (1 / 16 : ℝ) ^ (d : ℝ)

/-- One cutoff enforces both the radius bound and the logarithmic level
bound. -/
def initialGridDeltaZero (d : ℕ) : ℝ :=
  min (initialRadiusDeltaZero d) (1 / 4)

theorem initialRadiusDeltaZero_pos (d : ℕ) :
    0 < initialRadiusDeltaZero d := by
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem initialGridDeltaZero_pos (d : ℕ) :
    0 < initialGridDeltaZero d := by
  exact lt_min (initialRadiusDeltaZero_pos d) (by norm_num)

theorem initialRadius_le_one {d : ℕ} {delta : ℝ}
    (hd : 1 ≤ d) (hdelta : 0 < delta)
    (hdelta_small : delta ≤ initialRadiusDeltaZero d) :
    initialRadius d delta ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hexp : 0 ≤ 1 / (d : ℝ) := by positivity
  have hpow := Real.rpow_le_rpow hdelta.le hdelta_small hexp
  have hmul : (d : ℝ) * (1 / (d : ℝ)) = 1 := by field_simp
  rw [initialRadiusDeltaZero, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 16),
    hmul, Real.rpow_one] at hpow
  rw [initialRadius]
  nlinarith

/-- The literal grid count is at most `1/(16*delta)` in dimensions at least
two once the initial radius is at most one. -/
theorem initialCandidateCount_cast_le_inv_sixteen_mul
    {d : ℕ} {delta : ℝ}
    (hd : 2 ≤ d) (hdelta : 0 < delta)
    (hradius : initialRadius d delta ≤ 1) :
    (initialCandidateCount d delta : ℝ) ≤ 1 / (16 * delta) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hradiusPos : 0 < initialRadius d delta := by
    simp only [initialRadius]
    positivity
  let x := 2 / initialRadius d delta
  have hx : 2 ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ hradiusPos]
    nlinarith
  have hx0 : 0 ≤ x := hx.trans' (by norm_num)
  have hceil : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have haxis : (initialAxisCount d delta : ℝ) ≤
      4 / initialRadius d delta := by
    have hxupper : x + 2 ≤ 2 * x := by linarith
    rw [initialAxisCount, Nat.cast_add, Nat.cast_one]
    dsimp [x] at hceil ⊢
    calc
      (Nat.ceil (2 / initialRadius d delta) : ℝ) + 1
          ≤ 2 / initialRadius d delta + 2 := by linarith
      _ ≤ 2 * (2 / initialRadius d delta) := hxupper
      _ = 4 / initialRadius d delta := by ring
  have hcandidate : (initialCandidateCount d delta : ℝ) ≤
      (4 / initialRadius d delta) ^ d := by
    rw [initialCandidateCount, Nat.cast_pow]
    exact pow_le_pow_left₀ (by positivity) haxis d
  let root := delta ^ (1 / (d : ℝ))
  have hrootPos : 0 < root := Real.rpow_pos_of_pos hdelta _
  have hrootPow : root ^ d = delta := by
    dsimp [root]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdelta.le]
    have hmul : (1 / (d : ℝ)) * (d : ℝ) = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  have hscale : (4 / initialRadius d delta) ^ d =
      (1 / 4 : ℝ) ^ d / delta := by
    rw [initialRadius]
    change (4 / (16 * root)) ^ d = _
    rw [show 4 / (16 * root) = (1 / 4 : ℝ) / root by
      field_simp; ring]
    rw [div_pow, hrootPow]
  have hquarterPow : (1 / 4 : ℝ) ^ d ≤ 1 / 16 := by
    calc
      (1 / 4 : ℝ) ^ d ≤ (1 / 4 : ℝ) ^ (2 : ℕ) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
      _ = 1 / 16 := by norm_num
  calc
    (initialCandidateCount d delta : ℝ)
        ≤ (4 / initialRadius d delta) ^ d := hcandidate
    _ = (1 / 4 : ℝ) ^ d / delta := hscale
    _ ≤ (1 / 16 : ℝ) / delta :=
      div_le_div_of_nonneg_right hquarterPow hdelta.le
    _ = 1 / (16 * delta) := by field_simp

/-- The natural ceiling in the cutoff is bounded by the underlying real
quantity plus one. -/
theorem initialOccupancyCutoff_cast_le {delta : ℝ} {n : ℕ}
    (hdelta : 0 ≤ delta) :
    (initialOccupancyCutoff delta n : ℝ) ≤
      2 * delta * (n : ℝ) + 1 := by
  have hnonneg : 0 ≤ 2 * delta * (n : ℝ) := by positivity
  exact (Nat.ceil_lt_add_one hnonneg).le

/-- A retained cell contains strictly more than `delta * n` points. -/
theorem retained_occupancy_gt_delta_mul {delta : ℝ} {n occupancy : ℕ}
    (hdelta : 0 < delta) (hn : 0 < n)
    (hretained : initialOccupancyCutoff delta n ≤ occupancy) :
    delta * (n : ℝ) < occupancy := by
  have hceil :
      2 * delta * (n : ℝ) ≤ (initialOccupancyCutoff delta n : ℝ) := by
    exact Nat.le_ceil _
  have hretainedR :
      (initialOccupancyCutoff delta n : ℝ) ≤ occupancy := by
    exact_mod_cast hretained
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

/-- Elementary discard estimate.  The analytic grid count
`candidates ≤ 1/(16*delta)` and the large-input threshold
`1/(2*delta) ≤ n` imply that discarded cells contain at most half the
points (in fact, the proof gives the stronger quarter bound before rounding). -/
theorem discard_cost_le_half {delta : ℝ} {n candidates : ℕ}
    (hdelta : 0 < delta)
    (hcandidates : (candidates : ℝ) ≤ 1 / (16 * delta))
    (hnLarge : 1 / (2 * delta) ≤ (n : ℝ)) :
    candidates * initialOccupancyCutoff delta n ≤ n / 2 := by
  have hcutoff := initialOccupancyCutoff_cast_le (n := n) hdelta.le
  have hcandidates0 : (0 : ℝ) ≤ candidates := by positivity
  have hcutoff0 : (0 : ℝ) ≤ initialOccupancyCutoff delta n := by positivity
  have hprod :
      ((candidates * initialOccupancyCutoff delta n : ℕ) : ℝ) ≤
        (1 / (16 * delta)) * (2 * delta * (n : ℝ) + 1) := by
    push_cast
    exact mul_le_mul hcandidates hcutoff hcutoff0
      (by positivity : (0 : ℝ) ≤ 1 / (16 * delta))
  have hinv : 1 / (16 * delta) ≤ (n : ℝ) / 8 := by
    have heq : 1 / (16 * delta) = (1 / (2 * delta)) / 8 := by
      field_simp
      ring
    rw [heq]
    linarith
  have hquarter :
      ((candidates * initialOccupancyCutoff delta n : ℕ) : ℝ) ≤
        (n : ℝ) / 4 := by
    calc
      ((candidates * initialOccupancyCutoff delta n : ℕ) : ℝ)
          ≤ (1 / (16 * delta)) * (2 * delta * (n : ℝ) + 1) := hprod
      _ = (n : ℝ) / 8 + 1 / (16 * delta) := by
        field_simp
        ring
      _ ≤ (n : ℝ) / 8 + (n : ℝ) / 8 :=
        by linarith
      _ = (n : ℝ) / 4 := by ring
  norm_num only [Nat.cast_mul] at hquarter
  have hnat : 4 * (candidates * initialOccupancyCutoff delta n) ≤ n := by
    have hreal :
        ((4 * (candidates * initialOccupancyCutoff delta n) : ℕ) : ℝ) ≤ n := by
      push_cast
      nlinarith
    exact_mod_cast hreal
  omega

/-- Version of the discard estimate using the literal candidate-grid bound. -/
theorem discard_initial_cells_le_half {d n candidates : ℕ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hcandidates : candidates ≤ initialCandidateCount d delta)
    (hgrid : (initialCandidateCount d delta : ℝ) ≤ 1 / (16 * delta))
    (hnLarge : 1 / (2 * delta) ≤ (n : ℝ)) :
    candidates * initialOccupancyCutoff delta n ≤ n / 2 := by
  apply discard_cost_le_half hdelta _ hnLarge
  exact (by exact_mod_cast hcandidates : (candidates : ℝ) ≤
    initialCandidateCount d delta).trans hgrid

/-- Literal `n ≥ N₀(delta)` version of the initial discard estimate. -/
theorem discard_initial_cells_le_half_of_largeEnough
    {d n candidates : ℕ} {delta : ℝ}
    (hdelta : 0 < delta)
    (hcandidates : candidates ≤ initialCandidateCount d delta)
    (hgrid : (initialCandidateCount d delta : ℝ) ≤ 1 / (16 * delta))
    (hnLarge : initialLargeEnough delta ≤ n) :
    candidates * initialOccupancyCutoff delta n ≤ n / 2 := by
  apply discard_initial_cells_le_half hdelta hcandidates hgrid
  exact (Nat.le_ceil (1 / (2 * delta))).trans (by exact_mod_cast hnLarge)

/-- Number of dyadic occupancy levels needed between `delta*n` and `n`. -/
def dyadicLevelCount (delta : ℝ) : ℕ :=
  Nat.ceil (Real.log (1 / delta) / Real.log 2) + 1

/-- Once the logarithmic ratio is at least two, the number of dyadic levels is
at most twice that ratio, hence `O(log(1/delta))`. -/
theorem dyadicLevelCount_cast_le {delta : ℝ}
    (hlogRatio : 2 ≤ Real.log (1 / delta) / Real.log 2) :
    (dyadicLevelCount delta : ℝ) ≤
      (2 / Real.log 2) * Real.log (1 / delta) := by
  let x := Real.log (1 / delta) / Real.log 2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hceil : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have hcount : (dyadicLevelCount delta : ℝ) ≤ 2 * x := by
    simp only [dyadicLevelCount, Nat.cast_add, Nat.cast_one]
    dsimp [x] at hlogRatio hceil ⊢
    linarith
  calc
    (dyadicLevelCount delta : ℝ) ≤ 2 * x := hcount
    _ = (2 / Real.log 2) * Real.log (1 / delta) := by
      dsimp [x]
      field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)]

/-- The hypothesis of `dyadicLevelCount_cast_le` follows from the concrete
smallness condition `delta ≤ 1/4`. -/
theorem two_le_log_one_div_div_log_two {delta : ℝ}
    (hdelta : 0 < delta) (hdelta_small : delta ≤ 1 / 4) :
    2 ≤ Real.log (1 / delta) / Real.log 2 := by
  have hinv : (4 : ℝ) ≤ 1 / delta := by
    rw [le_div_iff₀ hdelta]
    nlinarith
  have hlog : Real.log (4 : ℝ) ≤ Real.log (1 / delta) :=
    Real.log_le_log (by norm_num) hinv
  have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlogFour] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).2 hlog

/-- Concrete small-`delta` logarithmic level bound. -/
theorem dyadicLevelCount_cast_le_of_le_quarter {delta : ℝ}
    (hdelta : 0 < delta) (hdelta_small : delta ≤ 1 / 4) :
    (dyadicLevelCount delta : ℝ) ≤
      (2 / Real.log 2) * Real.log (1 / delta) :=
  dyadicLevelCount_cast_le
    (two_le_log_one_div_div_log_two hdelta hdelta_small)

/-- Bundled initial-scale arithmetic in the form used by the geometric core.
For `delta` below the explicit dimension-dependent cutoff and
`n ≥ initialLargeEnough delta`, it supplies the radius, discard, retained-cell,
and dyadic-level conclusions simultaneously. -/
theorem initial_grid_arithmetic {d n candidates : ℕ} {delta : ℝ}
    (hd : 2 ≤ d) (hdelta : 0 < delta)
    (hdelta_small : delta < initialGridDeltaZero d)
    (hcandidates : candidates ≤ initialCandidateCount d delta)
    (hnLarge : initialLargeEnough delta ≤ n) :
    initialRadius d delta ≤ 1 ∧
    candidates * initialOccupancyCutoff delta n ≤ n / 2 ∧
    (∀ occupancy : ℕ, initialOccupancyCutoff delta n ≤ occupancy →
      delta * (n : ℝ) < occupancy) ∧
    (dyadicLevelCount delta : ℝ) ≤
      (2 / Real.log 2) * Real.log (1 / delta) := by
  have hdeltaRadius : delta ≤ initialRadiusDeltaZero d :=
    hdelta_small.le.trans (min_le_left _ _)
  have hdeltaQuarter : delta ≤ (1 / 4 : ℝ) :=
    hdelta_small.le.trans (min_le_right _ _)
  have hradius : initialRadius d delta ≤ 1 :=
    initialRadius_le_one (by omega) hdelta hdeltaRadius
  have hgrid :
      (initialCandidateCount d delta : ℝ) ≤ 1 / (16 * delta) :=
    initialCandidateCount_cast_le_inv_sixteen_mul hd hdelta hradius
  have hdiscard : candidates * initialOccupancyCutoff delta n ≤ n / 2 :=
    discard_initial_cells_le_half_of_largeEnough
      hdelta hcandidates hgrid hnLarge
  have hnLargeR : 1 / (2 * delta) ≤ (n : ℝ) :=
    (Nat.le_ceil (1 / (2 * delta))).trans (by exact_mod_cast hnLarge)
  have hn : 0 < n := by
    have hnR : (0 : ℝ) < n := (by positivity : (0 : ℝ) < 1 / (2 * delta)).trans_le hnLargeR
    exact_mod_cast hnR
  refine ⟨hradius, hdiscard, ?_,
    dyadicLevelCount_cast_le_of_le_quarter hdelta hdeltaQuarter⟩
  intro occupancy hretained
  exact retained_occupancy_gt_delta_mul hdelta hn hretained

end

end Erdos186.PZ.ConvexDensity
