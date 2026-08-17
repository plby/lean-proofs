/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ErdosProblems.Erdos636.AsymptoticThresholds
import ErdosProblems.Erdos636.AugmentationGraphPartial
import ErdosProblems.Erdos636.AugmentationGraphFull
import ErdosProblems.Erdos636.CrowdSchedule

/-!
# The power scales in the balanced augmentation

This file contains only numerical bookkeeping.  All parameters are defined
on the ambient order `n`; this avoids repeatedly transporting fractional
powers through the rounded switching size.  The exponents are those in the
Kwan--Sudakov argument:

* the outer concentration error is `n^(9/16)`;
* a canonical crowd block has length `floor (n^(5/8))`;
* inspections, buckets, windows, and retained crowds live on the square-root
  scale.

The strict exponent gaps used below are
`11/16 < 3/4` for the crowd schedule and `23/16 < 3/2` for the boundary
charge.
-/

open Filter
open scoped Topology

namespace Erdos636.AugmentationScales

noncomputable section

open AsymptoticThresholds

/-- Error used for simultaneous concentration over every time and cell. -/
def outerError (n : ℕ) : ℝ := (n : ℝ) ^ (9 / 16 : ℝ)

/-- Length of one contiguous block of the outer switching path. -/
def blockLength (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (5 / 8 : ℝ)⌋₊

/-- The coefficient is chosen so that a bucket and two local travels fit in
an `eta * sqrt n` window. -/
def smallStepCoeff (K : ℕ) (eta : ℝ) : ℝ :=
  eta / (2 * (1 + 4 * K))

/-- Spacing between consecutive inspections inside a block. -/
def stride (K : ℕ) (eta : ℝ) (n : ℕ) : ℕ :=
  ⌊smallStepCoeff K eta * Real.sqrt n⌋₊

/-- Width of one degree bucket. -/
def width (K : ℕ) (eta : ℝ) (n : ℕ) : ℕ := stride K eta n

/-- Maximum movement from a local time to its preceding inspection. -/
def travel (K : ℕ) (eta : ℝ) (n : ℕ) : ℕ :=
  2 * K * stride K eta n

/-- Radius of the crowd degree window. -/
def window (eta : ℝ) (n : ℕ) : ℕ :=
  ⌈eta * Real.sqrt n⌉₊

/-- Same-time degree spread supplied by the outer concentration event. -/
def spread (n : ℕ) : ℕ := ⌈2 * outerError n⌉₊

/-- Half-open interval span used by the natural-valued buckets. -/
def span (n : ℕ) : ℕ := spread n + 2

/-- Number of matching cells retained in each crowded fibre. -/
def threshold (n : ℕ) : ℕ := ⌊Real.sqrt n⌋₊

/-- The two-sided failure probability for one time/cell pair. -/
def outerFailure (K nW n : ℕ) : ℝ :=
  2 * Real.exp
    (-(outerError n) ^ 2 /
      (2 * (2 * (nW : ℝ)) * (2 * (K : ℝ)) ^ 2))

@[simp] lemma width_eq (K : ℕ) (eta : ℝ) (n : ℕ) :
    width K eta n = stride K eta n := rfl

@[simp] lemma travel_eq (K : ℕ) (eta : ℝ) (n : ℕ) :
    travel K eta n = 2 * K * stride K eta n := rfl

lemma smallStepCoeff_pos {K : ℕ} {eta : ℝ} (heta : 0 < eta) :
    0 < smallStepCoeff K eta := by
  dsimp [smallStepCoeff]
  positivity

/-- A reusable strict power-gap estimate. -/
theorem exists_mul_rpow_lt_mul_rpow
    {A B p q : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (hpq : p < q) :
    ∃ N : ℕ, ∀ n ≥ N,
      A * (n : ℝ) ^ p < B * (n : ℝ) ^ q := by
  let gap : ℝ := q - p
  have hgap : 0 < gap := by dsimp [gap]; linarith
  obtain ⟨Npow, hNpow⟩ := exists_nat_rpow_ge gap (2 * A / B) hgap
  refine ⟨max 1 Npow, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hNpow' : Npow ≤ n := (le_max_right _ _).trans hn
  have hnreal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hpow := hNpow n hNpow'
  have hscaled := mul_le_mul_of_nonneg_left hpow hB.le
  have hmain : 2 * A ≤ B * (n : ℝ) ^ gap := by
    have hBne : B ≠ 0 := hB.ne'
    calc
      2 * A = B * (2 * A / B) := by field_simp
      _ ≤ B * (n : ℝ) ^ gap := hscaled
  have hpnonneg : 0 ≤ (n : ℝ) ^ p := Real.rpow_nonneg hnreal.le _
  have hmul := mul_le_mul_of_nonneg_right hmain hpnonneg
  have hrewrite :
      (n : ℝ) ^ gap * (n : ℝ) ^ p = (n : ℝ) ^ q := by
    rw [← Real.rpow_add hnreal]
    dsimp [gap]
    congr 1
    ring
  have hmul' : 2 * (A * (n : ℝ) ^ p) ≤ B * (n : ℝ) ^ q := by
    calc
      2 * (A * (n : ℝ) ^ p) ≤
          (B * (n : ℝ) ^ gap) * (n : ℝ) ^ p := by
            simpa only [mul_assoc] using hmul
      _ = B * ((n : ℝ) ^ gap * (n : ℝ) ^ p) := by ring
      _ = B * (n : ℝ) ^ q := by rw [hrewrite]
  have htargetPos : 0 < B * (n : ℝ) ^ q :=
    mul_pos hB (Real.rpow_pos_of_pos hnreal _)
  nlinarith [hmul']

/-- A polynomial is dominated by an exponential in any positive power.
This is the sublinear-exponent form needed for the simultaneous outer
concentration bound. -/
theorem exists_rpow_mul_exp_neg_rpow_lt
    {A b p q epsilon : ℝ}
    (hA : 0 ≤ A) (hb : 0 < b) (hq : 0 < q) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N,
      A * (n : ℝ) ^ p * Real.exp (-b * (n : ℝ) ^ q) < epsilon := by
  have htReal : Tendsto
      (fun x : ℝ ↦ A * (x ^ (p / q) * Real.exp (-b * x)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p / q) b hb) :
        Tendsto (fun x : ℝ ↦ A *
          (x ^ (p / q) * Real.exp (-b * x))) atTop (𝓝 (A * 0)))
  have htPow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ q) atTop atTop :=
    (tendsto_rpow_atTop hq).comp tendsto_natCast_atTop_atTop
  have ht : Tendsto
      (fun n : ℕ ↦ A *
        (((n : ℝ) ^ q) ^ (p / q) * Real.exp (-b * (n : ℝ) ^ q)))
      atTop (𝓝 0) := htReal.comp htPow
  have hevent : ∀ᶠ n : ℕ in atTop,
      A * (((n : ℝ) ^ q) ^ (p / q) *
        Real.exp (-b * (n : ℝ) ^ q)) < epsilon :=
    ht.eventually (Iio_mem_nhds hepsilon)
  apply eventually_atTop.mp
  filter_upwards [hevent, eventually_ge_atTop 1] with n hn hn1
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : ((n : ℝ) ^ q) ^ (p / q) = (n : ℝ) ^ p := by
    rw [← Real.rpow_mul hnreal.le]
    congr 1
    field_simp
  simpa only [hpow, mul_assoc] using hn

lemma blockLength_upper (n : ℕ) :
    (blockLength n : ℝ) ≤ (n : ℝ) ^ (5 / 8 : ℝ) := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma stride_upper (K : ℕ) {eta : ℝ} (heta : 0 ≤ eta) (n : ℕ) :
    (stride K eta n : ℝ) ≤ smallStepCoeff K eta * Real.sqrt n := by
  exact Nat.floor_le (mul_nonneg (by
    dsimp [smallStepCoeff]
    positivity) (Real.sqrt_nonneg _))

lemma threshold_upper (n : ℕ) :
    (threshold n : ℝ) ≤ Real.sqrt n := by
  exact Nat.floor_le (Real.sqrt_nonneg _)

lemma blockLast_le_blockLength {nW n : ℕ}
    (q : Fin (Crowd.canonicalBlockCount nW (blockLength n))) :
    Crowd.canonicalBlockLast nW (blockLength n) q ≤ blockLength n := by
  rw [Crowd.canonicalBlockLast]
  exact (min_le_left _ _).trans (by omega)

/-- The bucket plus twice the local travel fits in the desired crowd
window.  This estimate is pointwise and needs no large-order threshold. -/
lemma radius_fits {K n : ℕ} {eta : ℝ} (heta : 0 ≤ eta) :
    width K eta n + 2 * travel K eta n ≤ window eta n := by
  have hstride := stride_upper K heta n
  have hcoeff : (0 : ℝ) ≤ 1 + 4 * K := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hstride hcoeff
  have hreal :
      ((width K eta n + 2 * travel K eta n : ℕ) : ℝ) ≤
        (window eta n : ℝ) := by
    push_cast
    simp only [width, travel]
    calc
      (stride K eta n : ℝ) +
          2 * (2 * K * (stride K eta n : ℕ) : ℕ) =
          (1 + 4 * K) * (stride K eta n : ℝ) := by
            push_cast
            ring
      _ ≤ (1 + 4 * K) *
          (smallStepCoeff K eta * Real.sqrt n) := hscaled
      _ = eta / 2 * Real.sqrt n := by
        dsimp [smallStepCoeff]
        field_simp
      _ ≤ eta * Real.sqrt n := by
        have hs : 0 ≤ eta * Real.sqrt n :=
          mul_nonneg heta (Real.sqrt_nonneg _)
        linarith
      _ ≤ (window eta n : ℝ) := Nat.le_ceil _
  exact_mod_cast hreal

/-! ## Simultaneous rounding bounds -/

/-- A positive real power survives a natural floor with at least half of
its value once the ambient order is large enough. -/
theorem exists_half_rpow_le_floor (p : ℝ) (hp : 0 < p) :
    ∃ N : ℕ, ∀ n ≥ N,
      (1 / 2 : ℝ) * (n : ℝ) ^ p ≤ (⌊(n : ℝ) ^ p⌋₊ : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_rpow_ge p 2 hp
  refine ⟨N, ?_⟩
  intro n hn
  have hlarge := hN n hn
  have hfloor := Nat.lt_floor_add_one ((n : ℝ) ^ p)
  linarith

/-- All floor/ceiling estimates used by the crowd schedule after one ambient
threshold. -/
structure RoundingBounds (K n : ℕ) (eta : ℝ) : Prop where
  order_pos : 1 ≤ n
  block_pos : 0 < blockLength n
  stride_pos : 0 < stride K eta n
  width_pos : 0 < width K eta n
  threshold_pos : 0 < threshold n
  block_lower :
    (1 / 2 : ℝ) * (n : ℝ) ^ (5 / 8 : ℝ) ≤ (blockLength n : ℝ)
  block_upper :
    (blockLength n : ℝ) ≤ (n : ℝ) ^ (5 / 8 : ℝ)
  stride_lower :
    smallStepCoeff K eta / 2 * Real.sqrt n ≤ (stride K eta n : ℝ)
  stride_upper :
    (stride K eta n : ℝ) ≤ smallStepCoeff K eta * Real.sqrt n
  threshold_lower :
    (1 / 2 : ℝ) * Real.sqrt n ≤ (threshold n : ℝ)
  threshold_upper : (threshold n : ℝ) ≤ Real.sqrt n
  window_upper : (window eta n : ℝ) ≤ 2 * eta * Real.sqrt n
  spread_upper : (spread n : ℝ) ≤ 3 * outerError n
  span_upper : (span n : ℝ) ≤ 5 * outerError n
  radius : width K eta n + 2 * travel K eta n ≤ window eta n

/-- Eventual positivity and two-sided rounding for every augmentation power
scale. -/
theorem exists_roundingBounds {K : ℕ} {eta : ℝ} (heta : 0 < eta) :
    ∃ N : ℕ, ∀ n ≥ N, RoundingBounds K n eta := by
  have ha : 0 < smallStepCoeff K eta := smallStepCoeff_pos heta
  obtain ⟨Nblock, hblock⟩ :=
    exists_half_rpow_le_floor (5 / 8 : ℝ) (by norm_num)
  obtain ⟨Nstride, hstride⟩ :=
    exists_half_mul_sqrt_le_floor (smallStepCoeff K eta) ha
  obtain ⟨Nthreshold, hthreshold⟩ :=
    exists_half_mul_sqrt_le_floor 1 (by norm_num)
  obtain ⟨Nwindow, hwindow⟩ := exists_const_le_mul_sqrt eta 1 heta
  obtain ⟨Nspread, hspread⟩ :=
    exists_nat_rpow_ge (9 / 16 : ℝ) 1 (by norm_num)
  let N := max 1 (max Nblock (max Nstride (max Nthreshold (max Nwindow Nspread))))
  refine ⟨N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have htail :
      max Nblock (max Nstride (max Nthreshold (max Nwindow Nspread))) ≤ n :=
    (le_max_right _ _).trans hn
  have hNb : Nblock ≤ n := (le_max_left _ _).trans htail
  have htail2 : max Nstride (max Nthreshold (max Nwindow Nspread)) ≤ n :=
    (le_max_right _ _).trans htail
  have hNs : Nstride ≤ n := (le_max_left _ _).trans htail2
  have htail3 : max Nthreshold (max Nwindow Nspread) ≤ n :=
    (le_max_right _ _).trans htail2
  have hNt : Nthreshold ≤ n := (le_max_left _ _).trans htail3
  have htail4 : max Nwindow Nspread ≤ n :=
    (le_max_right _ _).trans htail3
  have hNw : Nwindow ≤ n := (le_max_left _ _).trans htail4
  have hNsp : Nspread ≤ n := (le_max_right _ _).trans htail4
  have hbLower := hblock n hNb
  have hsLower := hstride n hNs
  have htLowerRaw := hthreshold n hNt
  have htLower :
      (1 / 2 : ℝ) * Real.sqrt n ≤ (threshold n : ℝ) := by
    simpa only [one_div, one_mul, threshold] using htLowerRaw
  have hwLarge := hwindow n hNw
  have hspLarge := hspread n hNsp
  have hwindowCeil : (window eta n : ℝ) < eta * Real.sqrt n + 1 := by
    exact Nat.ceil_lt_add_one
      (mul_nonneg heta.le (Real.sqrt_nonneg _))
  have hwUpper : (window eta n : ℝ) ≤ 2 * eta * Real.sqrt n := by
    exact (hwindowCeil.trans_le (by linarith)).le
  have hspreadCeil : (spread n : ℝ) < 2 * outerError n + 1 := by
    exact Nat.ceil_lt_add_one (by
      dsimp [outerError]
      positivity)
  have hspreadUpper : (spread n : ℝ) ≤ 3 * outerError n := by
    exact (hspreadCeil.trans_le (by
      dsimp [outerError] at hspLarge ⊢
      linarith)).le
  have hspanUpper : (span n : ℝ) ≤ 5 * outerError n := by
    rw [span]
    push_cast
    have : (1 : ℝ) ≤ outerError n := by simpa [outerError] using hspLarge
    linarith
  have hbpos : 0 < blockLength n := by
    have hp : 0 < (n : ℝ) ^ (5 / 8 : ℝ) := by
      apply Real.rpow_pos_of_pos
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have : (0 : ℝ) < blockLength n := lt_of_lt_of_le (by positivity) hbLower
    exact_mod_cast this
  have hspos : 0 < stride K eta n := by
    have hsqrt : 0 < Real.sqrt n := by
      apply Real.sqrt_pos.2
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have : (0 : ℝ) < stride K eta n :=
      lt_of_lt_of_le (mul_pos (by positivity) hsqrt) hsLower
    exact_mod_cast this
  have htpos : 0 < threshold n := by
    have hsqrt : 0 < Real.sqrt n := by
      apply Real.sqrt_pos.2
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have : (0 : ℝ) < threshold n :=
      lt_of_lt_of_le (mul_pos (by norm_num) hsqrt) htLower
    exact_mod_cast this
  exact {
    order_pos := hn1
    block_pos := hbpos
    stride_pos := hspos
    width_pos := by simpa only [width] using hspos
    threshold_pos := htpos
    block_lower := hbLower
    block_upper := blockLength_upper n
    stride_lower := hsLower
    stride_upper := stride_upper K heta.le n
    threshold_lower := htLower
    threshold_upper := threshold_upper n
    window_upper := hwUpper
    spread_upper := hspreadUpper
    span_upper := hspanUpper
    radius := radius_fits heta.le }

/-! ## Simultaneous outer concentration -/

/-- The `n^(9/16)` error gives exponentially small simultaneous failure
over every switching time and every matching cell.  The hypotheses on
`nW` and `matchingCard` are deliberately the exact coarse inequalities
available at the graph-facing call site. -/
theorem exists_outerConcentrationBudget
    {K : ℕ} (hK : 0 < K) {cW : ℝ} (hcW : 0 < cW) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ nW matchingCard : ℕ,
      1 ≤ nW → (nW : ℝ) ≤ cW * n → matchingCard ≤ n →
      ((((nW + 1) * matchingCard : ℕ) : ℝ) * outerFailure K nW n < 1) := by
  let b : ℝ := 1 / (16 * (K : ℝ) ^ 2 * cW)
  have hb : 0 < b := by dsimp [b]; positivity
  let A : ℝ := 2 * (cW + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨Ndecay, hdecay⟩ :=
    exists_rpow_mul_exp_neg_rpow_lt
      (A := A) (b := b) (p := 2) (q := 1 / 8) (epsilon := 1)
      hA hb (by norm_num) (by norm_num)
  refine ⟨max 1 Ndecay, ?_⟩
  intro n hn nW matchingCard hnW hnWupper hmatching
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hNdecay : Ndecay ≤ n := (le_max_right _ _).trans hn
  have hnreal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnreal1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnWreal : (0 : ℝ) < nW := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hnW)
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hdenpos :
      0 < (2 : ℝ) * (2 * nW) * (2 * K) ^ 2 := by positivity
  have herrorSq :
      (outerError n) ^ 2 = (n : ℝ) ^ (9 / 8 : ℝ) := by
    dsimp [outerError]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have hpowProduct :
      (n : ℝ) ^ (1 / 8 : ℝ) * n = (n : ℝ) ^ (9 / 8 : ℝ) := by
    calc
      (n : ℝ) ^ (1 / 8 : ℝ) * n =
          (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 / 8 : ℝ) + 1) := by
            rw [Real.rpow_add hnreal]
      _ = (n : ℝ) ^ (9 / 8 : ℝ) := by norm_num
  have hquot :
      b * (n : ℝ) ^ (1 / 8 : ℝ) ≤
        (outerError n) ^ 2 /
          ((2 : ℝ) * (2 * nW) * (2 * K) ^ 2) := by
    rw [le_div_iff₀ hdenpos]
    calc
      b * (n : ℝ) ^ (1 / 8 : ℝ) *
          ((2 : ℝ) * (2 * nW) * (2 * K) ^ 2) ≤
          b * (n : ℝ) ^ (1 / 8 : ℝ) *
            (16 * (K : ℝ) ^ 2 * (cW * n)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              calc
                (2 : ℝ) * (2 * nW) * (2 * K) ^ 2 =
                    16 * (K : ℝ) ^ 2 * nW := by ring
                _ ≤ 16 * (K : ℝ) ^ 2 * (cW * n) := by
                  exact mul_le_mul_of_nonneg_left hnWupper (by positivity)
      _ = (n : ℝ) ^ (1 / 8 : ℝ) * n := by
            dsimp [b]
            field_simp
      _ = (n : ℝ) ^ (9 / 8 : ℝ) := hpowProduct
      _ = (outerError n) ^ 2 := herrorSq.symm
  have hexp :
      Real.exp (-((outerError n) ^ 2 /
          ((2 : ℝ) * (2 * nW) * (2 * K) ^ 2))) ≤
        Real.exp (-b * (n : ℝ) ^ (1 / 8 : ℝ)) := by
    exact Real.exp_le_exp.mpr (by simpa only [neg_mul] using neg_le_neg hquot)
  have hnWone : (nW : ℝ) + 1 ≤ (cW + 1) * n := by
    nlinarith [hnWupper]
  have hmatchingReal : (matchingCard : ℝ) ≤ n := by exact_mod_cast hmatching
  have hprefactor :
      (2 : ℝ) * ((nW : ℝ) + 1) * matchingCard ≤
        A * (n : ℝ) ^ (2 : ℝ) := by
    calc
      (2 : ℝ) * ((nW : ℝ) + 1) * matchingCard ≤
          2 * ((cW + 1) * n) * n := by gcongr
      _ = A * (n : ℝ) ^ (2 : ℝ) := by
        rw [Real.rpow_two]
        dsimp [A]
        ring
  have hExpNonneg :
      0 ≤ Real.exp (-((outerError n) ^ 2 /
        ((2 : ℝ) * (2 * nW) * (2 * K) ^ 2))) :=
    (Real.exp_pos _).le
  have hExpBoundNonneg :
      0 ≤ Real.exp (-b * (n : ℝ) ^ (1 / 8 : ℝ)) :=
    (Real.exp_pos _).le
  have hbound :
      (2 : ℝ) * ((nW : ℝ) + 1) * matchingCard *
          Real.exp (-((outerError n) ^ 2 /
            ((2 : ℝ) * (2 * nW) * (2 * K) ^ 2))) ≤
        A * (n : ℝ) ^ (2 : ℝ) *
          Real.exp (-b * (n : ℝ) ^ (1 / 8 : ℝ)) := by
    calc
      (2 : ℝ) * ((nW : ℝ) + 1) * matchingCard *
          Real.exp (-((outerError n) ^ 2 /
            ((2 : ℝ) * (2 * nW) * (2 * K) ^ 2))) ≤
          A * (n : ℝ) ^ (2 : ℝ) *
            Real.exp (-((outerError n) ^ 2 /
              ((2 : ℝ) * (2 * nW) * (2 * K) ^ 2))) := by
                exact mul_le_mul_of_nonneg_right hprefactor hExpNonneg
      _ ≤ A * (n : ℝ) ^ (2 : ℝ) *
          Real.exp (-b * (n : ℝ) ^ (1 / 8 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hdecay' := hdecay n hNdecay
  have hfinal := hbound.trans_lt hdecay'
  simpa only [outerFailure, neg_div, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    mul_assoc, mul_left_comm, mul_comm] using hfinal

/-! ## Crowd-schedule counting -/

/-- The exact strict schedule count follows from the rounded scale bounds
and the sole exponent-gap inequality `n^(11/16) = o(n^(3/4))`. -/
lemma schedule_count_of_rounding
    {K n : ℕ} {eta b : ℝ}
    (heta : 0 < eta) (hb : 0 < b) (H : RoundingBounds K n eta)
    (hgap :
      ((2 / smallStepCoeff K eta + 1) *
          (10 / smallStepCoeff K eta + 1)) *
          (n : ℝ) ^ (11 / 16 : ℝ) <
        b * (n : ℝ) ^ (3 / 4 : ℝ))
    {nW matchingCard : ℕ}
    (hmatching : b * (n : ℝ) ^ (3 / 4 : ℝ) ≤ matchingCard)
    (q : Fin (Crowd.canonicalBlockCount nW (blockLength n))) :
    (Crowd.canonicalBlockLast nW (blockLength n) q /
          stride K eta n + 1) *
        Crowd.natBucketCount (span n) (width K eta n) * threshold n <
      matchingCard := by
  let a : ℝ := smallStepCoeff K eta
  have ha : 0 < a := smallStepCoeff_pos heta
  have hnreal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one H.order_pos)
  have hnreal1 : (1 : ℝ) ≤ n := by exact_mod_cast H.order_pos
  have hsqrt : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow _
  have hpow18 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow hnreal1 (by norm_num)
  have hpow116 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) :=
    Real.one_le_rpow hnreal1 (by norm_num)
  have hstrideReal : (0 : ℝ) < stride K eta n := by
    exact_mod_cast H.stride_pos
  have hinspection :
      ((Crowd.canonicalBlockLast nW (blockLength n) q /
          stride K eta n + 1 : ℕ) : ℝ) ≤
        (2 / a + 1) * (n : ℝ) ^ (1 / 8 : ℝ) := by
    have hlast := blockLast_le_blockLength q
    have hcastDiv :
        ((Crowd.canonicalBlockLast nW (blockLength n) q /
            stride K eta n : ℕ) : ℝ) ≤
          (Crowd.canonicalBlockLast nW (blockLength n) q : ℝ) /
            stride K eta n := Nat.cast_div_le
    have hnum :
        (Crowd.canonicalBlockLast nW (blockLength n) q : ℝ) ≤
          (n : ℝ) ^ (5 / 8 : ℝ) := by
      calc
        (Crowd.canonicalBlockLast nW (blockLength n) q : ℝ) ≤
            (blockLength n : ℝ) := by exact_mod_cast hlast
        _ ≤ (n : ℝ) ^ (5 / 8 : ℝ) := H.block_upper
    have hratio :
        (Crowd.canonicalBlockLast nW (blockLength n) q : ℝ) /
            stride K eta n ≤
          (2 / a) * (n : ℝ) ^ (1 / 8 : ℝ) := by
      calc
        (Crowd.canonicalBlockLast nW (blockLength n) q : ℝ) /
              stride K eta n ≤
            ((n : ℝ) ^ (5 / 8 : ℝ)) /
              (a / 2 * Real.sqrt n) := by
                exact div_le_div₀ (Real.rpow_nonneg hnreal.le _) hnum
                  (by positivity) H.stride_lower
        _ = (2 / a) * (n : ℝ) ^ (1 / 8 : ℝ) := by
          rw [hsqrt]
          have hp : (n : ℝ) ^ (5 / 8 : ℝ) =
              (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_add hnreal]
            norm_num
          rw [hp]
          field_simp
    push_cast
    calc
      ((Crowd.canonicalBlockLast nW (blockLength n) q /
          stride K eta n : ℕ) : ℝ) + 1 ≤
          (2 / a) * (n : ℝ) ^ (1 / 8 : ℝ) + 1 := by linarith
      _ ≤ (2 / a) * (n : ℝ) ^ (1 / 8 : ℝ) +
          (n : ℝ) ^ (1 / 8 : ℝ) := by linarith
      _ = (2 / a + 1) * (n : ℝ) ^ (1 / 8 : ℝ) := by ring
  have hwidthReal : (0 : ℝ) < width K eta n := by
    exact_mod_cast H.width_pos
  have hbucket :
      (Crowd.natBucketCount (span n) (width K eta n) : ℝ) ≤
        (10 / a + 1) * (n : ℝ) ^ (1 / 16 : ℝ) := by
    have hcastDiv :
        (((span n) / (width K eta n) : ℕ) : ℝ) ≤
          (span n : ℝ) / width K eta n := Nat.cast_div_le
    have hratio :
        (span n : ℝ) / width K eta n ≤
          (10 / a) * (n : ℝ) ^ (1 / 16 : ℝ) := by
      calc
        (span n : ℝ) / width K eta n ≤
            (5 * (n : ℝ) ^ (9 / 16 : ℝ)) /
              (a / 2 * Real.sqrt n) := by
                exact div_le_div₀ (by positivity) (by
                  simpa only [outerError] using H.span_upper)
                  (by positivity) (by simpa only [width, a] using H.stride_lower)
        _ = (10 / a) * (n : ℝ) ^ (1 / 16 : ℝ) := by
          rw [hsqrt]
          have hp : (n : ℝ) ^ (9 / 16 : ℝ) =
              (n : ℝ) ^ (1 / 16 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_add hnreal]
            norm_num
          rw [hp]
          field_simp
          norm_num
    rw [Crowd.natBucketCount]
    push_cast
    calc
      (((span n) / width K eta n : ℕ) : ℝ) + 1 ≤
          (10 / a) * (n : ℝ) ^ (1 / 16 : ℝ) + 1 := by linarith
      _ ≤ (10 / a) * (n : ℝ) ^ (1 / 16 : ℝ) +
          (n : ℝ) ^ (1 / 16 : ℝ) := by linarith
      _ = (10 / a + 1) * (n : ℝ) ^ (1 / 16 : ℝ) := by ring
  have hthreshold : (threshold n : ℝ) ≤
      (n : ℝ) ^ (1 / 2 : ℝ) := by
    simpa only [Real.sqrt_eq_rpow] using H.threshold_upper
  have hcoeff1 : 0 ≤ 2 / a + 1 := by positivity
  have hcoeff2 : 0 ≤ 10 / a + 1 := by positivity
  have hinspection' :
      ((Crowd.canonicalBlockLast nW (blockLength n) q /
          stride K eta n : ℕ) : ℝ) + 1 ≤
        (2 / a + 1) * (n : ℝ) ^ (1 / 8 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hinspection
  have hpowProduct :
      (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (1 / 16 : ℝ) *
          (n : ℝ) ^ (1 / 2 : ℝ) = (n : ℝ) ^ (11 / 16 : ℝ) := by
    rw [← Real.rpow_add hnreal, ← Real.rpow_add hnreal]
    norm_num
  have hproduct :
      (((Crowd.canonicalBlockLast nW (blockLength n) q /
            stride K eta n + 1) *
          Crowd.natBucketCount (span n) (width K eta n) *
          threshold n : ℕ) : ℝ) ≤
        ((2 / a + 1) * (10 / a + 1)) *
          (n : ℝ) ^ (11 / 16 : ℝ) := by
    push_cast
    calc
      (((Crowd.canonicalBlockLast nW (blockLength n) q /
            stride K eta n : ℕ) : ℝ) + 1) *
          Crowd.natBucketCount (span n) (width K eta n) * threshold n ≤
        ((2 / a + 1) * (n : ℝ) ^ (1 / 8 : ℝ)) *
          ((10 / a + 1) * (n : ℝ) ^ (1 / 16 : ℝ)) *
          (n : ℝ) ^ (1 / 2 : ℝ) := by gcongr
      _ = ((2 / a + 1) * (10 / a + 1)) *
          (n : ℝ) ^ (11 / 16 : ℝ) := by
            rw [← hpowProduct]
            ring
  have hmatchingReal : b * (n : ℝ) ^ (3 / 4 : ℝ) ≤
      (matchingCard : ℝ) := hmatching
  have hstrict :
      (((Crowd.canonicalBlockLast nW (blockLength n) q /
            stride K eta n + 1) *
          Crowd.natBucketCount (span n) (width K eta n) *
          threshold n : ℕ) : ℝ) < matchingCard := by
    exact hproduct.trans_lt (hgap.trans_le hmatchingReal)
  exact_mod_cast hstrict

/-- The canonical crowd schedule has enough matching cells after one
ambient threshold. -/
theorem exists_crowdScheduleCount
    {K : ℕ} {eta b : ℝ} (heta : 0 < eta) (hb : 0 < b) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ nW matchingCard : ℕ,
      b * (n : ℝ) ^ (3 / 4 : ℝ) ≤ matchingCard →
      ∀ q : Fin (Crowd.canonicalBlockCount nW (blockLength n)),
        (Crowd.canonicalBlockLast nW (blockLength n) q /
              stride K eta n + 1) *
            Crowd.natBucketCount (span n) (width K eta n) * threshold n <
          matchingCard := by
  have ha : 0 < smallStepCoeff K eta := smallStepCoeff_pos heta
  let C : ℝ := (2 / smallStepCoeff K eta + 1) *
    (10 / smallStepCoeff K eta + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨Nround, hround⟩ := exists_roundingBounds (K := K) heta
  obtain ⟨Ngap, hgap⟩ := exists_mul_rpow_lt_mul_rpow
    (A := C) (B := b) (p := 11 / 16) (q := 3 / 4)
    hC hb (by norm_num)
  refine ⟨max Nround Ngap, ?_⟩
  intro n hn nW matchingCard hmatching q
  apply schedule_count_of_rounding heta hb
    (hround n ((le_max_left _ _).trans hn))
  · simpa only [C] using hgap n ((le_max_right _ _).trans hn)
  · exact hmatching

/-! ## Boundary exceptional charge -/

/-- The charged block boundaries have scale `n^(23/16)`, strictly below
the `n^(3/2)` marked-packing budget. -/
lemma boundary_budget_of_rounding
    {K n nW : ℕ} {eta cW epsilon : ℝ}
    (hcW : 0 ≤ cW) (hepsilon : 0 < epsilon)
    (H : RoundingBounds K n eta)
    (hnW : (nW : ℝ) ≤ cW * n)
    (hgap :
      (2 * cW * (2 * K + 4)) * (n : ℝ) ^ (23 / 16 : ℝ) <
        epsilon * (n : ℝ) ^ (3 / 2 : ℝ)) :
    ((((nW / blockLength n) * (spread n + 2 * K + 1) : ℕ) : ℝ) *
        Real.sqrt n < epsilon * n * Real.sqrt n) := by
  have hnreal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one H.order_pos)
  have hnreal1 : (1 : ℝ) ≤ n := by exact_mod_cast H.order_pos
  have hblockReal : (0 : ℝ) < blockLength n := by
    exact_mod_cast H.block_pos
  have hpow916 : (1 : ℝ) ≤ (n : ℝ) ^ (9 / 16 : ℝ) :=
    Real.one_le_rpow hnreal1 (by norm_num)
  have hdivCast : ((nW / blockLength n : ℕ) : ℝ) ≤
      (nW : ℝ) / blockLength n := Nat.cast_div_le
  have hfirst : ((nW / blockLength n : ℕ) : ℝ) ≤
      2 * cW * (n : ℝ) ^ (3 / 8 : ℝ) := by
    have hratio : (nW : ℝ) / blockLength n ≤
        2 * cW * (n : ℝ) ^ (3 / 8 : ℝ) := by
      calc
        (nW : ℝ) / blockLength n ≤
            (cW * n) /
              ((1 / 2 : ℝ) * (n : ℝ) ^ (5 / 8 : ℝ)) := by
                exact div_le_div₀ (by positivity) hnW
                  (by positivity) H.block_lower
        _ = 2 * cW * (n : ℝ) ^ (3 / 8 : ℝ) := by
          have hp : (n : ℝ) =
              (n : ℝ) ^ (3 / 8 : ℝ) * (n : ℝ) ^ (5 / 8 : ℝ) := by
            rw [← Real.rpow_add hnreal]
            norm_num
          field_simp
          nlinarith [hp]
    exact hdivCast.trans hratio
  have hsecond : ((spread n + 2 * K + 1 : ℕ) : ℝ) ≤
      (2 * K + 4 : ℝ) * (n : ℝ) ^ (9 / 16 : ℝ) := by
    push_cast
    have hspread : (spread n : ℝ) ≤ 3 * (n : ℝ) ^ (9 / 16 : ℝ) := by
      simpa only [outerError] using H.spread_upper
    have hconst : (2 : ℝ) * K + 1 ≤
        ((2 : ℝ) * K + 1) * (n : ℝ) ^ (9 / 16 : ℝ) := by
      have hnonneg : (0 : ℝ) ≤ 2 * K + 1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hpow916 hnonneg]
    nlinarith
  have hsqrt : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow _
  have hsecond' :
      (spread n : ℝ) + 2 * K + 1 ≤
        (2 * K + 4 : ℝ) * (n : ℝ) ^ (9 / 16 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      using hsecond
  have hpowProduct :
      (n : ℝ) ^ (3 / 8 : ℝ) * (n : ℝ) ^ (9 / 16 : ℝ) *
          (n : ℝ) ^ (1 / 2 : ℝ) = (n : ℝ) ^ (23 / 16 : ℝ) := by
    rw [← Real.rpow_add hnreal, ← Real.rpow_add hnreal]
    norm_num
  have hcharge :
      ((((nW / blockLength n) * (spread n + 2 * K + 1) : ℕ) : ℝ) *
          Real.sqrt n) ≤
        (2 * cW * (2 * K + 4)) * (n : ℝ) ^ (23 / 16 : ℝ) := by
    push_cast
    rw [hsqrt]
    calc
      ((nW / blockLength n : ℕ) : ℝ) *
          ((spread n : ℝ) + 2 * K + 1) * (n : ℝ) ^ (1 / 2 : ℝ) ≤
        (2 * cW * (n : ℝ) ^ (3 / 8 : ℝ)) *
          ((2 * K + 4 : ℝ) * (n : ℝ) ^ (9 / 16 : ℝ)) *
          (n : ℝ) ^ (1 / 2 : ℝ) := by
            gcongr
      _ = (2 * cW * (2 * K + 4)) *
          (n : ℝ) ^ (23 / 16 : ℝ) := by
            rw [← hpowProduct]
            ring
  have htarget : epsilon * (n : ℝ) ^ (3 / 2 : ℝ) =
      epsilon * n * Real.sqrt n := by
    rw [hsqrt]
    have hp : (n : ℝ) ^ (3 / 2 : ℝ) =
        (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hnreal]
      norm_num
    rw [hp, Real.rpow_one]
    ring
  exact hcharge.trans_lt (hgap.trans_eq htarget)

/-- Concrete `o(n^(3/2))` boundary budget against any fixed positive
coefficient. -/
theorem exists_boundaryBudget
    {K : ℕ} {eta cW epsilon : ℝ}
    (heta : 0 < eta) (hcW : 0 < cW) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ nW : ℕ,
      (nW : ℝ) ≤ cW * n →
      ((((nW / blockLength n) * (spread n + 2 * K + 1) : ℕ) : ℝ) *
          Real.sqrt n < epsilon * n * Real.sqrt n) := by
  let C : ℝ := 2 * cW * (2 * K + 4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨Nround, hround⟩ := exists_roundingBounds (K := K) heta
  obtain ⟨Ngap, hgap⟩ := exists_mul_rpow_lt_mul_rpow
    (A := C) (B := epsilon) (p := 23 / 16) (q := 3 / 2)
    hC hepsilon (by norm_num)
  refine ⟨max Nround Ngap, ?_⟩
  intro n hn nW hnW
  exact boundary_budget_of_rounding hcW.le hepsilon
    (hround n ((le_max_left _ _).trans hn)) hnW
    (by simpa only [C] using hgap n ((le_max_right _ _).trans hn))

/-! ## Uniform rounded branch parameters -/

/-- Final consequences of `RoundedParameters.Bounds` for one outer
parameter, branch, and structural arity.  Besides feasibility, the structure
records the exact linear piece coefficient and square-root index coefficient
used by `PointwiseWindows`. -/
structure BranchBounds
    (c c₀ δ₀ δZ : ℝ) (K n ell k : ℕ) (branch : Bool) : Prop where
  deletion_le_parameter : OuterAssembly.deletionSize c₀ n ≤ ell
  deletion_lower :
    c₀ / 2 * n ≤ (OuterAssembly.deletionSize c₀ n : ℝ)
  deletion_upper :
    (OuterAssembly.deletionSize c₀ n : ℝ) ≤ c₀ * n
  order_pos :
    0 < RoundedParameters.branchScale branch
      (OuterAssembly.deletionSize c₀ n)
  order_lower :
    c₀ / 2 * n ≤
      (RoundedParameters.branchScale branch
        (OuterAssembly.deletionSize c₀ n) : ℝ)
  order_upper :
    (RoundedParameters.branchScale branch
        (OuterAssembly.deletionSize c₀ n) : ℝ) ≤ 2 * c₀ * n
  feasible :
    2 * RoundedParameters.branchScale branch
        (OuterAssembly.deletionSize c₀ n) ≤
      RoundedParameters.branchScale branch ell
  augmentation_two :
    2 ≤ OuterAssembly.augmentationSize δ₀
      (OuterAssembly.deletionSize c₀ n) k
  augmentation_lower :
    δ₀ / (4 * K) *
        Real.sqrt (RoundedParameters.branchScale branch
          (OuterAssembly.deletionSize c₀ n)) ≤
      (OuterAssembly.augmentationSize δ₀
        (OuterAssembly.deletionSize c₀ n) k : ℝ)
  augmentation_upper :
    (OuterAssembly.augmentationSize δ₀
        (OuterAssembly.deletionSize c₀ n) k : ℝ) ≤
      δZ * Real.sqrt (RoundedParameters.branchScale branch
        (OuterAssembly.deletionSize c₀ n))
  piece_scale : ∀ {a₂ L : ℝ}, 0 ≤ a₂ →
    a₂ * OuterAssembly.augmentationSize δ₀
        (OuterAssembly.deletionSize c₀ n) k *
        Real.sqrt (RoundedParameters.branchScale branch
          (OuterAssembly.deletionSize c₀ n)) ≤ L →
    a₂ * δ₀ * c₀ / (4 * K) * n ≤ L
  index_scale : ∀ {bIndex m : ℝ}, 0 ≤ bIndex →
    bIndex * Real.sqrt (RoundedParameters.branchScale branch
        (OuterAssembly.deletionSize c₀ n)) ≤ m →
    bIndex * Real.sqrt (c₀ / 2) * Real.sqrt n ≤ m

/-- Extract all branch-scale estimates from the repository's established
uniform rounding package. -/
lemma branchBounds_of_rounding
    {c c₀ δ₀ δZ : ℝ} {K n ell k : ℕ} {branch : Bool}
    (hc₀ : 0 < c₀) (hδ₀ : 0 < δ₀) (hK : 0 < K)
    (hell : ell ∈ RoundedParameters.outerParameterInterval c n)
    (hk1 : 1 ≤ k) (hkK : k ≤ K)
    (H : RoundedParameters.Bounds c c₀ δ₀ δZ K n) :
    BranchBounds c c₀ δ₀ δZ K n ell k branch := by
  let f : ℕ := OuterAssembly.deletionSize c₀ n
  let nD : ℕ := RoundedParameters.branchScale branch f
  let nZ : ℕ := OuterAssembly.augmentationSize δ₀ f k
  have hfLower : c₀ / 2 * n ≤ (f : ℝ) := by
    simpa only [f] using H.deletion_lower
  have hfUpper : (f : ℝ) ≤ c₀ * n := by
    simpa only [f] using H.deletion_upper
  have hnDLower : c₀ / 2 * n ≤ (nD : ℝ) := by
    simpa only [nD, f] using H.branch_linear_lower branch
  have hnDUpper : (nD : ℝ) ≤ 2 * c₀ * n := by
    simpa only [nD, f] using H.branch_linear_upper branch
  have hnZtwo : 2 ≤ nZ := by
    simpa only [nZ, f] using H.augmentation_two k hk1 hkK
  have hfpos : 0 < f := by
    by_contra hfnot
    have hfzero : f = 0 := Nat.eq_zero_of_not_pos hfnot
    have hnZzero : nZ = 0 := by
      simp [nZ, hfzero, OuterAssembly.augmentationSize]
    omega
  have hfposReal : (0 : ℝ) < f := by exact_mod_cast hfpos
  have hnDpos : 0 < nD := by
    dsimp [nD]
    exact RoundedParameters.branchScale_pos hfpos
  have hf_le_nD : f ≤ nD := by
    cases branch <;> simp [nD] <;> omega
  have hf_sqrt_le : Real.sqrt f ≤ Real.sqrt nD := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hf_le_nD)
  have hnD_le_two_f : nD ≤ 2 * f := by
    simpa only [nD] using
      RoundedParameters.branchScale_le_two_mul branch f
  have hsqrt_nD_le_two_sqrt_f : Real.sqrt nD ≤ 2 * Real.sqrt f := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hfSq : (Real.sqrt f) ^ 2 = (f : ℝ) :=
        Real.sq_sqrt (Nat.cast_nonneg f)
      have hnDreal : (nD : ℝ) ≤ 2 * f := by exact_mod_cast hnD_le_two_f
      nlinarith
  have hnZLowerRaw : δ₀ / (2 * K) * Real.sqrt f ≤ (nZ : ℝ) := by
    simpa only [nZ, f] using H.augmentation_lower k hk1 hkK
  have hnZLower : δ₀ / (4 * K) * Real.sqrt nD ≤ (nZ : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hsqrt_nD_le_two_sqrt_f
      (show 0 ≤ δ₀ / (4 * K) by positivity)
    calc
      δ₀ / (4 * K) * Real.sqrt nD ≤
          δ₀ / (4 * K) * (2 * Real.sqrt f) := hscaled
      _ = δ₀ / (2 * K) * Real.sqrt f := by ring
      _ ≤ nZ := hnZLowerRaw
  have hfeasible : 2 * nD ≤ RoundedParameters.branchScale branch ell := by
    have hthree := H.reservoir_large branch ell hell
    have hthree' : 3 * nD ≤ RoundedParameters.branchScale branch ell := by
      simpa only [nD, f] using hthree
    omega
  have hfEll : f ≤ ell := by
    have hthree := H.reservoir_large false ell hell
    have hthree' : 3 * f ≤ ell := by
      simpa only [RoundedParameters.branchScale_false, f] using hthree
    omega
  refine {
    deletion_le_parameter := by simpa only [f] using hfEll
    deletion_lower := by simpa only [f] using hfLower
    deletion_upper := by simpa only [f] using hfUpper
    order_pos := by simpa only [nD, f] using hnDpos
    order_lower := by simpa only [nD, f] using hnDLower
    order_upper := by simpa only [nD, f] using hnDUpper
    feasible := by simpa only [nD, f] using hfeasible
    augmentation_two := by
      simpa only [nZ, f] using H.augmentation_two k hk1 hkK
    augmentation_lower := by simpa only [nZ, nD, f] using hnZLower
    augmentation_upper := by
      simpa only [nZ, nD, f] using H.augmentation_upper branch k hk1 hkK
    piece_scale := ?_
    index_scale := ?_ }
  · intro a₂ L ha₂ hL
    have hsqrtF : (Real.sqrt f) ^ 2 = (f : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg f)
    have hnZnonneg : (0 : ℝ) ≤ nZ := by positivity
    have hfirst : δ₀ / (2 * K) * (f : ℝ) ≤
        (nZ : ℝ) * Real.sqrt nD := by
      calc
        δ₀ / (2 * K) * (f : ℝ) =
            (δ₀ / (2 * K) * Real.sqrt f) * Real.sqrt f := by
              calc
                δ₀ / (2 * K) * (f : ℝ) =
                    δ₀ / (2 * K) * (Real.sqrt f) ^ 2 := by rw [hsqrtF]
                _ = (δ₀ / (2 * K) * Real.sqrt f) * Real.sqrt f := by ring
        _ ≤ (nZ : ℝ) * Real.sqrt f := by gcongr
        _ ≤ (nZ : ℝ) * Real.sqrt nD := by gcongr
    have hscaled := mul_le_mul_of_nonneg_left hfirst ha₂
    calc
      a₂ * δ₀ * c₀ / (4 * K) * (n : ℝ) ≤
          a₂ * (δ₀ / (2 * K) * (f : ℝ)) := by
            have hcoeff : δ₀ / (2 * K) * (c₀ / 2 * n) ≤
                δ₀ / (2 * K) * (f : ℝ) := by gcongr
            calc
              a₂ * δ₀ * c₀ / (4 * K) * (n : ℝ) =
                  a₂ * (δ₀ / (2 * K) * (c₀ / 2 * n)) := by ring
              _ ≤ a₂ * (δ₀ / (2 * K) * (f : ℝ)) :=
                mul_le_mul_of_nonneg_left hcoeff ha₂
      _ ≤ a₂ * ((nZ : ℝ) * Real.sqrt nD) := hscaled
      _ = a₂ * nZ * Real.sqrt nD := by ring
      _ ≤ L := by simpa only [nZ, nD, f] using hL
  · intro bIndex m hbIndex hm
    have hlowerNonneg : 0 ≤ c₀ / 2 * (n : ℝ) := by positivity
    have hsqrtLower : Real.sqrt (c₀ / 2 * (n : ℝ)) ≤ Real.sqrt nD :=
      Real.sqrt_le_sqrt hnDLower
    have hsqrtProduct : Real.sqrt (c₀ / 2 * (n : ℝ)) =
        Real.sqrt (c₀ / 2) * Real.sqrt n := by
      exact Real.sqrt_mul (by positivity) _
    calc
      bIndex * Real.sqrt (c₀ / 2) * Real.sqrt n =
          bIndex * Real.sqrt (c₀ / 2 * (n : ℝ)) := by rw [hsqrtProduct]; ring
      _ ≤ bIndex * Real.sqrt nD := by gcongr
      _ ≤ m := by simpa only [nD, f] using hm

/-- One threshold supplies the branch package uniformly over every outer
parameter, both branches, and all `1 ≤ k ≤ K`. -/
theorem exists_branchBounds
    {c c₀ δ₀ δZ : ℝ} {K : ℕ}
    (hc : 0 < c) (hc₀ : 0 < c₀) (hsmall : 6 * c₀ ≤ c)
    (hδ₀ : 0 < δ₀) (hδZ : δ₀ ≤ δZ) (hK : 0 < K) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ell,
      ell ∈ RoundedParameters.outerParameterInterval c n →
      ∀ branch k, 1 ≤ k → k ≤ K →
        BranchBounds c c₀ δ₀ δZ K n ell k branch := by
  obtain ⟨N, hN⟩ := RoundedParameters.exists_uniform_rounding_threshold
    hc hc₀ hsmall hδ₀ hδZ hK
  refine ⟨N, ?_⟩
  intro n hn ell hell branch k hk1 hkK
  exact branchBounds_of_rounding hc₀ hδ₀ hK hell hk1 hkK (hN n hn)

/-! ## Raw-variation and window conversion -/

/-- A raw variation term of size `A * nW * sqrt nD` fits a prescribed
`epsilon * n sqrt n` packing budget once the fixed constants satisfy the
displayed small-`c₀` inequality. -/
lemma rawVariation_le_packingBudget
    {A cW c₀ epsilon : ℝ} {nW nD n : ℕ}
    (hA : 0 ≤ A) (hcW : 0 ≤ cW) (hc₀ : 0 ≤ c₀)
    (hnW : (nW : ℝ) ≤ cW * n)
    (hnD : (nD : ℝ) ≤ 2 * c₀ * n)
    (hsmall : A * cW * Real.sqrt (2 * c₀) ≤ epsilon) :
    A * nW * Real.sqrt nD ≤ epsilon * n * Real.sqrt n := by
  have hsqrt : Real.sqrt nD ≤ Real.sqrt (2 * c₀ * (n : ℝ)) :=
    Real.sqrt_le_sqrt hnD
  have hsqrtProduct : Real.sqrt (2 * c₀ * (n : ℝ)) =
      Real.sqrt (2 * c₀) * Real.sqrt n := by
    exact Real.sqrt_mul (by positivity) _
  have hnWnonneg : (0 : ℝ) ≤ nW := by positivity
  have hsqrtNonneg : 0 ≤ Real.sqrt nD := Real.sqrt_nonneg _
  calc
    A * (nW : ℝ) * Real.sqrt nD ≤
        A * (cW * n) * Real.sqrt (2 * c₀ * (n : ℝ)) := by gcongr
    _ = (A * cW * Real.sqrt (2 * c₀)) * n * Real.sqrt n := by
      rw [hsqrtProduct]
      ring
    _ ≤ epsilon * n * Real.sqrt n := by gcongr

/-! ## One threshold for the complete ambient scale package -/

/-- The four ambient numerical obligations consumed by the graph-facing
augmentation integration. -/
structure OuterBounds
    (K n : ℕ) (eta cW matchingCoeff boundaryCoeff : ℝ) : Prop where
  rounding : RoundingBounds K n eta
  concentration : ∀ nW matchingCard : ℕ,
    1 ≤ nW → (nW : ℝ) ≤ cW * n → matchingCard ≤ n →
      ((((nW + 1) * matchingCard : ℕ) : ℝ) * outerFailure K nW n < 1)
  schedule_count : ∀ nW matchingCard : ℕ,
    matchingCoeff * (n : ℝ) ^ (3 / 4 : ℝ) ≤ matchingCard →
    ∀ q : Fin (Crowd.canonicalBlockCount nW (blockLength n)),
      (Crowd.canonicalBlockLast nW (blockLength n) q /
            stride K eta n + 1) *
          Crowd.natBucketCount (span n) (width K eta n) * threshold n <
        matchingCard
  boundary_budget : ∀ nW : ℕ, (nW : ℝ) ≤ cW * n →
    ((((nW / blockLength n) * (spread n + 2 * K + 1) : ℕ) : ℝ) *
      Real.sqrt n < boundaryCoeff * n * Real.sqrt n)

/-- One literal natural threshold makes every ambient rounding,
concentration, crowd-count, and boundary-budget estimate simultaneous. -/
theorem exists_outerBounds
    {K : ℕ} (hK : 0 < K)
    {eta cW matchingCoeff boundaryCoeff : ℝ}
    (heta : 0 < eta) (hcW : 0 < cW)
    (hmatchingCoeff : 0 < matchingCoeff)
    (hboundaryCoeff : 0 < boundaryCoeff) :
    ∃ N : ℕ, ∀ n ≥ N,
      OuterBounds K n eta cW matchingCoeff boundaryCoeff := by
  obtain ⟨Nr, hr⟩ := exists_roundingBounds (K := K) heta
  obtain ⟨Nc, hc⟩ := exists_outerConcentrationBudget hK hcW
  obtain ⟨Ns, hs⟩ := exists_crowdScheduleCount
    (K := K) heta hmatchingCoeff
  obtain ⟨Nb, hb⟩ := exists_boundaryBudget
    (K := K) heta hcW hboundaryCoeff
  let N := max Nr (max Nc (max Ns Nb))
  refine ⟨N, ?_⟩
  intro n hn
  have hNr : Nr ≤ n := (le_max_left _ _).trans hn
  have htail : max Nc (max Ns Nb) ≤ n := (le_max_right _ _).trans hn
  have hNc : Nc ≤ n := (le_max_left _ _).trans htail
  have htail2 : max Ns Nb ≤ n := (le_max_right _ _).trans htail
  have hNs : Ns ≤ n := (le_max_left _ _).trans htail2
  have hNb : Nb ≤ n := (le_max_right _ _).trans htail2
  exact {
    rounding := hr n hNr
    concentration := fun nW matchingCard hnW hnWupper hcard ↦
      hc n hNc nW matchingCard hnW hnWupper hcard
    schedule_count := fun nW matchingCard hcard q ↦
      hs n hNs nW matchingCard hcard q
    boundary_budget := fun nW hnW ↦ hb n hNb nW hnW }

/-! ## The six final outer numerical obligations -/

/-- Linear-scale centre rise reserved for the first switching. -/
def finalLambda (lambdaCoeff : ℝ) (n : ℕ) : ℝ :=
  lambdaCoeff * n * Real.sqrt n

/-- Separation increment between consecutive selected switching times. -/
def finalSigma (sigmaCoeff : ℝ) (n : ℕ) : ℝ := sigmaCoeff * n

/-- Edge-window separation scale. -/
def finalSeparation (RCoeff : ℝ) (n : ℕ) : ℝ := RCoeff * n

/-- The exact final index coefficient after the marked-packing denominator. -/
def finalIndexCoeff (K : ℕ) (eta RCoeff sigmaCoeff : ℝ) : ℝ :=
  smallStepCoeff K eta /
    (32 * ((⌈RCoeff / sigmaCoeff⌉₊ + 2 : ℕ) : ℝ))

/-- The exact linear piece coefficient supplied by `BranchBounds.piece_scale`. -/
def finalPieceCoeff (K : ℕ) (a₂ δ₀ c₀ : ℝ) : ℝ :=
  a₂ * δ₀ * c₀ / (4 * K)

/-- Conclusions (i)--(iv) and (vi) at one ambient order.  Conclusion (v)
is supplied without further asymptotics by `BranchBounds.piece_scale`; it is
combined with this record below. -/
structure OuterFinalBounds
    (K n nW nD nZ dMinus dPlus : ℕ)
    (eta cW matchingCoeff boundaryCoeff aDisc lambdaCoeff sigmaCoeff
      RCoeff radiusCoeff : ℝ)
    (weightedStep radius : ℝ) : Prop where
  outer : OuterBounds K n eta cW matchingCoeff boundaryCoeff
  endpoint_loss :
    finalLambda lambdaCoeff n +
        (nZ : ℝ) * |(dPlus : ℝ) - dMinus| ≤
      aDisc * n * Real.sqrt n
  motion_boundary :
    (stride K eta n : ℝ) *
        (weightedStep + (nZ : ℝ) * (2 * K) + finalSigma sigmaCoeff n) +
      (nW / blockLength n : ℕ) *
        (weightedStep + (nZ : ℝ) * (spread n + 2 * K)) ≤
      finalLambda lambdaCoeff n
  packing_budget :
    8 * ((nW : ℝ) * (2 * Real.sqrt nD)) ≤
      (1 / 8 : ℝ) / 2 * (stride K eta n : ℝ) * finalSigma sigmaCoeff n
  radius_separation : 2 * radius < finalSeparation RCoeff n
  index_scale :
    finalIndexCoeff K eta RCoeff sigmaCoeff * Real.sqrt n ≤
      (1 / 8 : ℝ) /
        (2 * (⌈finalSeparation RCoeff n / finalSigma sigmaCoeff n⌉₊ + 2 : ℕ)) *
        (stride K eta n : ℝ)

/-- The raw-increment expectation fits the marked-packing budget. -/
lemma final_packing_budget
    {K n nW nD : ℕ} {eta cW c₀ sigmaCoeff : ℝ}
    (hcW : 0 ≤ cW) (hc₀ : 0 ≤ c₀) (hsigmaCoeff : 0 < sigmaCoeff)
    (H : RoundingBounds K n eta)
    (hnW : (nW : ℝ) ≤ cW * n)
    (hnD : (nD : ℝ) ≤ 2 * c₀ * n)
    (hpackingCoeff :
      512 * cW * Real.sqrt (2 * c₀) ≤
        smallStepCoeff K eta * sigmaCoeff) :
    8 * ((nW : ℝ) * (2 * Real.sqrt nD)) ≤
      (1 / 8 : ℝ) / 2 * (stride K eta n : ℝ) * finalSigma sigmaCoeff n := by
  have hcoeff : 16 * cW * Real.sqrt (2 * c₀) ≤
      smallStepCoeff K eta * sigmaCoeff / 32 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).2
    calc
      16 * cW * Real.sqrt (2 * c₀) * 32 =
          512 * cW * Real.sqrt (2 * c₀) := by ring
      _ ≤ smallStepCoeff K eta * sigmaCoeff := hpackingCoeff
  have hleft : 8 * ((nW : ℝ) * (2 * Real.sqrt nD)) ≤
      (smallStepCoeff K eta * sigmaCoeff / 32) * n * Real.sqrt n := by
    have hraw := rawVariation_le_packingBudget
      (A := 16) (cW := cW) (c₀ := c₀)
      (epsilon := smallStepCoeff K eta * sigmaCoeff / 32)
      (nW := nW) (nD := nD) (n := n)
      (by norm_num) hcW hc₀ hnW hnD hcoeff
    simpa only [show 8 * ((nW : ℝ) * (2 * Real.sqrt nD)) =
      16 * nW * Real.sqrt nD by ring] using hraw
  have hright :
      (smallStepCoeff K eta * sigmaCoeff / 32) * n * Real.sqrt n ≤
        (1 / 8 : ℝ) / 2 * (stride K eta n : ℝ) *
          finalSigma sigmaCoeff n := by
    dsimp only [finalSigma]
    calc
      (smallStepCoeff K eta * sigmaCoeff / 32) * n * Real.sqrt n =
          (1 / 16 : ℝ) *
            (smallStepCoeff K eta / 2 * Real.sqrt n) *
            (sigmaCoeff * n) := by ring
      _ ≤ (1 / 16 : ℝ) * (stride K eta n : ℝ) *
          (sigmaCoeff * n) := by
        have hmid : (1 / 16 : ℝ) *
            (smallStepCoeff K eta / 2 * Real.sqrt n) ≤
            (1 / 16 : ℝ) * (stride K eta n : ℝ) :=
          mul_le_mul_of_nonneg_left H.stride_lower (by norm_num)
        exact mul_le_mul_of_nonneg_right hmid (by positivity)
      _ = (1 / 8 : ℝ) / 2 * (stride K eta n : ℝ) *
          (sigmaCoeff * n) := by ring
  exact hleft.trans hright

/-- A window bounded by `radiusCoeff * nD` is strictly separated at the
linear ambient scale. -/
lemma final_radius_separation
    {n nD : ℕ} {c₀ RCoeff radiusCoeff radius : ℝ}
    (hn : 0 < n) (hradiusCoeff : 0 ≤ radiusCoeff)
    (hnD : (nD : ℝ) ≤ 2 * c₀ * n)
    (hradius : radius ≤ radiusCoeff * nD)
    (hsmall : 4 * radiusCoeff * c₀ < RCoeff) :
    2 * radius < finalSeparation RCoeff n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hradiusD : radius ≤ radiusCoeff * (2 * c₀ * n) :=
    hradius.trans (mul_le_mul_of_nonneg_left hnD hradiusCoeff)
  have hscaled : 4 * radiusCoeff * c₀ * (n : ℝ) < RCoeff * n :=
    mul_lt_mul_of_pos_right hsmall hnreal
  dsimp only [finalSeparation]
  linarith

/-- The rounded stride supplies exactly the marked-packing index coefficient;
the quotient `R / sigma` is independent of `n`. -/
lemma final_index_scale
    {K n : ℕ} {eta RCoeff sigmaCoeff : ℝ}
    (hsigmaCoeff : 0 < sigmaCoeff) (H : RoundingBounds K n eta) :
    finalIndexCoeff K eta RCoeff sigmaCoeff * Real.sqrt n ≤
      (1 / 8 : ℝ) /
        (2 * (⌈finalSeparation RCoeff n / finalSigma sigmaCoeff n⌉₊ + 2 : ℕ)) *
        (stride K eta n : ℝ) := by
  have hnreal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one H.order_pos)
  have hratio : finalSeparation RCoeff n / finalSigma sigmaCoeff n =
      RCoeff / sigmaCoeff := by
    dsimp only [finalSeparation, finalSigma]
    field_simp
  rw [hratio]
  dsimp only [finalIndexCoeff]
  have hden : (0 : ℝ) < ((⌈RCoeff / sigmaCoeff⌉₊ + 2 : ℕ) : ℝ) := by
    positivity
  calc
    smallStepCoeff K eta /
        (32 * (((⌈RCoeff / sigmaCoeff⌉₊ + 2 : ℕ) : ℝ))) * Real.sqrt n =
      ((1 / 8 : ℝ) / (2 * (((⌈RCoeff / sigmaCoeff⌉₊ + 2 : ℕ) : ℝ)))) *
        (smallStepCoeff K eta / 2 * Real.sqrt n) := by field_simp; ring
    _ ≤ ((1 / 8 : ℝ) /
        (2 * (((⌈RCoeff / sigmaCoeff⌉₊ + 2 : ℕ) : ℝ)))) *
        (stride K eta n : ℝ) := by
      exact mul_le_mul_of_nonneg_left H.stride_lower (by positivity)

/-- Pointwise construction of the five genuinely outer final bounds. -/
lemma outerFinalBounds_of_outerBounds
    {K n nW nD nZ dMinus dPlus : ℕ}
    {eta cW matchingCoeff boundaryCoeff c c₀ δZ aDisc lambdaCoeff
      sigmaCoeff RCoeff radiusCoeff weightedStep radius : ℝ}
    (hK : 0 < K) (heta : 0 < eta)
    (hcW : 0 ≤ cW) (hboundaryCoeff : 0 ≤ boundaryCoeff)
    (hc : 0 ≤ c) (hc₀ : 0 ≤ c₀) (hδZ : 0 ≤ δZ)
    (hsigmaCoeff : 0 < sigmaCoeff) (hRCoeff : 0 < RCoeff)
    (hradiusCoeff : 0 ≤ radiusCoeff)
    (hendpointCoeff :
      lambdaCoeff + δZ * K * cW * Real.sqrt (2 * c₀) ≤ aDisc)
    (hmotionCoeff :
      smallStepCoeff K eta *
          (cW + 4 * c + sigmaCoeff +
            2 * K * δZ * Real.sqrt (2 * c₀)) +
        (cW + 4 * c + δZ * Real.sqrt (2 * c₀)) * boundaryCoeff ≤
      lambdaCoeff)
    (hpackingCoeff :
      512 * cW * Real.sqrt (2 * c₀) ≤
        smallStepCoeff K eta * sigmaCoeff)
    (hradiusCoeffSmall : 4 * radiusCoeff * c₀ < RCoeff)
    (O : OuterBounds K n eta cW matchingCoeff boundaryCoeff)
    (hnW : (nW : ℝ) ≤ cW * n)
    (hnD : (nD : ℝ) ≤ 2 * c₀ * n)
    (hnZ : (nZ : ℝ) ≤ δZ * Real.sqrt nD)
    (hdegreeGap : |(dPlus : ℝ) - dMinus| ≤ K * nW)
    (hweightedStepNonneg : 0 ≤ weightedStep)
    (hweightedStep : weightedStep ≤ (cW + 4 * c) * n)
    (hradius : radius ≤ radiusCoeff * nD) :
    OuterFinalBounds K n nW nD nZ dMinus dPlus eta cW matchingCoeff
      boundaryCoeff aDisc lambdaCoeff sigmaCoeff RCoeff radiusCoeff
      weightedStep radius := by
  have hnreal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one O.rounding.order_pos)
  have hnreal1 : (1 : ℝ) ≤ n := by exact_mod_cast O.rounding.order_pos
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hsqrtNPos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnreal
  have hsqrtNSq : (Real.sqrt n) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnreal.le
  have hsqrtD : Real.sqrt nD ≤ Real.sqrt (2 * c₀ * (n : ℝ)) :=
    Real.sqrt_le_sqrt hnD
  have hsqrtProduct : Real.sqrt (2 * c₀ * (n : ℝ)) =
      Real.sqrt (2 * c₀) * Real.sqrt n := by
    exact Real.sqrt_mul (by positivity) _
  have hsqrtDBound : Real.sqrt nD ≤
      Real.sqrt (2 * c₀) * Real.sqrt n := by
    simpa only [hsqrtProduct] using hsqrtD
  have hnZBound : (nZ : ℝ) ≤
      δZ * Real.sqrt (2 * c₀) * Real.sqrt n := by
    calc
      (nZ : ℝ) ≤ δZ * Real.sqrt nD := hnZ
      _ ≤ δZ * (Real.sqrt (2 * c₀) * Real.sqrt n) := by gcongr
      _ = δZ * Real.sqrt (2 * c₀) * Real.sqrt n := by ring
  have hdegreeGap' : |(dPlus : ℝ) - dMinus| ≤ (K : ℝ) * (cW * n) := by
    calc
      |(dPlus : ℝ) - dMinus| ≤ (K : ℝ) * nW := hdegreeGap
      _ ≤ (K : ℝ) * (cW * n) := by gcongr
  have hgapTerm : (nZ : ℝ) * |(dPlus : ℝ) - dMinus| ≤
      (δZ * (K : ℝ) * cW * Real.sqrt (2 * c₀)) *
        (n : ℝ) * Real.sqrt n := by
    calc
      (nZ : ℝ) * |(dPlus : ℝ) - dMinus| ≤
          (δZ * Real.sqrt (2 * c₀) * Real.sqrt n) *
            ((K : ℝ) * (cW * n)) := by
              exact mul_le_mul hnZBound hdegreeGap' (abs_nonneg _) (by positivity)
      _ = (δZ * (K : ℝ) * cW * Real.sqrt (2 * c₀)) *
          (n : ℝ) * Real.sqrt n := by ring
  have hendpoint :
      finalLambda lambdaCoeff n +
          (nZ : ℝ) * |(dPlus : ℝ) - dMinus| ≤
        aDisc * n * Real.sqrt n := by
    dsimp only [finalLambda]
    calc
      lambdaCoeff * (n : ℝ) * Real.sqrt n +
          (nZ : ℝ) * |(dPlus : ℝ) - dMinus| ≤
        (lambdaCoeff + δZ * K * cW * Real.sqrt (2 * c₀)) *
          (n : ℝ) * Real.sqrt n := by
            nlinarith [hgapTerm]
      _ ≤ aDisc * (n : ℝ) * Real.sqrt n := by gcongr
  have hsqrt_le_n : Real.sqrt n ≤ (n : ℝ) :=
    AsymptoticThresholds.sqrt_nat_le_nat O.rounding.order_pos
  let regularCoeff : ℝ := cW + 4 * c + sigmaCoeff +
    2 * K * δZ * Real.sqrt (2 * c₀)
  have hregular :
      weightedStep + (nZ : ℝ) * (2 * K) + finalSigma sigmaCoeff n ≤
        regularCoeff * n := by
    have hnZstep : (nZ : ℝ) * (2 * K) ≤
        (2 * K * δZ * Real.sqrt (2 * c₀)) * n := by
      calc
        (nZ : ℝ) * (2 * K) ≤
            (δZ * Real.sqrt (2 * c₀) * Real.sqrt n) * (2 * K) := by gcongr
        _ ≤ (δZ * Real.sqrt (2 * c₀) * n) * (2 * K) := by gcongr
        _ = (2 * K * δZ * Real.sqrt (2 * c₀)) * n := by ring
    dsimp only [finalSigma, regularCoeff]
    nlinarith [hweightedStep, hnZstep]
  have hregularTotal :
      (stride K eta n : ℝ) *
          (weightedStep + (nZ : ℝ) * (2 * K) + finalSigma sigmaCoeff n) ≤
        (smallStepCoeff K eta * regularCoeff) * n * Real.sqrt n := by
    have hinsideNonneg : 0 ≤
        weightedStep + (nZ : ℝ) * (2 * K) + finalSigma sigmaCoeff n := by
      dsimp only [finalSigma]
      positivity
    have hregNonneg : 0 ≤ regularCoeff * (n : ℝ) := by
      dsimp only [regularCoeff]
      positivity
    calc
      (stride K eta n : ℝ) *
          (weightedStep + (nZ : ℝ) * (2 * K) + finalSigma sigmaCoeff n) ≤
        (stride K eta n : ℝ) * (regularCoeff * n) := by
          exact mul_le_mul_of_nonneg_left hregular (by positivity)
      _ ≤ (smallStepCoeff K eta * Real.sqrt n) * (regularCoeff * n) := by
        exact mul_le_mul_of_nonneg_right O.rounding.stride_upper hregNonneg
      _ = (smallStepCoeff K eta * regularCoeff) * n * Real.sqrt n := by ring
  have hsqrt_le_outerError : Real.sqrt n ≤ outerError n := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hnreal1 (by norm_num)
  have houterError_le_spread : outerError n ≤ (spread n : ℝ) := by
    dsimp only [spread]
    have hceil := Nat.le_ceil (2 * outerError n)
    linarith [show 0 ≤ outerError n by dsimp [outerError]; positivity]
  have hsqrt_le_spread : Real.sqrt n ≤ (spread n : ℝ) :=
    hsqrt_le_outerError.trans houterError_le_spread
  have hn_le_spanSqrt : (n : ℝ) ≤
      ((spread n + 2 * K + 1 : ℕ) : ℝ) * Real.sqrt n := by
    push_cast
    calc
      (n : ℝ) = Real.sqrt n * Real.sqrt n := by
        rw [← pow_two, hsqrtNSq]
      _ ≤ (spread n : ℝ) * Real.sqrt n := by gcongr
      _ ≤ ((spread n : ℝ) + 2 * K + 1) * Real.sqrt n := by
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  let boundaryMultiplier : ℝ := cW + 4 * c +
    δZ * Real.sqrt (2 * c₀)
  have hboundaryInside :
      weightedStep + (nZ : ℝ) * (spread n + 2 * K) ≤
        boundaryMultiplier *
          ((spread n + 2 * K + 1 : ℕ) : ℝ) * Real.sqrt n := by
    have hweightedBoundary : weightedStep ≤
        (cW + 4 * c) *
          ((spread n + 2 * K + 1 : ℕ) : ℝ) * Real.sqrt n := by
      calc
        weightedStep ≤ (cW + 4 * c) * n := hweightedStep
        _ ≤ (cW + 4 * c) *
            (((spread n + 2 * K + 1 : ℕ) : ℝ) * Real.sqrt n) := by gcongr
        _ = (cW + 4 * c) *
            ((spread n + 2 * K + 1 : ℕ) : ℝ) * Real.sqrt n := by ring
    have hnZBoundary : (nZ : ℝ) * (spread n + 2 * K) ≤
        (δZ * Real.sqrt (2 * c₀)) *
          ((spread n + 2 * K + 1 : ℕ) : ℝ) * Real.sqrt n := by
      push_cast
      have hplus : (spread n : ℝ) + 2 * K ≤
          (spread n : ℝ) + 2 * K + 1 := by linarith
      calc
        (nZ : ℝ) * ((spread n : ℝ) + 2 * K) ≤
          (δZ * Real.sqrt (2 * c₀) * Real.sqrt n) *
            ((spread n : ℝ) + 2 * K + 1) := by
              exact mul_le_mul hnZBound hplus (by positivity) (by positivity)
        _ = (δZ * Real.sqrt (2 * c₀)) *
            ((spread n : ℝ) + 2 * K + 1) * Real.sqrt n := by ring
    dsimp only [boundaryMultiplier]
    calc
      weightedStep + (nZ : ℝ) * (spread n + 2 * K) ≤
          (cW + 4 * c) *
              ((spread n + 2 * K + 1 : ℕ) : ℝ) * Real.sqrt n +
            (δZ * Real.sqrt (2 * c₀)) *
              ((spread n + 2 * K + 1 : ℕ) : ℝ) * Real.sqrt n :=
        add_le_add hweightedBoundary hnZBoundary
      _ = (cW + 4 * c + δZ * Real.sqrt (2 * c₀)) *
          ((spread n + 2 * K + 1 : ℕ) : ℝ) * Real.sqrt n := by ring
  have hboundaryCore := O.boundary_budget nW hnW
  have hboundaryTotal :
      ((nW / blockLength n : ℕ) : ℝ) *
          (weightedStep + (nZ : ℝ) * (spread n + 2 * K)) ≤
        (boundaryMultiplier * boundaryCoeff) * n * Real.sqrt n := by
    have hqnonneg : (0 : ℝ) ≤ (nW / blockLength n : ℕ) := by positivity
    calc
      ((nW / blockLength n : ℕ) : ℝ) *
          (weightedStep + (nZ : ℝ) * (spread n + 2 * K)) ≤
        ((nW / blockLength n : ℕ) : ℝ) *
          (boundaryMultiplier *
            ((spread n + 2 * K + 1 : ℕ) : ℝ) * Real.sqrt n) := by gcongr
      _ = boundaryMultiplier *
          ((((nW / blockLength n) * (spread n + 2 * K + 1) : ℕ) : ℝ) *
            Real.sqrt n) := by push_cast; ring
      _ ≤ boundaryMultiplier * (boundaryCoeff * n * Real.sqrt n) := by
        exact mul_le_mul_of_nonneg_left hboundaryCore.le (by
          dsimp [boundaryMultiplier]
          positivity)
      _ = (boundaryMultiplier * boundaryCoeff) * n * Real.sqrt n := by ring
  have hmotion :
      (stride K eta n : ℝ) *
          (weightedStep + (nZ : ℝ) * (2 * K) + finalSigma sigmaCoeff n) +
        (nW / blockLength n : ℕ) *
          (weightedStep + (nZ : ℝ) * (spread n + 2 * K)) ≤
        finalLambda lambdaCoeff n := by
    dsimp only [finalLambda]
    calc
      (stride K eta n : ℝ) *
          (weightedStep + (nZ : ℝ) * (2 * K) + finalSigma sigmaCoeff n) +
        ((nW / blockLength n : ℕ) : ℝ) *
          (weightedStep + (nZ : ℝ) * (spread n + 2 * K)) ≤
        ((smallStepCoeff K eta * regularCoeff) +
          boundaryMultiplier * boundaryCoeff) * n * Real.sqrt n := by
          calc
            (stride K eta n : ℝ) *
                (weightedStep + (nZ : ℝ) * (2 * K) +
                  finalSigma sigmaCoeff n) +
              ((nW / blockLength n : ℕ) : ℝ) *
                (weightedStep + (nZ : ℝ) * (spread n + 2 * K)) ≤
              (smallStepCoeff K eta * regularCoeff) * n * Real.sqrt n +
                (boundaryMultiplier * boundaryCoeff) * n * Real.sqrt n :=
              add_le_add hregularTotal hboundaryTotal
            _ = ((smallStepCoeff K eta * regularCoeff) +
                boundaryMultiplier * boundaryCoeff) * n * Real.sqrt n := by ring
      _ ≤ lambdaCoeff * n * Real.sqrt n := by
        dsimp only [regularCoeff, boundaryMultiplier] at hmotionCoeff ⊢
        gcongr
  have hpacking :
      8 * ((nW : ℝ) * (2 * Real.sqrt nD)) ≤
        (1 / 8 : ℝ) / 2 * (stride K eta n : ℝ) * finalSigma sigmaCoeff n := by
    exact final_packing_budget hcW hc₀ hsigmaCoeff O.rounding
      hnW hnD hpackingCoeff
  have hradiusSep : 2 * radius < finalSeparation RCoeff n := by
    exact final_radius_separation
      (lt_of_lt_of_le Nat.zero_lt_one O.rounding.order_pos)
      hradiusCoeff hnD hradius hradiusCoeffSmall
  have hindex :
      finalIndexCoeff K eta RCoeff sigmaCoeff * Real.sqrt n ≤
        (1 / 8 : ℝ) /
          (2 * (⌈finalSeparation RCoeff n / finalSigma sigmaCoeff n⌉₊ + 2 : ℕ)) *
          (stride K eta n : ℝ) := by
    exact final_index_scale hsigmaCoeff O.rounding
  exact {
    outer := O
    endpoint_loss := hendpoint
    motion_boundary := hmotion
    packing_budget := hpacking
    radius_separation := hradiusSep
    index_scale := hindex }

/-- One threshold supplies conclusions (i)--(iv) and (vi), uniformly over
all rounded graph parameters satisfying their coarse ambient bounds. -/
theorem exists_outerFinalBounds
    {K : ℕ} (hK : 0 < K)
    {eta cW matchingCoeff boundaryCoeff c c₀ δZ aDisc lambdaCoeff
      sigmaCoeff RCoeff radiusCoeff : ℝ}
    (heta : 0 < eta) (hcW : 0 < cW)
    (hmatchingCoeff : 0 < matchingCoeff)
    (hboundaryCoeff : 0 < boundaryCoeff)
    (hc : 0 ≤ c) (hc₀ : 0 ≤ c₀) (hδZ : 0 ≤ δZ)
    (hsigmaCoeff : 0 < sigmaCoeff) (hRCoeff : 0 < RCoeff)
    (hradiusCoeff : 0 ≤ radiusCoeff)
    (hendpointCoeff :
      lambdaCoeff + δZ * K * cW * Real.sqrt (2 * c₀) ≤ aDisc)
    (hmotionCoeff :
      smallStepCoeff K eta *
          (cW + 4 * c + sigmaCoeff +
            2 * K * δZ * Real.sqrt (2 * c₀)) +
        (cW + 4 * c + δZ * Real.sqrt (2 * c₀)) * boundaryCoeff ≤
      lambdaCoeff)
    (hpackingCoeff :
      512 * cW * Real.sqrt (2 * c₀) ≤
        smallStepCoeff K eta * sigmaCoeff)
    (hradiusCoeffSmall : 4 * radiusCoeff * c₀ < RCoeff) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∀ nW nD nZ dMinus dPlus : ℕ, ∀ weightedStep radius : ℝ,
      (nW : ℝ) ≤ cW * n →
      (nD : ℝ) ≤ 2 * c₀ * n →
      (nZ : ℝ) ≤ δZ * Real.sqrt nD →
      |(dPlus : ℝ) - dMinus| ≤ K * nW →
      0 ≤ weightedStep → weightedStep ≤ (cW + 4 * c) * n →
      radius ≤ radiusCoeff * nD →
      OuterFinalBounds K n nW nD nZ dMinus dPlus eta cW matchingCoeff
        boundaryCoeff aDisc lambdaCoeff sigmaCoeff RCoeff radiusCoeff
        weightedStep radius := by
  obtain ⟨N, hN⟩ := exists_outerBounds hK heta hcW
    hmatchingCoeff hboundaryCoeff
  refine ⟨N, ?_⟩
  intro n hn nW nD nZ dMinus dPlus weightedStep radius
    hnW hnD hnZ hgap hstep0 hstep hradius
  exact outerFinalBounds_of_outerBounds hK heta hcW.le hboundaryCoeff.le
    hc hc₀ hδZ hsigmaCoeff hRCoeff hradiusCoeff hendpointCoeff
    hmotionCoeff hpackingCoeff hradiusCoeffSmall (hN n hn)
    hnW hnD hnZ hgap hstep0 hstep hradius

/-- All six final inequalities, adding the branch-derived piece scale to the
five outer conclusions. -/
structure FinalNumericBounds
    (K n nW nD nZ dMinus dPlus : ℕ)
    (eta cW matchingCoeff boundaryCoeff aDisc lambdaCoeff sigmaCoeff
      RCoeff radiusCoeff weightedStep radius a₂ δ₀ c₀ L : ℝ) : Prop where
  outer : OuterFinalBounds K n nW nD nZ dMinus dPlus eta cW
    matchingCoeff boundaryCoeff aDisc lambdaCoeff sigmaCoeff RCoeff
    radiusCoeff weightedStep radius
  piece_scale : finalPieceCoeff K a₂ δ₀ c₀ * n ≤ L

/-- Attach conclusion (v) from `BranchBounds` to the final outer record. -/
lemma finalNumericBounds_of_branchBounds
    {c c₀ δ₀ δZ : ℝ} {K n ell k nW nD nZ dMinus dPlus : ℕ}
    {branch : Bool}
    {eta cW matchingCoeff boundaryCoeff aDisc lambdaCoeff sigmaCoeff
      RCoeff radiusCoeff weightedStep radius a₂ L : ℝ}
    (F : OuterFinalBounds K n nW nD nZ dMinus dPlus eta cW
      matchingCoeff boundaryCoeff aDisc lambdaCoeff sigmaCoeff RCoeff
      radiusCoeff weightedStep radius)
    (B : BranchBounds c c₀ δ₀ δZ K n ell k branch)
    (hnD : nD = RoundedParameters.branchScale branch
      (OuterAssembly.deletionSize c₀ n))
    (hnZ : nZ = OuterAssembly.augmentationSize δ₀
      (OuterAssembly.deletionSize c₀ n) k)
    (ha₂ : 0 ≤ a₂)
    (hL : a₂ * (nZ : ℝ) * Real.sqrt nD ≤ L) :
    FinalNumericBounds K n nW nD nZ dMinus dPlus eta cW
      matchingCoeff boundaryCoeff aDisc lambdaCoeff sigmaCoeff RCoeff
      radiusCoeff weightedStep radius a₂ δ₀ c₀ L := by
  refine ⟨F, ?_⟩
  dsimp only [finalPieceCoeff]
  apply B.piece_scale ha₂
  simpa only [hnD, hnZ] using hL

/-- A single eventual theorem covering all six explicit numeric obligations.
The branch identities are conclusions of the structural/rounding assembly;
the remaining hypotheses are precisely its coarse degree and motion bounds. -/
theorem exists_finalNumericBounds
    {K : ℕ} (hK : 0 < K)
    {c c₀ δ₀ δZ eta cW matchingCoeff boundaryCoeff aDisc lambdaCoeff
      sigmaCoeff RCoeff radiusCoeff : ℝ}
    (hc : 0 < c) (hc₀ : 0 < c₀) (hsmall : 6 * c₀ ≤ c)
    (hδ₀ : 0 < δ₀) (hδZdom : δ₀ ≤ δZ)
    (heta : 0 < eta) (hcW : 0 < cW)
    (hmatchingCoeff : 0 < matchingCoeff)
    (hboundaryCoeff : 0 < boundaryCoeff)
    (hsigmaCoeff : 0 < sigmaCoeff) (hRCoeff : 0 < RCoeff)
    (hradiusCoeff : 0 ≤ radiusCoeff)
    (hendpointCoeff :
      lambdaCoeff + δZ * K * cW * Real.sqrt (2 * c₀) ≤ aDisc)
    (hmotionCoeff :
      smallStepCoeff K eta *
          (cW + 4 * c + sigmaCoeff +
            2 * K * δZ * Real.sqrt (2 * c₀)) +
        (cW + 4 * c + δZ * Real.sqrt (2 * c₀)) * boundaryCoeff ≤
      lambdaCoeff)
    (hpackingCoeff :
      512 * cW * Real.sqrt (2 * c₀) ≤
        smallStepCoeff K eta * sigmaCoeff)
    (hradiusCoeffSmall : 4 * radiusCoeff * c₀ < RCoeff) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ell,
      ell ∈ RoundedParameters.outerParameterInterval c n →
      ∀ branch k, 1 ≤ k → k ≤ K →
      ∀ nW dMinus dPlus : ℕ, ∀ weightedStep radius a₂ L : ℝ,
      (nW : ℝ) ≤ cW * n →
      |(dPlus : ℝ) - dMinus| ≤ K * nW →
      0 ≤ weightedStep → weightedStep ≤ (cW + 4 * c) * n →
      radius ≤ radiusCoeff *
        RoundedParameters.branchScale branch
          (OuterAssembly.deletionSize c₀ n) →
      0 ≤ a₂ →
      a₂ * (OuterAssembly.augmentationSize δ₀
          (OuterAssembly.deletionSize c₀ n) k : ℝ) *
          Real.sqrt (RoundedParameters.branchScale branch
            (OuterAssembly.deletionSize c₀ n)) ≤ L →
      FinalNumericBounds K n nW
        (RoundedParameters.branchScale branch
          (OuterAssembly.deletionSize c₀ n))
        (OuterAssembly.augmentationSize δ₀
          (OuterAssembly.deletionSize c₀ n) k)
        dMinus dPlus eta cW matchingCoeff boundaryCoeff aDisc lambdaCoeff
        sigmaCoeff RCoeff radiusCoeff weightedStep radius a₂ δ₀ c₀ L := by
  obtain ⟨Nouter, houter⟩ := exists_outerFinalBounds hK heta hcW
    hmatchingCoeff hboundaryCoeff hc.le hc₀.le (hδ₀.le.trans hδZdom)
      hsigmaCoeff hRCoeff hradiusCoeff hendpointCoeff hmotionCoeff
      hpackingCoeff hradiusCoeffSmall
  obtain ⟨Nbranch, hbranch⟩ := exists_branchBounds hc hc₀ hsmall
    hδ₀ hδZdom hK
  refine ⟨max Nouter Nbranch, ?_⟩
  intro n hn ell hell branch k hk1 hkK nW dMinus dPlus weightedStep radius a₂ L
    hnW hgap hstep0 hstep hradius ha₂ hL
  have hNo : Nouter ≤ n := (le_max_left _ _).trans hn
  have hNb : Nbranch ≤ n := (le_max_right _ _).trans hn
  let nD : ℕ := RoundedParameters.branchScale branch
    (OuterAssembly.deletionSize c₀ n)
  let nZ : ℕ := OuterAssembly.augmentationSize δ₀
    (OuterAssembly.deletionSize c₀ n) k
  have B := hbranch n hNb ell hell branch k hk1 hkK
  have F := houter n hNo nW nD nZ dMinus dPlus weightedStep radius
    hnW B.order_upper B.augmentation_upper
    hgap hstep0 hstep (by simpa only [nD] using hradius)
  exact finalNumericBounds_of_branchBounds F B rfl rfl ha₂
    (by simpa only [nD, nZ] using hL)

/-! ## Generalized partial-exposure thresholds

The graph partial-exposure theorem deliberately permits three independent
exception thresholds.  The large-exposure branch needs half of the first
matching to survive the two degree filters, while its collision graph may
have a separately chosen square-root number of edges.  The definitions below
are the literal parameters passed to that theorem and to the subsequent
Turán selector. -/

/-- Each degree-bad family is allowed to consume half of the first matching. -/
def partialDegreeThreshold (a₀ : ℝ) (nD : ℕ) : ℝ :=
  (partialMatchingSize a₀ nD : ℝ) / 2

/-- Collision threshold in the partial exposure. -/
def partialCollisionThreshold (LH : ℝ) (nD : ℕ) : ℝ :=
  LH * Real.sqrt nD

/-- Integer degree-exception budget used by the deterministic selector. -/
def partialBadBudget (a₀ : ℝ) (nD : ℕ) : ℕ :=
  partialMatchingSize a₀ nD / 2

/-- Integer collision-edge budget used by the deterministic selector. -/
def partialSelectionEdgeBudget (LH : ℝ) (nD : ℕ) : ℕ :=
  ⌊LH * Real.sqrt nD⌋₊

/-- Integer gap between successive selected cells. -/
def partialSelectionGap (gapCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊gapCoeff * Real.sqrt nD⌋₊

/-- The exact four-term probability budget and all threshold-rounding facts
needed to instantiate `PartialExposureCertificate`. -/
structure PartialExposureRiskBounds
    (K nD m : ℕ) (a₀ theta Q C LH : ℝ) : Prop where
  matching_pos : 0 < partialMatchingSize a₀ nD
  matching_lower :
    a₀ / 8 * Real.sqrt nD ≤ (partialMatchingSize a₀ nD : ℝ)
  degreeThreshold_pos : 0 < partialDegreeThreshold a₀ nD
  degreeThreshold_le_badBudget :
    partialDegreeThreshold a₀ nD ≤ (partialBadBudget a₀ nD : ℝ) + 1
  collisionThreshold_pos : 0 < partialCollisionThreshold LH nD
  collisionThreshold_le_edgeBudget :
    partialCollisionThreshold LH nD ≤
      (partialSelectionEdgeBudget LH nD : ℝ) + 1
  risk_budget :
    let s₀ := partialMatchingSize a₀ nD
    let pDiv := AugmentationGraphPartial.outerLinearFailure nD K (theta * nD)
    let pDegree := AugmentationGraphPartial.outerLinearFailure nD K
      (Q * Real.sqrt nD)
    let pCollision := C / Real.sqrt m
    (s₀.choose 2 : ℝ) * pDiv +
        s₀ * pDegree / partialDegreeThreshold a₀ nD +
        s₀ * pDegree / partialDegreeThreshold a₀ nD +
        (s₀.choose 2 : ℝ) * pCollision /
          partialCollisionThreshold LH nD ≤ 1 / 4

/-- Eventual generalized partial-exposure budget.  Unlike the earlier
square-root-threshold package, the degree denominators here are exactly
`s₀ / 2`, while the collision denominator is `LH * sqrt nD`. -/
theorem exists_partialExposureRiskBounds
    {K : ℕ} {a₀ theta Q C LH : ℝ}
    (hK : 0 < K) (ha₀ : 0 < a₀) (htheta : 0 < theta)
    (hQ : 0 < Q) (hC : 0 ≤ C) (hLH : 0 < LH)
    (hsmall :
      8 * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2))) +
          a₀ ^ 2 * C / (16 * LH) ≤ 3 / 16) :
    ∃ N : ℕ, ∀ nD ≥ N, ∀ m : ℕ, 2 * nD ≤ m →
      PartialExposureRiskBounds K nD m a₀ theta Q C LH := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  let b : ℝ := theta ^ 2 / (64 * (K : ℝ) ^ 2)
  have hb : 0 < b := by dsimp [b]; positivity
  let Adiv : ℝ := a₀ ^ 2 / 8
  have hAdiv : 0 ≤ Adiv := by dsimp [Adiv]; positivity
  obtain ⟨Ndiv, hNdiv⟩ :=
    exists_polynomial_mul_exp_neg_lt Adiv b 1 hAdiv hb (1 / 16) (by norm_num)
  obtain ⟨Nmatching, hNmatching⟩ :=
    exists_eighth_mul_sqrt_le_quarter_floor a₀ ha₀
  refine ⟨max 1 (max Ndiv Nmatching), ?_⟩
  intro nD hnD m hm
  have hnD1 : 1 ≤ nD := (le_max_left _ _).trans hnD
  have htail : max Ndiv Nmatching ≤ nD := (le_max_right _ _).trans hnD
  have hNdiv' : Ndiv ≤ nD := (le_max_left _ _).trans htail
  have hNmatching' : Nmatching ≤ nD := (le_max_right _ _).trans htail
  have hnDreal : (0 : ℝ) < nD := by exact_mod_cast (Nat.zero_lt_one.trans_le hnD1)
  have hm1 : 1 ≤ m := by omega
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_one.trans_le hm1)
  have hsqrtDPos : 0 < Real.sqrt nD := Real.sqrt_pos.2 hnDreal
  have hsqrtMPos : 0 < Real.sqrt m := Real.sqrt_pos.2 hmreal
  have hsqrtDSq : (Real.sqrt nD) ^ 2 = (nD : ℝ) :=
    Real.sq_sqrt hnDreal.le
  let s₀ : ℕ := partialMatchingSize a₀ nD
  have hs₀Lower : a₀ / 8 * Real.sqrt nD ≤ (s₀ : ℝ) := by
    simpa only [s₀, partialMatchingSize_eq] using hNmatching nD hNmatching'
  have hs₀posReal : (0 : ℝ) < s₀ :=
    lt_of_lt_of_le (mul_pos (by positivity) hsqrtDPos) hs₀Lower
  have hs₀pos : 0 < s₀ := by exact_mod_cast hs₀posReal
  have hs₀Upper : (s₀ : ℝ) ≤ a₀ / 4 * Real.sqrt nD := by
    dsimp only [s₀, partialMatchingSize]
    have hfloor := Nat.floor_le
      (show 0 ≤ a₀ * Real.sqrt nD / 4 by positivity)
    nlinarith
  have hs₀nonneg : (0 : ℝ) ≤ s₀ := by positivity
  have hs₀sq : (s₀ : ℝ) ^ 2 ≤ a₀ ^ 2 / 16 * nD := by
    have hsquare := mul_self_le_mul_self hs₀nonneg hs₀Upper
    calc
      (s₀ : ℝ) ^ 2 ≤ (a₀ / 4 * Real.sqrt nD) ^ 2 := by
        simpa only [pow_two] using hsquare
      _ = a₀ ^ 2 / 16 * nD := by rw [mul_pow, hsqrtDSq]; ring
  have hchoose : (s₀.choose 2 : ℝ) ≤ (s₀ : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_le_pow s₀ 2
  have hpDiv : AugmentationGraphPartial.outerLinearFailure nD K (theta * nD) =
      2 * Real.exp (-b * nD) := by
    simp only [AugmentationGraphPartial.outerLinearFailure]
    congr 2
    congr 1
    dsimp [b]
    field_simp
    ring
  have hpDegree : AugmentationGraphPartial.outerLinearFailure nD K
      (Q * Real.sqrt nD) =
      2 * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2))) := by
    simp only [AugmentationGraphPartial.outerLinearFailure]
    congr 2
    congr 1
    rw [show (Q * Real.sqrt nD) ^ 2 = Q ^ 2 * nD by
      rw [mul_pow, hsqrtDSq]]
    field_simp
    ring
  have hdivTerm : (s₀.choose 2 : ℝ) *
      AugmentationGraphPartial.outerLinearFailure nD K (theta * nD) ≤
        1 / 16 := by
    rw [hpDiv]
    have hdecay : 0 ≤ Real.exp (-b * nD) := (Real.exp_pos _).le
    calc
      (s₀.choose 2 : ℝ) * (2 * Real.exp (-b * nD)) ≤
          (a₀ ^ 2 / 16 * nD) * (2 * Real.exp (-b * nD)) := by
            exact mul_le_mul_of_nonneg_right (hchoose.trans hs₀sq)
              (mul_nonneg (by norm_num) hdecay)
      _ = Adiv * (nD : ℝ) ^ 1 * Real.exp (-b * nD) := by
            dsimp [Adiv]
            ring
      _ ≤ 1 / 16 := (hNdiv nD hNdiv').le
  have htDegree : partialDegreeThreshold a₀ nD = (s₀ : ℝ) / 2 := by
    simp only [partialDegreeThreshold, s₀]
  have htDegreePos : 0 < partialDegreeThreshold a₀ nD := by
    rw [htDegree]
    positivity
  have hdegreeTerms :
      (s₀ : ℝ) * AugmentationGraphPartial.outerLinearFailure nD K
            (Q * Real.sqrt nD) / partialDegreeThreshold a₀ nD +
          (s₀ : ℝ) * AugmentationGraphPartial.outerLinearFailure nD K
            (Q * Real.sqrt nD) / partialDegreeThreshold a₀ nD =
        8 * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2))) := by
    rw [hpDegree, htDegree]
    field_simp
    ring
  have hsqrtMono : Real.sqrt nD ≤ Real.sqrt m := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show nD ≤ m by omega)
  have hden : (nD : ℝ) ≤ Real.sqrt m * Real.sqrt nD := by
    calc
      (nD : ℝ) = Real.sqrt nD * Real.sqrt nD := by
        rw [← pow_two, hsqrtDSq]
      _ ≤ Real.sqrt m * Real.sqrt nD := by gcongr
  have htCollision : partialCollisionThreshold LH nD = LH * Real.sqrt nD := rfl
  have htCollisionPos : 0 < partialCollisionThreshold LH nD := by
    rw [htCollision]
    positivity
  have hcollisionTerm :
      (s₀.choose 2 : ℝ) * (C / Real.sqrt m) /
          partialCollisionThreshold LH nD ≤ a₀ ^ 2 * C / (16 * LH) := by
    have hdenPos : 0 < LH * (Real.sqrt m * Real.sqrt nD) := by positivity
    calc
      (s₀.choose 2 : ℝ) * (C / Real.sqrt m) /
          partialCollisionThreshold LH nD =
          ((s₀.choose 2 : ℝ) * C) /
            (LH * (Real.sqrt m * Real.sqrt nD)) := by
              rw [htCollision]
              field_simp
      _ ≤ ((a₀ ^ 2 / 16 * nD) * C) /
            (LH * (Real.sqrt m * Real.sqrt nD)) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hchoose.trans hs₀sq) hC) hdenPos.le
      _ ≤ a₀ ^ 2 * C / (16 * LH) := by
        rw [div_le_iff₀ hdenPos]
        have hscaled := mul_le_mul_of_nonneg_left hden
          (show 0 ≤ a₀ ^ 2 * C / 16 by positivity)
        field_simp
        nlinarith
  have htDegreeBudget : partialDegreeThreshold a₀ nD ≤
      (partialBadBudget a₀ nD : ℝ) + 1 := by
    rw [htDegree]
    have hnat : s₀ < 2 * (s₀ / 2 + 1) := by omega
    have hreal : (s₀ : ℝ) < 2 * ((s₀ / 2 : ℕ) + 1) := by
      exact_mod_cast hnat
    dsimp only [partialBadBudget, s₀]
    push_cast
    linarith
  have htCollisionBudget : partialCollisionThreshold LH nD ≤
      (partialSelectionEdgeBudget LH nD : ℝ) + 1 := by
    have hfloor := Nat.lt_floor_add_one (LH * Real.sqrt nD)
    dsimp only [partialCollisionThreshold, partialSelectionEdgeBudget]
    linarith
  refine {
    matching_pos := by simpa only [s₀] using hs₀pos
    matching_lower := by simpa only [s₀] using hs₀Lower
    degreeThreshold_pos := htDegreePos
    degreeThreshold_le_badBudget := htDegreeBudget
    collisionThreshold_pos := htCollisionPos
    collisionThreshold_le_edgeBudget := htCollisionBudget
    risk_budget := ?_ }
  dsimp only
  change (s₀.choose 2 : ℝ) *
      AugmentationGraphPartial.outerLinearFailure nD K (theta * nD) +
      (s₀ : ℝ) * AugmentationGraphPartial.outerLinearFailure nD K
          (Q * Real.sqrt nD) / partialDegreeThreshold a₀ nD +
      (s₀ : ℝ) * AugmentationGraphPartial.outerLinearFailure nD K
          (Q * Real.sqrt nD) / partialDegreeThreshold a₀ nD +
      (s₀.choose 2 : ℝ) * (C / Real.sqrt m) /
          partialCollisionThreshold LH nD ≤ 1 / 4
  linarith [hdivTerm, hdegreeTerms, hcollisionTerm, hsmall]

/-- The deterministic Turán inequality at the literal partial-exposure
budgets.  The harmless additive `1` in the first factor is absorbed by one
extra `deltaZ * sqrt nD`; this is why the coefficient is `3 * deltaZ` rather
than `2 * deltaZ`. -/
lemma partialExposure_selectionTuran
    {K nD m nZ nS : ℕ} {a₀ theta Q C LH δZ gapCoeff : ℝ}
    (ha₀ : 0 < a₀) (hLH : 0 < LH) (hδZ : 0 < δZ)
    (hgapCoeff : 0 ≤ gapCoeff)
    (hcoeff :
      (3 * δZ + gapCoeff) * (a₀ / 4 + 2 * LH) < (a₀ / 16) ^ 2)
    (H : PartialExposureRiskBounds K nD m a₀ theta Q C LH)
    (hnS : nS + 1 = nZ)
    (hnZ : (nZ : ℝ) ≤ δZ * Real.sqrt nD)
    (hone : 1 ≤ δZ * Real.sqrt nD) :
    (2 * nS + partialSelectionGap gapCoeff nD + 1) *
        (partialMatchingSize a₀ nD - partialBadBudget a₀ nD +
          2 * partialSelectionEdgeBudget LH nD) <
      (partialMatchingSize a₀ nD - partialBadBudget a₀ nD) ^ 2 := by
  let s₀ : ℕ := partialMatchingSize a₀ nD
  let bad : ℕ := partialBadBudget a₀ nD
  let edge : ℕ := partialSelectionEdgeBudget LH nD
  let gap : ℕ := partialSelectionGap gapCoeff nD
  have hnDpos : 0 < nD := by
    by_contra hzero
    have hnDzero : nD = 0 := Nat.eq_zero_of_not_pos hzero
    norm_num [hnDzero] at hone
  have hnDreal : (0 : ℝ) < nD := by exact_mod_cast hnDpos
  have hsqrtDPos : 0 < Real.sqrt nD := Real.sqrt_pos.2 hnDreal
  have hsqrtDSq : (Real.sqrt nD) ^ 2 = (nD : ℝ) :=
    Real.sq_sqrt hnDreal.le
  have hs₀Upper : (s₀ : ℝ) ≤ a₀ / 4 * Real.sqrt nD := by
    dsimp only [s₀, partialMatchingSize]
    have hfloor := Nat.floor_le
      (show 0 ≤ a₀ * Real.sqrt nD / 4 by positivity)
    nlinarith
  have hbadEq : bad = s₀ / 2 := by
    simp only [bad, partialBadBudget, s₀]
  have hsurvivorNat : s₀ ≤ 2 * (s₀ - bad) := by
    rw [hbadEq]
    omega
  have hsurvivorCast : (s₀ : ℝ) ≤ 2 * (s₀ - bad : ℕ) := by
    exact_mod_cast hsurvivorNat
  have hsurvivorLower : a₀ / 16 * Real.sqrt nD ≤
      (s₀ - bad : ℕ) := by
    have hsLower : a₀ / 8 * Real.sqrt nD ≤ (s₀ : ℝ) := by
      simpa only [s₀] using H.matching_lower
    push_cast at hsurvivorCast ⊢
    nlinarith
  have hsurvivorUpper : ((s₀ - bad : ℕ) : ℝ) ≤
      a₀ / 4 * Real.sqrt nD := by
    calc
      ((s₀ - bad : ℕ) : ℝ) ≤ (s₀ : ℝ) := by
        exact_mod_cast Nat.sub_le s₀ bad
      _ ≤ a₀ / 4 * Real.sqrt nD := hs₀Upper
  have hedgeUpper : (edge : ℝ) ≤ LH * Real.sqrt nD := by
    dsimp only [edge, partialSelectionEdgeBudget]
    exact Nat.floor_le (by positivity)
  have hgapUpper : (gap : ℝ) ≤ gapCoeff * Real.sqrt nD := by
    dsimp only [gap, partialSelectionGap]
    exact Nat.floor_le (mul_nonneg hgapCoeff hsqrtDPos.le)
  have hnSle : nS ≤ nZ := by omega
  have hnSreal : (nS : ℝ) ≤ δZ * Real.sqrt nD := by
    calc
      (nS : ℝ) ≤ (nZ : ℝ) := by exact_mod_cast hnSle
      _ ≤ δZ * Real.sqrt nD := hnZ
  have hfirst : ((2 * nS + gap + 1 : ℕ) : ℝ) ≤
      (3 * δZ + gapCoeff) * Real.sqrt nD := by
    push_cast
    calc
      2 * (nS : ℝ) + (gap : ℝ) + 1 ≤
          2 * (δZ * Real.sqrt nD) + gapCoeff * Real.sqrt nD +
            δZ * Real.sqrt nD := by linarith
      _ = (3 * δZ + gapCoeff) * Real.sqrt nD := by ring
  have hsecond : (((s₀ - bad) + 2 * edge : ℕ) : ℝ) ≤
      (a₀ / 4 + 2 * LH) * Real.sqrt nD := by
    push_cast
    calc
      ((s₀ - bad : ℕ) : ℝ) + 2 * (edge : ℝ) ≤
          a₀ / 4 * Real.sqrt nD + 2 * (LH * Real.sqrt nD) := by
            linarith
      _ = (a₀ / 4 + 2 * LH) * Real.sqrt nD := by ring
  have hfirstNonneg : (0 : ℝ) ≤ (2 * nS + gap + 1 : ℕ) := by positivity
  have hsecondNonneg : (0 : ℝ) ≤ (s₀ - bad + 2 * edge : ℕ) := by
    positivity
  have hproduct :
      (((2 * nS + gap + 1) * (s₀ - bad + 2 * edge) : ℕ) : ℝ) ≤
        ((3 * δZ + gapCoeff) * (a₀ / 4 + 2 * LH)) * nD := by
    calc
      (((2 * nS + gap + 1) * (s₀ - bad + 2 * edge) : ℕ) : ℝ) =
          ((2 * nS + gap + 1 : ℕ) : ℝ) *
            ((s₀ - bad + 2 * edge : ℕ) : ℝ) := by
              push_cast
              rfl
      _ ≤ ((3 * δZ + gapCoeff) * Real.sqrt nD) *
          ((a₀ / 4 + 2 * LH) * Real.sqrt nD) := by
            exact mul_le_mul hfirst hsecond hsecondNonneg (by positivity)
      _ = ((3 * δZ + gapCoeff) * (a₀ / 4 + 2 * LH)) *
          (Real.sqrt nD) ^ 2 := by ring
      _ = ((3 * δZ + gapCoeff) * (a₀ / 4 + 2 * LH)) * nD := by
        rw [hsqrtDSq]
  have hcoeffScaled :
      ((3 * δZ + gapCoeff) * (a₀ / 4 + 2 * LH)) * (nD : ℝ) <
        (a₀ / 16) ^ 2 * nD :=
    mul_lt_mul_of_pos_right hcoeff hnDreal
  have hsurvivorSq : (a₀ / 16) ^ 2 * (nD : ℝ) ≤
      (((s₀ - bad : ℕ) : ℝ)) ^ 2 := by
    have hnonneg : 0 ≤ a₀ / 16 * Real.sqrt nD := by positivity
    have hsq := mul_self_le_mul_self hnonneg hsurvivorLower
    calc
      (a₀ / 16) ^ 2 * (nD : ℝ) =
          (a₀ / 16 * Real.sqrt nD) ^ 2 := by rw [mul_pow, hsqrtDSq]
      _ ≤ (((s₀ - bad : ℕ) : ℝ)) ^ 2 := by
        simpa only [pow_two] using hsq
  have hreal :
      (((2 * nS + gap + 1) * (s₀ - bad + 2 * edge) : ℕ) : ℝ) <
        (((s₀ - bad : ℕ) ^ 2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow] using
      hproduct.trans_lt (hcoeffScaled.trans_le hsurvivorSq)
  exact_mod_cast hreal

/-- The first partial matching fits inside an ambient square-root crowd. -/
lemma partialExposure_familyFit
    {a₀ c₀ : ℝ} {n nD : ℕ}
    (ha₀ : 0 < a₀) (hc₀ : 0 ≤ c₀)
    (hcoeff : a₀ * Real.sqrt (2 * c₀) ≤ 1)
    (hnD : (nD : ℝ) ≤ 2 * c₀ * n)
    (hthreshold : (1 / 2 : ℝ) * Real.sqrt n ≤ threshold n) :
    2 * partialMatchingSize a₀ nD ≤ threshold n := by
  have hsUpper : (partialMatchingSize a₀ nD : ℝ) ≤
      a₀ / 4 * Real.sqrt nD := by
    dsimp only [partialMatchingSize]
    have hfloor := Nat.floor_le
      (show 0 ≤ a₀ * Real.sqrt nD / 4 by positivity)
    nlinarith
  have hsqrtD : Real.sqrt nD ≤ Real.sqrt (2 * c₀ * (n : ℝ)) :=
    Real.sqrt_le_sqrt hnD
  have hsqrtProduct : Real.sqrt (2 * c₀ * (n : ℝ)) =
      Real.sqrt (2 * c₀) * Real.sqrt n := by
    exact Real.sqrt_mul (by positivity) _
  have hsqrtDBound : Real.sqrt nD ≤
      Real.sqrt (2 * c₀) * Real.sqrt n := by
    simpa only [hsqrtProduct] using hsqrtD
  have hreal : (2 : ℝ) * partialMatchingSize a₀ nD ≤
      (threshold n : ℝ) := by
    calc
      (2 : ℝ) * partialMatchingSize a₀ nD ≤
          a₀ / 2 * Real.sqrt nD := by nlinarith
      _ ≤ a₀ / 2 *
          (Real.sqrt (2 * c₀) * Real.sqrt n) := by gcongr
      _ = (a₀ * Real.sqrt (2 * c₀)) / 2 * Real.sqrt n := by ring
      _ ≤ (1 / 2 : ℝ) * Real.sqrt n := by gcongr
      _ ≤ threshold n := hthreshold
  exact_mod_cast hreal

/-- The complete numeric package consumed by the generalized outer partial
exposure and its deterministic survivor selection. -/
structure PartialExposureFinalBounds
    (K n nD nZ nS m : ℕ)
    (a₀ theta Q C LH c₀ δZ gapCoeff : ℝ) : Prop where
  risk : PartialExposureRiskBounds K nD m a₀ theta Q C LH
  family_fit : 2 * partialMatchingSize a₀ nD ≤ threshold n
  selection_turan :
    (2 * nS + partialSelectionGap gapCoeff nD + 1) *
        (partialMatchingSize a₀ nD - partialBadBudget a₀ nD +
          2 * partialSelectionEdgeBudget LH nD) <
      (partialMatchingSize a₀ nD - partialBadBudget a₀ nD) ^ 2

/-- A single ambient threshold supplies the generalized risk budget, the
matching/crowd fit, and the strict natural Turán inequality uniformly over
every branch order between its prescribed linear bounds. -/
theorem exists_partialExposureFinalBounds
    {K : ℕ} {a₀ theta Q C LH c₀ δZ gapCoeff : ℝ}
    (hK : 0 < K) (ha₀ : 0 < a₀) (htheta : 0 < theta)
    (hQ : 0 < Q) (hC : 0 ≤ C) (hLH : 0 < LH)
    (hc₀ : 0 < c₀) (hδZ : 0 < δZ) (hgapCoeff : 0 ≤ gapCoeff)
    (hriskCoeff :
      8 * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2))) +
          a₀ ^ 2 * C / (16 * LH) ≤ 3 / 16)
    (hfamilyCoeff : a₀ * Real.sqrt (2 * c₀) ≤ 1)
    (hturanCoeff :
      (3 * δZ + gapCoeff) * (a₀ / 4 + 2 * LH) < (a₀ / 16) ^ 2) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ nD nZ nS m : ℕ,
      c₀ / 2 * n ≤ (nD : ℝ) →
      (nD : ℝ) ≤ 2 * c₀ * n →
      (nZ : ℝ) ≤ δZ * Real.sqrt nD →
      nS + 1 = nZ → 2 * nD ≤ m →
      PartialExposureFinalBounds K n nD nZ nS m
        a₀ theta Q C LH c₀ δZ gapCoeff := by
  obtain ⟨Nrisk, hNrisk⟩ := exists_partialExposureRiskBounds
    hK ha₀ htheta hQ hC hLH hriskCoeff
  obtain ⟨Nthreshold, hNthreshold⟩ :=
    exists_half_mul_sqrt_le_floor 1 (by norm_num)
  obtain ⟨Ndelta, hNdelta⟩ := exists_const_le_mul_sqrt δZ 1 hδZ
  let ND : ℕ := max Nrisk Ndelta
  obtain ⟨Nlinear, hNlinear⟩ :=
    exists_nat_rpow_ge 1 (2 * (ND : ℝ) / c₀) (by norm_num)
  refine ⟨max Nthreshold Nlinear, ?_⟩
  intro n hn nD nZ nS m hnDLower hnDUpper hnZ hnS hm
  have hNthresh : Nthreshold ≤ n := (le_max_left _ _).trans hn
  have hNlin : Nlinear ≤ n := (le_max_right _ _).trans hn
  have hnLarge := hNlinear n hNlin
  have hNDreal : (ND : ℝ) ≤ c₀ / 2 * n := by
    rw [Real.rpow_one] at hnLarge
    have hcne : c₀ ≠ 0 := hc₀.ne'
    calc
      (ND : ℝ) = c₀ / 2 * (2 * (ND : ℝ) / c₀) := by field_simp
      _ ≤ c₀ / 2 * n := by gcongr
  have hNDcast : (ND : ℝ) ≤ nD := hNDreal.trans hnDLower
  have hNDnat : ND ≤ nD := by exact_mod_cast hNDcast
  have hNrisk' : Nrisk ≤ nD := (le_max_left _ _).trans hNDnat
  have hNdelta' : Ndelta ≤ nD := (le_max_right _ _).trans hNDnat
  have H := hNrisk nD hNrisk' m hm
  have hthreshold : (1 / 2 : ℝ) * Real.sqrt n ≤ threshold n := by
    simpa only [threshold, one_div, one_mul] using hNthreshold n hNthresh
  have hfit := partialExposure_familyFit ha₀ hc₀.le hfamilyCoeff
    hnDUpper hthreshold
  have hone : 1 ≤ δZ * Real.sqrt nD := hNdelta nD hNdelta'
  exact {
    risk := H
    family_fit := hfit
    selection_turan := partialExposure_selectionTuran ha₀ hLH hδZ hgapCoeff
      hturanCoeff H hnS hnZ hone }

/-- Choose constants for the stricter generalized partial-exposure risk.
The degree contribution no longer contains a factor `a₀`, so `Q` is first
chosen genuinely large; only then is `a₀` reduced to pay for collisions.
The returned collision multiplier may be taken to be `1`. -/
theorem exists_partialExposureRiskConstants
    {K : ℕ} {A C : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hC : 0 ≤ C) :
    ∃ a₀ Q LH : ℝ,
      0 < a₀ ∧ a₀ ≤ A ∧ 0 < Q ∧ 0 < LH ∧
        8 * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2))) +
            a₀ ^ 2 * C / (16 * LH) ≤ 3 / 16 := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨Nexp, hNexp⟩ :=
    exists_polynomial_mul_exp_neg_lt 8 1 0 (by norm_num) (by norm_num)
      (1 / 16) (by norm_num)
  let q : ℕ := max 1 Nexp
  have hq1 : 1 ≤ q := le_max_left _ _
  have hNq : Nexp ≤ q := le_max_right _ _
  have hqreal : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_one.trans_le hq1)
  have hsqrtqPos : 0 < Real.sqrt q := Real.sqrt_pos.2 hqreal
  have hsqrtqSq : (Real.sqrt q) ^ 2 = (q : ℝ) := Real.sq_sqrt hqreal.le
  let Q : ℝ := 8 * (K : ℝ) * Real.sqrt q
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hQratio : Q ^ 2 / (64 * (K : ℝ) ^ 2) = (q : ℝ) := by
    dsimp [Q]
    rw [show (8 * (K : ℝ) * Real.sqrt q) ^ 2 =
        64 * (K : ℝ) ^ 2 * (Real.sqrt q) ^ 2 by ring, hsqrtqSq]
    field_simp
  have hdegree : 8 * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2))) ≤
      1 / 16 := by
    have hdecay := (hNexp q hNq).le
    rw [hQratio]
    simpa only [Real.rpow_zero, pow_zero, mul_one, neg_mul, one_mul] using hdecay
  have hCplus : 0 < C + 1 := by linarith
  let cap : ℝ := 1 / (C + 1)
  have hcap : 0 < cap := by dsimp [cap]; positivity
  let a₀ : ℝ := min A cap
  have ha₀ : 0 < a₀ := by dsimp [a₀]; exact lt_min hA hcap
  have haA : a₀ ≤ A := by dsimp [a₀]; exact min_le_left _ _
  have haCap : a₀ ≤ cap := by dsimp [a₀]; exact min_le_right _ _
  have hcapOne : cap ≤ 1 := by
    dsimp [cap]
    apply (div_le_iff₀ hCplus).2
    linarith
  have haOne : a₀ ≤ 1 := haCap.trans hcapOne
  have hcapC : cap * C ≤ 1 := by
    dsimp [cap]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hCplus).2
    linarith
  have haC : a₀ * C ≤ 1 :=
    (mul_le_mul_of_nonneg_right haCap hC).trans hcapC
  have ha₀nonneg : 0 ≤ a₀ := ha₀.le
  have haCnonneg : 0 ≤ a₀ * C := mul_nonneg ha₀nonneg hC
  have hsquareC : a₀ ^ 2 * C ≤ 1 := by
    calc
      a₀ ^ 2 * C = a₀ * (a₀ * C) := by ring
      _ ≤ 1 * 1 := mul_le_mul haOne haC haCnonneg (by norm_num)
      _ = 1 := by norm_num
  have hcollision : a₀ ^ 2 * C / (16 * (1 : ℝ)) ≤ 1 / 16 := by
    norm_num only [mul_one]
    nlinarith
  refine ⟨a₀, Q, 1, ha₀, haA, hQ, by norm_num, ?_⟩
  linarith

/-! ## Corrected full-exposure geometry scales -/

/-- Radius for inserting one candidate cell into the translated inner path.
This is a square-root-scale quantity. -/
def innerExposureRadius (K nS degreeWindow : ℕ)
    (degreeThreshold degreeRadius : ℝ) : ℝ :=
  (K : ℝ) ^ 2 * (nS + 1 : ℕ) + degreeWindow + degreeThreshold +
    degreeRadius / 2

/-- Separation step paired with `innerExposureRadius`; also square-root
scale, unlike `finalSigma` from the ambient outer switching. -/
def innerExposureSigma (sigmaCoeff : ℝ) (nD : ℕ) : ℝ :=
  sigmaCoeff * Real.sqrt nD

/-- Tail threshold for the deletion degree of an entire switching state.
Since `nS` is square-root scale, this threshold is linear in `nD`. -/
def geometricThreshold (qGeom : ℝ) (K nS nD : ℕ) : ℝ :=
  qGeom * (K * nS : ℕ) * Real.sqrt nD

/-- Integer number of translated-path indices allowed to fail geometry. -/
def geometricBadBudget (badGeomCoeff : ℝ) (nD : ℕ) : ℕ :=
  ⌊badGeomCoeff * Real.sqrt nD⌋₊

/-- Common global window radius, on the linear branch-order scale. -/
def exposureGlobalRadius (globalCoeff : ℝ) (nD : ℕ) : ℝ :=
  globalCoeff * nD

/-- At the chosen geometric threshold, the graph degree tail has a constant
exponent independent of `nD`, `K`, and `nS`. -/
lemma graphDegreeRisk_geometricThreshold
    {K nS nD : ℕ} {qGeom : ℝ}
    (hK : 0 < K) (hnS : 0 < nS) (hnD : 0 < nD) :
    AugmentationGraphFull.graphDegreeRisk
        (geometricThreshold qGeom K nS nD) nD (K * nS) =
      2 * Real.exp (-(qGeom ^ 2 / 32)) := by
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hnSne : (nS : ℝ) ≠ 0 := by exact_mod_cast hnS.ne'
  have hnDne : (nD : ℝ) ≠ 0 := by exact_mod_cast hnD.ne'
  have hnDreal : (0 : ℝ) ≤ nD := by positivity
  have hsqrtSq : (Real.sqrt nD) ^ 2 = (nD : ℝ) := Real.sq_sqrt hnDreal
  simp only [AugmentationGraphFull.graphDegreeRisk, geometricThreshold]
  congr 2
  congr 1
  push_cast
  rw [show (qGeom * ((K : ℝ) * nS) * Real.sqrt nD) ^ 2 =
      qGeom ^ 2 * ((K : ℝ) * nS) ^ 2 * (Real.sqrt nD) ^ 2 by ring,
    hsqrtSq]
  field_simp
  ring

/-- All scalar geometry conclusions needed by the corrected graph full
exposure.  In particular, `geometric_risk` is the nonzero first summand of
the final four-term failure budget. -/
structure ExposureGeometryBounds
    (K nD nZ nS degreeWindow : ℕ)
    (degreeThreshold degreeRadius qGeom badGeomCoeff sigmaCoeff
      globalCoeff geomRisk : ℝ) : Prop where
  innerRadius_nonneg :
    0 ≤ innerExposureRadius K nS degreeWindow degreeThreshold degreeRadius
  innerSigma_pos : 0 < innerExposureSigma sigmaCoeff nD
  innerRadius_small :
    2 * innerExposureRadius K nS degreeWindow degreeThreshold degreeRadius <
      innerExposureSigma sigmaCoeff nD
  geometricThreshold_nonneg : 0 ≤ geometricThreshold qGeom K nS nD
  geometric_risk :
    (nS + 1 : ℕ) *
        AugmentationGraphFull.graphDegreeRisk
          (geometricThreshold qGeom K nS nD) nD (K * nS) /
          (geometricBadBudget badGeomCoeff nD + 1 : ℕ) ≤ geomRisk
  global_radius :
    ((K * nS : ℕ) : ℝ) ^ 2 +
        (nS : ℝ) * degreeWindow +
        geometricThreshold qGeom K nS nD +
        (nS : ℝ) * degreeRadius / 2 +
        innerExposureRadius K nS degreeWindow degreeThreshold degreeRadius ≤
      exposureGlobalRadius globalCoeff nD

/-- Pointwise construction of the corrected full-exposure geometry package.
All hypotheses are coefficient comparisons; the graph theorem sees only the
five concrete conclusions in `ExposureGeometryBounds`. -/
lemma exposureGeometryBounds
    {K nD nZ nS degreeWindow : ℕ}
    {degreeThreshold degreeRadius qGeom badGeomCoeff sigmaCoeff
      globalCoeff geomRisk δZ windowCoeff thresholdCoeff radiusCoeff : ℝ}
    (hK : 0 < K) (hnD : 0 < nD) (hnSpos : 0 < nS)
    (hnS : nS + 1 = nZ)
    (hδZ : 0 ≤ δZ)
    (hnZ : (nZ : ℝ) ≤ δZ * Real.sqrt nD)
    (hwindowCoeff : 0 ≤ windowCoeff)
    (hdegreeWindow : (degreeWindow : ℝ) ≤ windowCoeff * Real.sqrt nD)
    (hthresholdCoeff : 0 ≤ thresholdCoeff)
    (hdegreeThreshold : 0 ≤ degreeThreshold)
    (hdegreeThresholdUpper : degreeThreshold ≤ thresholdCoeff * Real.sqrt nD)
    (hradiusCoeff : 0 ≤ radiusCoeff)
    (hdegreeRadius : 0 ≤ degreeRadius)
    (hdegreeRadiusUpper : degreeRadius ≤ radiusCoeff * Real.sqrt nD)
    (hqGeom : 0 ≤ qGeom) (hbadGeomCoeff : 0 < badGeomCoeff)
    (hsigmaCoeff : 0 < sigmaCoeff)
    (hinnerCoeff :
      2 * ((K : ℝ) ^ 2 * δZ + windowCoeff + thresholdCoeff +
          radiusCoeff / 2) < sigmaCoeff)
    (hgeomRiskCoeff :
      δZ * (2 * Real.exp (-(qGeom ^ 2 / 32))) / badGeomCoeff ≤ geomRisk)
    (hglobalCoeff :
      ((K : ℝ) * δZ) ^ 2 + δZ * windowCoeff +
          qGeom * K * δZ + δZ * radiusCoeff / 2 +
          ((K : ℝ) ^ 2 * δZ + windowCoeff + thresholdCoeff +
            radiusCoeff / 2) ≤ globalCoeff) :
    ExposureGeometryBounds K nD nZ nS degreeWindow degreeThreshold degreeRadius
      qGeom badGeomCoeff sigmaCoeff globalCoeff geomRisk := by
  have hnDreal : (0 : ℝ) < nD := by exact_mod_cast hnD
  have hsqrtPos : 0 < Real.sqrt nD := Real.sqrt_pos.2 hnDreal
  have hsqrtSq : (Real.sqrt nD) ^ 2 = (nD : ℝ) :=
    Real.sq_sqrt hnDreal.le
  have hsqrtLe : Real.sqrt nD ≤ (nD : ℝ) :=
    AsymptoticThresholds.sqrt_nat_le_nat (by omega)
  have hnSleZ : nS ≤ nZ := by omega
  have hnSUpper : (nS : ℝ) ≤ δZ * Real.sqrt nD := by
    calc
      (nS : ℝ) ≤ (nZ : ℝ) := by exact_mod_cast hnSleZ
      _ ≤ δZ * Real.sqrt nD := hnZ
  have hnSOneUpper : ((nS + 1 : ℕ) : ℝ) ≤
      δZ * Real.sqrt nD := by simpa only [hnS] using hnZ
  have hnSOneUpper' : (nS : ℝ) + 1 ≤ δZ * Real.sqrt nD := by
    simpa only [Nat.cast_add, Nat.cast_one] using hnSOneUpper
  let innerCoeff : ℝ := (K : ℝ) ^ 2 * δZ + windowCoeff +
    thresholdCoeff + radiusCoeff / 2
  have hinnerUpper :
      innerExposureRadius K nS degreeWindow degreeThreshold degreeRadius ≤
        innerCoeff * Real.sqrt nD := by
    dsimp only [innerExposureRadius, innerCoeff]
    push_cast
    calc
      (K : ℝ) ^ 2 * ((nS : ℝ) + 1) + degreeWindow +
          degreeThreshold + degreeRadius / 2 ≤
        (K : ℝ) ^ 2 * (δZ * Real.sqrt nD) +
          windowCoeff * Real.sqrt nD + thresholdCoeff * Real.sqrt nD +
          (radiusCoeff * Real.sqrt nD) / 2 := by
            gcongr
      _ = ((K : ℝ) ^ 2 * δZ + windowCoeff + thresholdCoeff +
          radiusCoeff / 2) * Real.sqrt nD := by ring
  have hinnerNonneg :
      0 ≤ innerExposureRadius K nS degreeWindow degreeThreshold degreeRadius := by
    dsimp only [innerExposureRadius]
    positivity
  have hinnerSmall :
      2 * innerExposureRadius K nS degreeWindow degreeThreshold degreeRadius <
        innerExposureSigma sigmaCoeff nD := by
    have hscaled := mul_lt_mul_of_pos_right hinnerCoeff hsqrtPos
    dsimp only [innerExposureSigma]
    calc
      2 * innerExposureRadius K nS degreeWindow degreeThreshold degreeRadius ≤
          2 * (innerCoeff * Real.sqrt nD) := by gcongr
      _ < sigmaCoeff * Real.sqrt nD := by
        dsimp only [innerCoeff] at hscaled ⊢
        simpa only [mul_assoc] using hscaled
  have hgeomEq := graphDegreeRisk_geometricThreshold
    (qGeom := qGeom) hK hnSpos hnD
  have hbadFloor : badGeomCoeff * Real.sqrt nD <
      (geometricBadBudget badGeomCoeff nD : ℝ) + 1 := by
    simpa only [geometricBadBudget] using
      Nat.lt_floor_add_one (badGeomCoeff * Real.sqrt nD)
  have hbadDenPos : (0 : ℝ) <
      (geometricBadBudget badGeomCoeff nD + 1 : ℕ) := by positivity
  have hpNonneg : 0 ≤ 2 * Real.exp (-(qGeom ^ 2 / 32)) := by positivity
  have hgeomCore :
      ((nS + 1 : ℕ) : ℝ) * (2 * Real.exp (-(qGeom ^ 2 / 32))) /
          (geometricBadBudget badGeomCoeff nD + 1 : ℕ) ≤
        δZ * (2 * Real.exp (-(qGeom ^ 2 / 32))) / badGeomCoeff := by
    rw [div_le_iff₀ hbadDenPos]
    have hbadFloorLe : badGeomCoeff * Real.sqrt nD ≤
        ((geometricBadBudget badGeomCoeff nD + 1 : ℕ) : ℝ) := by
      push_cast
      exact hbadFloor.le
    calc
      ((nS + 1 : ℕ) : ℝ) * (2 * Real.exp (-(qGeom ^ 2 / 32))) ≤
          (δZ * Real.sqrt nD) * (2 * Real.exp (-(qGeom ^ 2 / 32))) := by
            gcongr
      _ = (δZ * (2 * Real.exp (-(qGeom ^ 2 / 32))) / badGeomCoeff) *
          (badGeomCoeff * Real.sqrt nD) := by field_simp
      _ ≤ (δZ * (2 * Real.exp (-(qGeom ^ 2 / 32))) / badGeomCoeff) *
          (geometricBadBudget badGeomCoeff nD + 1 : ℕ) := by
            gcongr
  have hgeomRisk :
      (nS + 1 : ℕ) *
          AugmentationGraphFull.graphDegreeRisk
            (geometricThreshold qGeom K nS nD) nD (K * nS) /
            (geometricBadBudget badGeomCoeff nD + 1 : ℕ) ≤ geomRisk := by
    rw [hgeomEq]
    exact hgeomCore.trans hgeomRiskCoeff
  have hstateSq : (((K * nS : ℕ) : ℝ)) ^ 2 ≤
      ((K : ℝ) * δZ) ^ 2 * nD := by
    push_cast
    have hmul : (K : ℝ) * nS ≤
        ((K : ℝ) * δZ) * Real.sqrt nD := by
      calc
        (K : ℝ) * nS ≤ (K : ℝ) * (δZ * Real.sqrt nD) := by
          exact mul_le_mul_of_nonneg_left hnSUpper (by positivity)
        _ = ((K : ℝ) * δZ) * Real.sqrt nD := by ring
    have hnonneg : (0 : ℝ) ≤ (K : ℝ) * nS := by positivity
    have hsq := mul_self_le_mul_self hnonneg hmul
    calc
      ((K : ℝ) * nS) ^ 2 ≤
          (((K : ℝ) * δZ) * Real.sqrt nD) ^ 2 := by
            simpa only [pow_two] using hsq
      _ = ((K : ℝ) * δZ) ^ 2 * nD := by rw [mul_pow, hsqrtSq]
  have hstateWindow : (nS : ℝ) * degreeWindow ≤
      (δZ * windowCoeff) * nD := by
    calc
      (nS : ℝ) * degreeWindow ≤
          (δZ * Real.sqrt nD) * (windowCoeff * Real.sqrt nD) := by
            exact mul_le_mul hnSUpper hdegreeWindow (by positivity) (by positivity)
      _ = (δZ * windowCoeff) * (Real.sqrt nD) ^ 2 := by ring
      _ = (δZ * windowCoeff) * nD := by rw [hsqrtSq]
  have hgeomUpper : geometricThreshold qGeom K nS nD ≤
      (qGeom * K * δZ) * nD := by
    dsimp only [geometricThreshold]
    push_cast
    calc
      qGeom * ((K : ℝ) * nS) * Real.sqrt nD ≤
          qGeom * ((K : ℝ) * (δZ * Real.sqrt nD)) * Real.sqrt nD := by
            gcongr
      _ = (qGeom * K * δZ) * (Real.sqrt nD) ^ 2 := by ring
      _ = (qGeom * K * δZ) * nD := by rw [hsqrtSq]
  have hstateRadius : (nS : ℝ) * degreeRadius / 2 ≤
      (δZ * radiusCoeff / 2) * nD := by
    have hmul : (nS : ℝ) * degreeRadius ≤
        (δZ * Real.sqrt nD) * (radiusCoeff * Real.sqrt nD) :=
      mul_le_mul hnSUpper hdegreeRadiusUpper hdegreeRadius (by positivity)
    calc
      (nS : ℝ) * degreeRadius / 2 ≤
          ((δZ * Real.sqrt nD) * (radiusCoeff * Real.sqrt nD)) / 2 := by
            linarith
      _ = (δZ * radiusCoeff / 2) * (Real.sqrt nD) ^ 2 := by ring
      _ = (δZ * radiusCoeff / 2) * nD := by rw [hsqrtSq]
  have hinnerLinear :
      innerExposureRadius K nS degreeWindow degreeThreshold degreeRadius ≤
        innerCoeff * nD := hinnerUpper.trans (by
          exact mul_le_mul_of_nonneg_left hsqrtLe (by
            dsimp [innerCoeff]
            positivity))
  have hglobal :
      ((K * nS : ℕ) : ℝ) ^ 2 + (nS : ℝ) * degreeWindow +
          geometricThreshold qGeom K nS nD +
          (nS : ℝ) * degreeRadius / 2 +
          innerExposureRadius K nS degreeWindow degreeThreshold degreeRadius ≤
        exposureGlobalRadius globalCoeff nD := by
    dsimp only [exposureGlobalRadius]
    calc
      ((K * nS : ℕ) : ℝ) ^ 2 + (nS : ℝ) * degreeWindow +
          geometricThreshold qGeom K nS nD +
          (nS : ℝ) * degreeRadius / 2 +
          innerExposureRadius K nS degreeWindow degreeThreshold degreeRadius ≤
        (((K : ℝ) * δZ) ^ 2 + δZ * windowCoeff +
          qGeom * K * δZ + δZ * radiusCoeff / 2 + innerCoeff) * nD := by
            nlinarith [hstateSq, hstateWindow, hgeomUpper, hstateRadius,
              hinnerLinear]
      _ ≤ globalCoeff * nD := by gcongr
  exact {
    innerRadius_nonneg := hinnerNonneg
    innerSigma_pos := by dsimp [innerExposureSigma]; positivity
    innerRadius_small := hinnerSmall
    geometricThreshold_nonneg := by dsimp [geometricThreshold]; positivity
    geometric_risk := hgeomRisk
    global_radius := hglobal }

/-- An ambient crowd window becomes a branch-order square-root bound with
any coefficient strictly larger than its limiting value
`eta * sqrt (2 / c₀)`.  This is the transport used when instantiating
`exposureGeometryBounds` from `degreeWindow ≤ window eta n`. -/
theorem exists_window_le_branchSqrt
    {eta c₀ windowCoeff : ℝ}
    (heta : 0 ≤ eta) (hc₀ : 0 < c₀)
    (hwindowCoeff : eta * Real.sqrt (2 / c₀) < windowCoeff) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ nD : ℕ,
      c₀ / 2 * n ≤ (nD : ℝ) →
      (window eta n : ℝ) ≤ windowCoeff * Real.sqrt nD := by
  let gap : ℝ := windowCoeff - eta * Real.sqrt (2 / c₀)
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hcHalf : 0 < c₀ / 2 := by positivity
  have hscale : 0 < gap * Real.sqrt (c₀ / 2) := by positivity
  obtain ⟨N, hN⟩ := exists_const_le_mul_sqrt
    (gap * Real.sqrt (c₀ / 2)) 1 hscale
  refine ⟨max 1 N, ?_⟩
  intro n hn nD hnD
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hN' : N ≤ n := (le_max_right _ _).trans hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_one.trans_le hn1)
  have hnDpos : (0 : ℝ) < nD := lt_of_lt_of_le
    (mul_pos hcHalf hnreal) hnD
  have hsqrtDPos : 0 < Real.sqrt nD := Real.sqrt_pos.2 hnDpos
  have hsqrtLower : Real.sqrt (c₀ / 2 * (n : ℝ)) ≤ Real.sqrt nD :=
    Real.sqrt_le_sqrt hnD
  have hsqrtProduct : Real.sqrt (c₀ / 2 * (n : ℝ)) =
      Real.sqrt (c₀ / 2) * Real.sqrt n := by
    exact Real.sqrt_mul (by positivity) _
  have hgapUnit : 1 ≤ gap * Real.sqrt nD := by
    calc
      1 ≤ (gap * Real.sqrt (c₀ / 2)) * Real.sqrt n := hN n hN'
      _ = gap * Real.sqrt (c₀ / 2 * (n : ℝ)) := by
        rw [hsqrtProduct]
        ring
      _ ≤ gap * Real.sqrt nD := by gcongr
  have hsqrtRecip : Real.sqrt (2 / c₀) * Real.sqrt (c₀ / 2) = 1 := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 / c₀)]
    have hcne : c₀ ≠ 0 := hc₀.ne'
    have hprod : (2 / c₀) * (c₀ / 2) = (1 : ℝ) := by field_simp
    rw [hprod, Real.sqrt_one]
  have hsqrtAmbient : Real.sqrt n ≤ Real.sqrt (2 / c₀) * Real.sqrt nD := by
    calc
      Real.sqrt n =
          (Real.sqrt (2 / c₀) * Real.sqrt (c₀ / 2)) * Real.sqrt n := by
            rw [hsqrtRecip, one_mul]
      _ = Real.sqrt (2 / c₀) *
          Real.sqrt (c₀ / 2 * (n : ℝ)) := by rw [hsqrtProduct]; ring
      _ ≤ Real.sqrt (2 / c₀) * Real.sqrt nD := by gcongr
  have hceil : (window eta n : ℝ) < eta * Real.sqrt n + 1 := by
    simpa only [window] using Nat.ceil_lt_add_one
      (mul_nonneg heta (Real.sqrt_nonneg _))
  calc
    (window eta n : ℝ) ≤ eta * Real.sqrt n + 1 := hceil.le
    _ ≤ eta * (Real.sqrt (2 / c₀) * Real.sqrt nD) +
        gap * Real.sqrt nD := by gcongr
    _ = windowCoeff * Real.sqrt nD := by dsimp [gap]; ring

/-! ## A simultaneous outer coefficient choice -/

/-- Fixed constants discharging every coefficient premise of
`exists_finalNumericBounds`.  The augmentation lower and upper coefficients
are both chosen to be `c₀`. -/
structure OuterCoefficientChoice
    (K : ℕ) (cW c aDisc radiusCoeff bStruct : ℝ) where
  c₀ : ℝ
  eta : ℝ
  matchingCoeff : ℝ
  boundaryCoeff : ℝ
  lambdaCoeff : ℝ
  sigmaCoeff : ℝ
  RCoeff : ℝ
  c₀_pos : 0 < c₀
  c₀_small : 6 * c₀ ≤ c
  eta_pos : 0 < eta
  matchingCoeff_pos : 0 < matchingCoeff
  matchingCoeff_eq : matchingCoeff = bStruct
  boundaryCoeff_pos : 0 < boundaryCoeff
  lambdaCoeff_pos : 0 < lambdaCoeff
  sigmaCoeff_pos : 0 < sigmaCoeff
  RCoeff_pos : 0 < RCoeff
  endpointCoeff :
    lambdaCoeff + c₀ * K * cW * Real.sqrt (2 * c₀) ≤ aDisc
  motionCoeff :
    smallStepCoeff K eta *
        (cW + 4 * c + sigmaCoeff +
          2 * K * c₀ * Real.sqrt (2 * c₀)) +
      (cW + 4 * c + c₀ * Real.sqrt (2 * c₀)) * boundaryCoeff ≤
        lambdaCoeff
  packingCoeff :
    512 * cW * Real.sqrt (2 * c₀) ≤
      smallStepCoeff K eta * sigmaCoeff
  radiusCoeffSmall : 4 * radiusCoeff * c₀ < RCoeff

/-- Explicit simultaneous choice of all outer coefficients.  `c₀` is
made small only after the positive step and motion coefficients have been
fixed, so the packing, endpoint, and radius requirements are compatible. -/
theorem exists_outerCoefficientChoice
    {K : ℕ} {cW c aDisc radiusCoeff bStruct : ℝ}
    (hK : 0 < K) (hcW : 0 < cW) (hc : 0 < c) (haDisc : 0 < aDisc)
    (hradiusCoeff : 0 ≤ radiusCoeff) (hbStruct : 0 < bStruct) :
    Nonempty (OuterCoefficientChoice K cW c aDisc radiusCoeff bStruct) := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  let lambdaCoeff : ℝ := aDisc / 2
  have hlambda : 0 < lambdaCoeff := by dsimp [lambdaCoeff]; positivity
  let sigmaCoeff : ℝ := 1
  let B : ℝ := cW + 4 * c + 1 + 2 * K * Real.sqrt 2
  have hB : 0 < B := by dsimp [B]; positivity
  let s : ℝ := lambdaCoeff / (4 * B)
  have hs : 0 < s := by dsimp [s]; positivity
  let eta : ℝ := 2 * (1 + 4 * K) * s
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hstep : smallStepCoeff K eta = s := by
    dsimp [smallStepCoeff, eta]
    have hden : (2 : ℝ) * (1 + 4 * K) ≠ 0 := by positivity
    field_simp
  let boundaryCoeff : ℝ := s
  have hboundary : 0 < boundaryCoeff := by dsimp [boundaryCoeff]; exact hs
  let T : ℝ := min (s / (512 * cW)) (aDisc / (2 * K * cW))
  have hTleft : 0 < s / (512 * cW) := by positivity
  have hTright : 0 < aDisc / (2 * K * cW) := by positivity
  have hT : 0 < T := by dsimp [T]; exact lt_min hTleft hTright
  let c₀ : ℝ := min (c / 6) (min 1 (T ^ 2 / 2))
  have hc₀ : 0 < c₀ := by
    dsimp [c₀]
    exact lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hc₀c : c₀ ≤ c / 6 := by dsimp [c₀]; exact min_le_left _ _
  have hc₀one : c₀ ≤ 1 := by
    dsimp [c₀]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hc₀T : c₀ ≤ T ^ 2 / 2 := by
    dsimp [c₀]
    exact (min_le_right _ _).trans
      (min_le_right _ _)
  have hsqrtT : Real.sqrt (2 * c₀) ≤ T := by
    rw [Real.sqrt_le_iff]
    exact ⟨hT.le, by nlinarith⟩
  have hTpacking : T ≤ s / (512 * cW) := by
    dsimp [T]
    exact min_le_left _ _
  have hTendpoint : T ≤ aDisc / (2 * K * cW) := by
    dsimp [T]
    exact min_le_right _ _
  have hsqrtPacking : 512 * cW * Real.sqrt (2 * c₀) ≤ s := by
    calc
      512 * cW * Real.sqrt (2 * c₀) ≤ 512 * cW * T := by gcongr
      _ ≤ 512 * cW * (s / (512 * cW)) := by gcongr
      _ = s := by field_simp
  have hsqrtEndpoint : (K : ℝ) * cW * Real.sqrt (2 * c₀) ≤
      aDisc / 2 := by
    calc
      (K : ℝ) * cW * Real.sqrt (2 * c₀) ≤ (K : ℝ) * cW * T := by
        gcongr
      _ ≤ (K : ℝ) * cW * (aDisc / (2 * K * cW)) := by gcongr
      _ = aDisc / 2 := by field_simp
  have hc₀sqrtEndpoint : c₀ * (K : ℝ) * cW * Real.sqrt (2 * c₀) ≤
      aDisc / 2 := by
    calc
      c₀ * (K : ℝ) * cW * Real.sqrt (2 * c₀) =
          c₀ * ((K : ℝ) * cW * Real.sqrt (2 * c₀)) := by ring
      _ ≤
          1 * ((K : ℝ) * cW * Real.sqrt (2 * c₀)) := by
            exact mul_le_mul_of_nonneg_right hc₀one
              (show 0 ≤ (K : ℝ) * cW * Real.sqrt (2 * c₀) by positivity)
      _ ≤ aDisc / 2 := by simpa only [one_mul] using hsqrtEndpoint
  have hsqrtTwo : Real.sqrt (2 * c₀) ≤ Real.sqrt 2 := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hc₀sqrtTwo : c₀ * Real.sqrt (2 * c₀) ≤ Real.sqrt 2 := by
    calc
      c₀ * Real.sqrt (2 * c₀) ≤ 1 * Real.sqrt (2 * c₀) := by
        gcongr
      _ ≤ Real.sqrt 2 := by simpa only [one_mul] using hsqrtTwo
  have hregular :
      cW + 4 * c + sigmaCoeff +
          2 * K * c₀ * Real.sqrt (2 * c₀) ≤ B := by
    dsimp only [sigmaCoeff, B]
    have hscaled := mul_le_mul_of_nonneg_left hc₀sqrtTwo
      (show (0 : ℝ) ≤ 2 * K by positivity)
    nlinarith
  have hboundaryRegular :
      cW + 4 * c + c₀ * Real.sqrt (2 * c₀) ≤ B := by
    dsimp only [B]
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hsqrtTwoNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith [hc₀sqrtTwo]
  have hmotion :
      smallStepCoeff K eta *
          (cW + 4 * c + sigmaCoeff +
            2 * K * c₀ * Real.sqrt (2 * c₀)) +
        (cW + 4 * c + c₀ * Real.sqrt (2 * c₀)) * boundaryCoeff ≤
      lambdaCoeff := by
    rw [hstep]
    dsimp only [boundaryCoeff]
    calc
      s * (cW + 4 * c + sigmaCoeff +
          2 * K * c₀ * Real.sqrt (2 * c₀)) +
          (cW + 4 * c + c₀ * Real.sqrt (2 * c₀)) * s ≤
        s * B + B * s := by gcongr
      _ = lambdaCoeff / 2 := by dsimp [s]; field_simp; ring
      _ ≤ lambdaCoeff := by linarith
  let RCoeff : ℝ := 4 * radiusCoeff * c₀ + 1
  have hRCoeff : 0 < RCoeff := by
    dsimp only [RCoeff]
    positivity
  have hradius : 4 * radiusCoeff * c₀ < RCoeff := by
    dsimp only [RCoeff]
    linarith
  refine ⟨{
    c₀ := c₀
    eta := eta
    matchingCoeff := bStruct
    boundaryCoeff := boundaryCoeff
    lambdaCoeff := lambdaCoeff
    sigmaCoeff := sigmaCoeff
    RCoeff := RCoeff
    c₀_pos := hc₀
    c₀_small := by nlinarith [hc₀c]
    eta_pos := heta
    matchingCoeff_pos := hbStruct
    matchingCoeff_eq := rfl
    boundaryCoeff_pos := hboundary
    lambdaCoeff_pos := hlambda
    sigmaCoeff_pos := by norm_num [sigmaCoeff]
    RCoeff_pos := hRCoeff
    endpointCoeff := ?_
    motionCoeff := hmotion
    packingCoeff := ?_
    radiusCoeffSmall := hradius }⟩
  · dsimp only [lambdaCoeff]
    nlinarith [hc₀sqrtEndpoint]
  · dsimp only [sigmaCoeff]
    rw [hstep, mul_one]
    exact hsqrtPacking

end

end Erdos636.AugmentationScales
