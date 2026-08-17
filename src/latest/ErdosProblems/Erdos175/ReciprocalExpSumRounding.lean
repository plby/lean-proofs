/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.ReciprocalExpSumBound
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Shift selection and harmonic-factor bounds

This file contains the rounding and elementary real-algebra part of the
two-step reciprocal exponential-sum estimate.  The selected shift is the
largest integer `q ≤ √N` for which the terminal Kusmin--Landau phase is
admissible.  In the high-frequency branch this is an integer cube-root
choice up to the harmless rounding factor `2^3`.
-/

namespace Erdos175

noncomputable section

/-- The upper-phase constraint imposed on the two Weyl shift ranges. -/
def reciprocalShiftAdmissible (x : ℝ) (C q : ℕ) : Prop :=
  12 * x * (q : ℝ) ^ 3 ≤ (C : ℝ) ^ 4

/-- The largest phase-admissible shift not exceeding `⌊√N⌋`. -/
def reciprocalShift (x : ℝ) (C N : ℕ) : ℕ :=
  by
    classical
    exact Nat.findGreatest (reciprocalShiftAdmissible x C) (Nat.sqrt N)

lemma reciprocalShift_le_sqrt (x : ℝ) (C N : ℕ) :
    reciprocalShift x C N ≤ Nat.sqrt N := by
  classical
  unfold reciprocalShift
  exact Nat.findGreatest_le _

/-- The selected shift is always short enough for both differencing steps. -/
lemma reciprocalShift_sq_le (x : ℝ) (C N : ℕ) :
    (reciprocalShift x C N) ^ 2 ≤ N := by
  exact (Nat.pow_le_pow_left (reciprocalShift_le_sqrt x C N) 2).trans
    (Nat.sqrt_le' N)

/-- The selected shift satisfies the terminal phase constraint. -/
lemma reciprocalShift_admissible (x : ℝ) (C N : ℕ) :
    reciprocalShiftAdmissible x C (reciprocalShift x C N) := by
  classical
  unfold reciprocalShift
  exact Nat.findGreatest_spec (P := reciprocalShiftAdmissible x C)
    (m := 0) (n := Nat.sqrt N) (Nat.zero_le _) (by
      simp [reciprocalShiftAdmissible])

/-- If shift `1` is admissible and the interval is nonempty, then the
selected shift is positive. -/
lemma reciprocalShift_pos {x : ℝ} {C N : ℕ} (hN : 0 < N)
    (hone : 12 * x ≤ (C : ℝ) ^ 4) :
    0 < reciprocalShift x C N := by
  classical
  rw [reciprocalShift, Nat.findGreatest_pos]
  refine ⟨1, by omega, ?_, ?_⟩
  · exact Nat.sqrt_pos.mpr hN
  · simpa [reciprocalShiftAdmissible] using hone

/-- If the selected shift has not reached the square-root ceiling, its
successor violates the phase constraint. -/
lemma reciprocalShift_succ_not_admissible {x : ℝ} {C N : ℕ}
    (hlt : reciprocalShift x C N < Nat.sqrt N) :
    ¬ reciprocalShiftAdmissible x C (reciprocalShift x C N + 1) := by
  classical
  exact Nat.findGreatest_is_greatest (P := reciprocalShiftAdmissible x C)
    (Nat.lt_succ_self _) (Nat.succ_le_iff.mpr hlt)

/-- Cube-root rounding: below the square-root ceiling, a positive selected
shift is within a factor `2` of the real phase threshold. -/
lemma reciprocalShift_rounding_lower {x : ℝ} {C N : ℕ} (hx : 0 < x)
    (hq : 1 ≤ reciprocalShift x C N)
    (hlt : reciprocalShift x C N < Nat.sqrt N) :
    (C : ℝ) ^ 4 <
      96 * x * (reciprocalShift x C N : ℝ) ^ 3 := by
  let q := reciprocalShift x C N
  have hfail := reciprocalShift_succ_not_admissible (x := x) (C := C) (N := N) hlt
  have hnext : (C : ℝ) ^ 4 < 12 * x * ((q + 1 : ℕ) : ℝ) ^ 3 := by
    exact lt_of_not_ge hfail
  have hqdoubleNat : q + 1 ≤ 2 * q := by omega
  have hqdouble : ((q + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by
    exact_mod_cast hqdoubleNat
  calc
    (C : ℝ) ^ 4 < 12 * x * ((q + 1 : ℕ) : ℝ) ^ 3 := hnext
    _ ≤ 12 * x * (2 * (q : ℝ)) ^ 3 := by gcongr
    _ = 96 * x * (q : ℝ) ^ 3 := by ring

/-- The high-frequency hypothesis says that the phase constraint already
fails at `⌊√N⌋`; hence the selected shift lies strictly below that ceiling. -/
lemma reciprocalShift_lt_sqrt_of_highFrequency {x : ℝ} {C N : ℕ}
    (hhigh : (C : ℝ) ^ 4 <
      12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    reciprocalShift x C N < Nat.sqrt N := by
  have hle := reciprocalShift_le_sqrt x C N
  by_contra hnot
  have heq : reciprocalShift x C N = Nat.sqrt N :=
    Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
  have hadm := reciprocalShift_admissible x C N
  rw [heq] at hadm
  exact (not_le_of_gt hhigh) hadm

/-- All integer rounding facts for the high-frequency cube-root choice. -/
lemma reciprocalShift_scale_bounds {x : ℝ} {C N : ℕ}
    (hx : 0 < x) (hN : 0 < N)
    (hone : 12 * x ≤ (C : ℝ) ^ 4)
    (hhigh : (C : ℝ) ^ 4 <
      12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    let q := reciprocalShift x C N
    1 ≤ q ∧ q ^ 2 ≤ N ∧
      12 * x * (q : ℝ) ^ 3 ≤ (C : ℝ) ^ 4 ∧
      (C : ℝ) ^ 4 < 96 * x * (q : ℝ) ^ 3 := by
  let q := reciprocalShift x C N
  have hqpos : 0 < q := reciprocalShift_pos hN hone
  have hq : 1 ≤ q := hqpos
  have hlt : q < Nat.sqrt N := reciprocalShift_lt_sqrt_of_highFrequency hhigh
  exact ⟨hq, reciprocalShift_sq_le x C N,
    reciprocalShift_admissible x C N,
    reciprocalShift_rounding_lower hx hq hlt⟩

/-- `finiteHarmonic` is Mathlib's harmonic number, coerced to the reals. -/
lemma finiteHarmonic_eq_harmonic (H : ℕ) :
    finiteHarmonic H = (harmonic H : ℝ) := by
  unfold finiteHarmonic harmonic
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma finiteHarmonic_le_one_add_log (H : ℕ) :
    finiteHarmonic H ≤ 1 + Real.log H := by
  rw [finiteHarmonic_eq_harmonic]
  exact harmonic_le_one_add_log H

/-- The two harmonic factors produced by the Weyl shifts cost at most two
squares of the usual logarithmic factor. -/
lemma finiteHarmonic_sq_mul_le {q : ℕ} (hq : 1 ≤ q) :
    finiteHarmonic (q ^ 2) * finiteHarmonic q ≤
      2 * (1 + Real.log q) ^ 2 := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hq2 := finiteHarmonic_le_one_add_log (q ^ 2)
  have hq1 := finiteHarmonic_le_one_add_log q
  have hlogpow : Real.log ((q ^ 2 : ℕ) : ℝ) = 2 * Real.log (q : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hlogpow] at hq2
  calc
    finiteHarmonic (q ^ 2) * finiteHarmonic q ≤
        (1 + 2 * Real.log (q : ℝ)) * (1 + Real.log (q : ℝ)) := by
      exact mul_le_mul hq2 hq1 (finiteHarmonic_nonneg q)
        (by positivity)
    _ ≤ 2 * (1 + Real.log (q : ℝ)) ^ 2 := by nlinarith

/-- The terminal part of the fourth-power estimate after cube-root
rounding.  On a dyadic interval (`N ≤ C`) the apparent fourth power of the
right endpoint is absorbed by the lower rounding inequality. -/
lemma dyadic_terminal_term_le {x : ℝ} {C N q : ℕ}
    (hx : 0 < x) (hq : 1 ≤ q) (hNC : N ≤ C)
    (hscale : (C : ℝ) ^ 4 ≤ 96 * x * (q : ℝ) ^ 3) :
    (512 : ℝ) * (N : ℝ) ^ 3 *
          (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) ≤
      131072 * (N : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hCN : ((C + N : ℕ) : ℝ) ≤ 2 * (C : ℝ) := by
    exact_mod_cast (show C + N ≤ 2 * C by omega)
  have hpow : ((C + N : ℕ) : ℝ) ^ 4 ≤ (2 * (C : ℝ)) ^ 4 := by
    gcongr
  have hratio : ((C + N : ℕ) : ℝ) ^ 4 / (6 * x) /
      (q : ℝ) ^ 3 ≤ 256 := by
    rw [div_le_iff₀ (pow_pos hqpos 3), div_le_iff₀ (by positivity : 0 < 6 * x)]
    calc
      ((C + N : ℕ) : ℝ) ^ 4 ≤ (2 * (C : ℝ)) ^ 4 := hpow
      _ = 16 * (C : ℝ) ^ 4 := by ring
      _ ≤ 16 * (96 * x * (q : ℝ) ^ 3) := by gcongr
      _ = 256 * (q : ℝ) ^ 3 * (6 * x) := by ring
  have hH : 0 ≤ finiteHarmonic (q ^ 2) * finiteHarmonic q :=
    mul_nonneg (finiteHarmonic_nonneg _) (finiteHarmonic_nonneg _)
  calc
    (512 : ℝ) * (N : ℝ) ^ 3 *
          (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) =
        (512 * (N : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q)) *
          (((C + N : ℕ) : ℝ) ^ 4 / (6 * x) / (q : ℝ) ^ 3) := by ring
    _ ≤ (512 * (N : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q)) * 256 := by
      gcongr
    _ = 131072 * (N : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by ring

/-- Fully elementary simplification of the fourth-power right-hand side:
after the dyadic and cube-root inequalities only the diagonal power-saving
term and a squared logarithm remain. -/
lemma dyadic_fourth_rhs_le {x : ℝ} {C N q : ℕ}
    (hx : 0 < x) (hq : 1 ≤ q) (hNC : N ≤ C)
    (hscale : (C : ℝ) ^ 4 ≤ 96 * x * (q : ℝ) ^ 3) :
    512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
        (512 : ℝ) * (N : ℝ) ^ 3 *
          (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
            (finiteHarmonic (q ^ 2) * finiteHarmonic q) ≤
      512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
        262144 * (N : ℝ) ^ 3 * (1 + Real.log q) ^ 2 := by
  have hterm :
    (512 : ℝ) * (N : ℝ) ^ 3 *
          (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) ≤
        262144 * (N : ℝ) ^ 3 * (1 + Real.log q) ^ 2 := by
    calc
      (512 : ℝ) * (N : ℝ) ^ 3 *
            (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
            (finiteHarmonic (q ^ 2) * finiteHarmonic q) ≤
          131072 * (N : ℝ) ^ 3 *
            (finiteHarmonic (q ^ 2) * finiteHarmonic q) :=
        dyadic_terminal_term_le hx hq hNC hscale
      _ ≤ 131072 * (N : ℝ) ^ 3 *
            (2 * (1 + Real.log q) ^ 2) := by
        exact mul_le_mul_of_nonneg_left (finiteHarmonic_sq_mul_le hq) (by positivity)
      _ = 262144 * (N : ℝ) ^ 3 * (1 + Real.log q) ^ 2 := by ring
  exact add_le_add_right hterm _

/-- The concrete high-frequency, dyadic reciprocal exponential-sum bound.
The shift parameter is selected internally, so no rounding side conditions
remain in the statement. -/
theorem reciprocalExpRange_fourth_le_dyadic_highFrequency
    (x : ℝ) (C N : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hN : 0 < N) (hNC : N ≤ C)
    (hone : 12 * x ≤ (C : ℝ) ^ 4)
    (hhigh : (C : ℝ) ^ 4 <
      12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    let q := reciprocalShift x C N
    ‖reciprocalExpRange x C N‖ ^ 4 ≤
      512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
        262144 * (N : ℝ) ^ 3 * (1 + Real.log q) ^ 2 := by
  let q := reciprocalShift x C N
  obtain ⟨hq, hqN, hderiv, hscale⟩ :=
    reciprocalShift_scale_bounds hx hN hone hhigh
  have hraw := reciprocalExpRange_fourth_le
    x C N q hx hC hq hqN hderiv
  exact hraw.trans (dyadic_fourth_rhs_le hx hq hNC hscale.le)

/-! ### Eliminating the shift parameter -/

/-- A cubic scale inequality gives the inverse-square saving used below. -/
private lemma inv_sq_le_rpow_two_thirds {a : ℝ} {q : ℕ}
    (ha : 0 ≤ a) (hq : 1 ≤ q)
    (hscale : 1 ≤ a * (q : ℝ) ^ 3) :
    1 / (q : ℝ) ^ 2 ≤ a ^ (2 / 3 : ℝ) := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (Real.rpow_nonneg ha _)
  have hsquare : (1 : ℝ) ≤ (a * (q : ℝ) ^ 3) ^ 2 := by
    nlinarith [sq_nonneg (a * (q : ℝ) ^ 3 - 1)]
  have hrpow : (a ^ (2 / 3 : ℝ)) ^ 3 = a ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul ha]
    norm_num
  rw [hrpow]
  calc
    (1 / (q : ℝ) ^ 2) ^ 3 = 1 / ((q : ℝ) ^ 3) ^ 2 := by
      field_simp
    _ ≤ a ^ 2 := by
      rw [div_le_iff₀ (by positivity : 0 < ((q : ℝ) ^ 3) ^ 2)]
      simpa [mul_pow] using hsquare

/-- The selected shift's diagonal factor, with the shift eliminated. -/
private lemma reciprocalShift_inv_sq_le {x : ℝ} {C N : ℕ}
    (hx : 0 < x) (hC : 0 < C) (hN : 0 < N)
    (hone : 12 * x ≤ (C : ℝ) ^ 4)
    (hhigh : (C : ℝ) ^ 4 < 12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    let q := reciprocalShift x C N
    1 / (q : ℝ) ^ 2 ≤
      (96 * x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) := by
  let q := reciprocalShift x C N
  obtain ⟨hq, -, -, hscale⟩ :=
    reciprocalShift_scale_bounds hx hN hone hhigh
  have hC4 : 0 < (C : ℝ) ^ 4 := by positivity
  have honeScale :
      1 ≤ (96 * x / (C : ℝ) ^ 4) * (q : ℝ) ^ 3 := by
    calc
      (1 : ℝ) = (C : ℝ) ^ 4 / (C : ℝ) ^ 4 := by field_simp
      _ ≤ (96 * x * (q : ℝ) ^ 3) / (C : ℝ) ^ 4 := by gcongr
      _ = (96 * x / (C : ℝ) ^ 4) * (q : ℝ) ^ 3 := by ring
  exact inv_sq_le_rpow_two_thirds (by positivity) hq honeScale

/-- In the high-frequency branch, the interval-length loss is absorbed by
the same sixth-root scale as the selected shift. -/
private lemma inv_length_le_scale {x : ℝ} {C N : ℕ}
    (hx : 0 < x) (hC : 0 < C) (hN : 0 < N)
    (hhigh : (C : ℝ) ^ 4 < 12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    1 / (N : ℝ) ≤
      (96 * x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) := by
  have hsqrt : 1 ≤ Nat.sqrt N := Nat.sqrt_pos.mpr hN
  have hC4 : 0 < (C : ℝ) ^ 4 := by positivity
  have honeScale :
      1 ≤ (96 * x / (C : ℝ) ^ 4) * (Nat.sqrt N : ℝ) ^ 3 := by
    have hscaled : (C : ℝ) ^ 4 < 96 * x * (Nat.sqrt N : ℝ) ^ 3 := by
      calc
        (C : ℝ) ^ 4 < 12 * x * (Nat.sqrt N : ℝ) ^ 3 := hhigh
        _ ≤ 96 * x * (Nat.sqrt N : ℝ) ^ 3 := by
          have : 0 ≤ x * (Nat.sqrt N : ℝ) ^ 3 := by positivity
          nlinarith
    calc
      (1 : ℝ) = (C : ℝ) ^ 4 / (C : ℝ) ^ 4 := by field_simp
      _ ≤ (96 * x * (Nat.sqrt N : ℝ) ^ 3) / (C : ℝ) ^ 4 := by gcongr
      _ = (96 * x / (C : ℝ) ^ 4) * (Nat.sqrt N : ℝ) ^ 3 := by ring
  have hsqrtInv :
      1 / (Nat.sqrt N : ℝ) ^ 2 ≤
        (96 * x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) :=
    inv_sq_le_rpow_two_thirds (by positivity) hsqrt honeScale
  have hsqrtSq : (Nat.sqrt N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast Nat.sqrt_le' N
  exact (one_div_le_one_div_of_le (by positivity) hsqrtSq).trans hsqrtInv

/-- A q-free fourth-power estimate.  The deliberately generous numerical
constant keeps all later consumers independent of rounding details. -/
theorem reciprocalExpRange_fourth_le_dyadic_qfree
    (x : ℝ) (C N : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hN : 0 < N) (hNC : N ≤ C)
    (hone : 12 * x ≤ (C : ℝ) ^ 4)
    (hhigh : (C : ℝ) ^ 4 <
      12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    ‖reciprocalExpRange x C N‖ ^ 4 ≤
      25214976 * (N : ℝ) ^ 4 *
        (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) *
        (1 + Real.log C) ^ 2 := by
  let q := reciprocalShift x C N
  let D := (96 * x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ)
  have hq : 1 ≤ q := (reciprocalShift_scale_bounds hx hN hone hhigh).1
  have hqC : q ≤ C :=
    (reciprocalShift_le_sqrt x C N).trans
      ((Nat.sqrt_le_self N).trans hNC)
  have hlogq : Real.log (q : ℝ) ≤ Real.log (C : ℝ) := by
    exact Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqC)
  have hlogC : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hD : 0 ≤ D := Real.rpow_nonneg (by positivity) _
  have hqInv : 1 / (q : ℝ) ^ 2 ≤ D :=
    reciprocalShift_inv_sq_le hx hC hN hone hhigh
  have hNInv : 1 / (N : ℝ) ≤ D :=
    inv_length_le_scale hx hC hN hhigh
  have hbase := reciprocalExpRange_fourth_le_dyadic_highFrequency
    x C N hx hC hN hNC hone hhigh
  change ‖reciprocalExpRange x C N‖ ^ 4 ≤
    512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
      262144 * (N : ℝ) ^ 3 * (1 + Real.log q) ^ 2 at hbase
  have hdiag :
      512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 ≤
        512 * (N : ℝ) ^ 4 * D := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hqInv) (by positivity)
  have hNpow : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 4 * D := by
    have hNr : (N : ℝ) ≠ 0 := by positivity
    calc
      (N : ℝ) ^ 3 = (N : ℝ) ^ 4 * (1 / (N : ℝ)) := by
        field_simp
      _ ≤ (N : ℝ) ^ 4 * D := by gcongr
  have hlogpow :
      (1 + Real.log (q : ℝ)) ^ 2 ≤
        (1 + Real.log (C : ℝ)) ^ 2 := by
    gcongr
  have hrough :
      ‖reciprocalExpRange x C N‖ ^ 4 ≤
        262656 * (N : ℝ) ^ 4 * D *
          (1 + Real.log (C : ℝ)) ^ 2 := by
    calc
      ‖reciprocalExpRange x C N‖ ^ 4 ≤
          512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
            262144 * (N : ℝ) ^ 3 * (1 + Real.log q) ^ 2 := hbase
      _ ≤ 512 * (N : ℝ) ^ 4 * D +
            262144 * ((N : ℝ) ^ 4 * D) *
              (1 + Real.log C) ^ 2 := by gcongr
      _ ≤ 262656 * (N : ℝ) ^ 4 * D *
            (1 + Real.log C) ^ 2 := by
        have : 1 ≤ (1 + Real.log (C : ℝ)) ^ 2 := by nlinarith
        have hND : 0 ≤ (N : ℝ) ^ 4 * D := by positivity
        nlinarith
  have hfactor :
      D ≤ 96 * (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) := by
    dsimp [D]
    have hδ : 0 ≤ x / (C : ℝ) ^ 4 := by positivity
    have h96 : (96 : ℝ) ^ (2 / 3 : ℝ) ≤ 96 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    rw [show 96 * x / (C : ℝ) ^ 4 =
      96 * (x / (C : ℝ) ^ 4) by ring, Real.mul_rpow (by norm_num) hδ]
    gcongr
  exact hrough.trans (by
    have hL : 0 ≤ (1 + Real.log (C : ℝ)) ^ 2 := sq_nonneg _
    calc
      262656 * (N : ℝ) ^ 4 * D * (1 + Real.log C) ^ 2 ≤
          262656 * (N : ℝ) ^ 4 *
            (96 * (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ)) *
              (1 + Real.log C) ^ 2 := by gcongr
      _ = 25214976 * (N : ℝ) ^ 4 *
            (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) *
              (1 + Real.log C) ^ 2 := by ring)

/-- Norm form of the q-free high-frequency estimate. -/
theorem norm_reciprocalExpRange_le_dyadic_qfree
    (x : ℝ) (C N : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hN : 0 < N) (hNC : N ≤ C)
    (hone : 12 * x ≤ (C : ℝ) ^ 4)
    (hhigh : (C : ℝ) ^ 4 <
      12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    ‖reciprocalExpRange x C N‖ ≤
      128 * (N : ℝ) *
        (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log C) := by
  have hδ : 0 ≤ x / (C : ℝ) ^ 4 := by positivity
  have hlogC : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hL : 0 ≤ 1 + Real.log (C : ℝ) := by positivity
  have hδpow :
      ((x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ)) ^ 4 =
        (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hδ]
    norm_num
  have hsqrtpow :
      (Real.sqrt (1 + Real.log (C : ℝ))) ^ 4 =
        (1 + Real.log (C : ℝ)) ^ 2 := by
    calc
      (Real.sqrt (1 + Real.log (C : ℝ))) ^ 4 =
          ((Real.sqrt (1 + Real.log (C : ℝ))) ^ 2) ^ 2 := by ring
      _ = (1 + Real.log (C : ℝ)) ^ 2 := by rw [Real.sq_sqrt hL]
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
  calc
    ‖reciprocalExpRange x C N‖ ^ 4 ≤
        25214976 * (N : ℝ) ^ 4 *
          (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) *
          (1 + Real.log C) ^ 2 :=
      reciprocalExpRange_fourth_le_dyadic_qfree
        x C N hx hC hN hNC hone hhigh
    _ ≤ (128 * (N : ℝ) *
          (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt (1 + Real.log C)) ^ 4 := by
      rw [mul_pow, mul_pow, mul_pow, hδpow, hsqrtpow]
      have hprod : 0 ≤ (N : ℝ) ^ 4 *
          (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) *
          (1 + Real.log (C : ℝ)) ^ 2 := by positivity
      norm_num
      nlinarith

/-- A log-only presentation, convenient once the scale is large enough that
`log C ≥ 1`. -/
theorem norm_reciprocalExpRange_le_dyadic_qfree_log
    (x : ℝ) (C N : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hN : 0 < N) (hNC : N ≤ C)
    (hone : 12 * x ≤ (C : ℝ) ^ 4)
    (hhigh : (C : ℝ) ^ 4 <
      12 * x * (Nat.sqrt N : ℝ) ^ 3)
    (hlog : 1 ≤ Real.log (C : ℝ)) :
    ‖reciprocalExpRange x C N‖ ≤
      256 * (N : ℝ) *
        (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (Real.log C) := by
  have hsqrt :
      Real.sqrt (1 + Real.log (C : ℝ)) ≤
        2 * Real.sqrt (Real.log (C : ℝ)) := by
    rw [Real.sqrt_le_left (by positivity)]
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ Real.log (C : ℝ))]
    nlinarith
  calc
    ‖reciprocalExpRange x C N‖ ≤
        128 * (N : ℝ) *
          (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt (1 + Real.log C) :=
      norm_reciprocalExpRange_le_dyadic_qfree
        x C N hx hC hN hNC hone hhigh
    _ ≤ 128 * (N : ℝ) *
          (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
          (2 * Real.sqrt (Real.log C)) := by gcongr
    _ = 256 * (N : ℝ) *
          (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt (Real.log C) := by ring

/-- Natural-interval form of the q-free high-frequency estimate, for
`A < n ≤ B`. -/
theorem norm_reciprocalExpSum_le_dyadic_qfree
    (x : ℝ) (A B : ℕ)
    (hx : 0 < x) (hAB : A ≤ B) (hne : A < B)
    (hdyadic : B - A ≤ A + 1)
    (hone : 12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4)
    (hhigh : ((A + 1 : ℕ) : ℝ) ^ 4 <
      12 * x * (Nat.sqrt (B - A) : ℝ) ^ 3) :
    ‖reciprocalExpSum x A B‖ ≤
      128 * ((B - A : ℕ) : ℝ) *
        (x / ((A + 1 : ℕ) : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log ((A + 1 : ℕ) : ℝ)) := by
  rw [reciprocalExpSum_eq_range x A B hAB]
  exact norm_reciprocalExpRange_le_dyadic_qfree
    x (A + 1) (B - A) hx (by omega) (by omega) hdyadic hone hhigh

/-- Natural-interval version of the log-only q-free estimate. -/
theorem norm_reciprocalExpSum_le_dyadic_qfree_log
    (x : ℝ) (A B : ℕ)
    (hx : 0 < x) (hAB : A ≤ B) (hne : A < B)
    (hdyadic : B - A ≤ A + 1)
    (hone : 12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4)
    (hhigh : ((A + 1 : ℕ) : ℝ) ^ 4 <
      12 * x * (Nat.sqrt (B - A) : ℝ) ^ 3)
    (hlog : 1 ≤ Real.log ((A + 1 : ℕ) : ℝ)) :
    ‖reciprocalExpSum x A B‖ ≤
      256 * ((B - A : ℕ) : ℝ) *
        (x / ((A + 1 : ℕ) : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (Real.log ((A + 1 : ℕ) : ℝ)) := by
  rw [reciprocalExpSum_eq_range x A B hAB]
  exact norm_reciprocalExpRange_le_dyadic_qfree_log
    x (A + 1) (B - A) hx (by omega) (by omega) hdyadic hone hhigh hlog

end

end Erdos175
