import ErdosProblems.Erdos486.Statement
import Mathlib.NumberTheory.Harmonic.Bounds

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary bounds for logarithmic counting sums

This file records bounds for the exact real-cutoff definitions in
`Erdos486.Statement`.  In particular, the final lemmas show that every
`logAverage B` is eventually bounded above and below along `atTop`, as needed
by the conditionally complete lattice API for `liminf` and `limsup`.
-/

open Filter Set
open scoped BigOperators

namespace Erdos486

/-- The sum of the reciprocals in `range (n + 1)` is the real coercion of the
`n`th harmonic number.  The term at zero vanishes. -/
theorem sum_range_succ_natCast_inv_eq_harmonic (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), ((m : ℕ) : ℝ)⁻¹) = (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show Nat.succ n + 1 = (n + 1) + 1 by omega, Finset.sum_range_succ,
        ih, harmonic_succ]
      simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]

/-- The reciprocals in `range n` are bounded by the `n`th harmonic number. -/
theorem sum_range_natCast_inv_le_harmonic (n : ℕ) :
    (∑ m ∈ Finset.range n, ((m : ℕ) : ℝ)⁻¹) ≤ (harmonic n : ℝ) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [sum_range_succ_natCast_inv_eq_harmonic]
      simp only [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      exact le_add_of_nonneg_right (by positivity)

/-- At an integral cutoff, the strict real inequality in `logSum` is exactly
membership in `Finset.range n`. -/
theorem logSum_natCast (B : Set ℕ) (n : ℕ) :
    logSum B (n : ℝ) =
      (by
        classical
        exact ∑ m ∈ Finset.range n, if m ∈ B then ((m : ℕ) : ℝ)⁻¹ else 0) := by
  classical
  simp only [logSum, Nat.ceil_natCast]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m < n := Finset.mem_range.mp hm
  simp [hmn]

/-- A logarithmic counting sum is nonnegative at every real cutoff. -/
theorem logSum_nonneg (B : Set ℕ) (x : ℝ) : 0 ≤ logSum B x := by
  classical
  simp only [logSum]
  exact Finset.sum_nonneg fun m _ ↦ by split_ifs <;> positivity

/-- Dropping membership in `B` can only increase the logarithmic counting
sum. -/
theorem logSum_le_sum_range_inv (B : Set ℕ) (x : ℝ) :
    logSum B x ≤ ∑ m ∈ Finset.range ⌈x⌉₊, ((m : ℕ) : ℝ)⁻¹ := by
  classical
  simp only [logSum]
  apply Finset.sum_le_sum
  intro m hm
  split_ifs
  · exact le_rfl
  · positivity

/-- The exact real-cutoff logarithmic sum is bounded by the harmonic number at
the natural ceiling of the cutoff. -/
theorem logSum_le_harmonic_ceil (B : Set ℕ) (x : ℝ) :
    logSum B x ≤ (harmonic ⌈x⌉₊ : ℝ) :=
  (logSum_le_sum_range_inv B x).trans
    (sum_range_natCast_inv_le_harmonic ⌈x⌉₊)

/-- A convenient logarithmic upper bound valid at every real cutoff. -/
theorem logSum_le_one_add_log_ceil (B : Set ℕ) (x : ℝ) :
    logSum B x ≤ 1 + Real.log (⌈x⌉₊ : ℝ) :=
  (logSum_le_harmonic_ceil B x).trans (harmonic_le_one_add_log ⌈x⌉₊)

/-- The corresponding upper bound at a natural-number cutoff. -/
theorem logSum_natCast_le_one_add_log (B : Set ℕ) (n : ℕ) :
    logSum B (n : ℝ) ≤ 1 + Real.log (n : ℝ) := by
  simpa using logSum_le_one_add_log_ceil B (n : ℝ)

/-- Once the cutoff is at least one, the normalized logarithmic average is
nonnegative. -/
theorem logAverage_nonneg (B : Set ℕ) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ logAverage B x := by
  exact div_nonneg (logSum_nonneg B x) (Real.log_nonneg hx)

/-- Natural cutoffs satisfy the direct harmonic-over-log estimate. -/
theorem logAverage_natCast_le (B : Set ℕ) {n : ℕ} (hn : 2 ≤ n) :
    logAverage B (n : ℝ) ≤
      (1 + Real.log (n : ℝ)) / Real.log (n : ℝ) := by
  rw [logAverage]
  have hn' : (1 : ℝ) < n := by
    exact_mod_cast (show 1 < n by omega)
  apply (div_le_div_iff_of_pos_right (Real.log_pos hn')).2
  exact logSum_natCast_le_one_add_log B n

/-- A simple uniform upper bound for all sufficiently large real cutoffs. -/
theorem logAverage_le_three (B : Set ℕ) {x : ℝ}
    (hx : Real.exp 1 ≤ x) : logAverage B x ≤ 3 := by
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hxone : 1 ≤ x := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp 1
      norm_num at h
      exact h
    linarith
  have hlogx : 1 ≤ Real.log x := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) hx
  have hceil_le : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
    have hceil_lt : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos.le
    linarith
  have hceil_pos : 0 < (⌈x⌉₊ : ℝ) :=
    hxpos.trans_le (Nat.le_ceil x)
  have hlog_ceil : Real.log (⌈x⌉₊ : ℝ) ≤ Real.log (2 * x) :=
    Real.log_le_log hceil_pos hceil_le
  have hlog_two : Real.log (2 : ℝ) ≤ 1 := by
    calc
      Real.log (2 : ℝ) ≤ Real.log (Real.exp 1) :=
        Real.log_le_log (by norm_num) (by
          have h := Real.add_one_le_exp 1
          norm_num at h
          exact h)
      _ = 1 := Real.log_exp 1
  rw [Real.log_mul (by norm_num) hxpos.ne'] at hlog_ceil
  have hsum : logSum B x ≤ 3 * Real.log x := by
    linarith [logSum_le_one_add_log_ceil B x]
  rw [logAverage]
  exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hlogx)).2 (by simpa using hsum)

/-- Every logarithmic average is eventually between zero and three. -/
theorem eventually_logAverage_mem_Icc (B : Set ℕ) :
    ∀ᶠ x in atTop, logAverage B x ∈ Set.Icc (0 : ℝ) 3 := by
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hxone : 1 ≤ x := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp 1
      norm_num at h
      exact h
    linarith
  exact ⟨logAverage_nonneg B hxone, logAverage_le_three B hx⟩

/-- The logarithmic average is eventually bounded above along `atTop`. -/
theorem logAverage_isBoundedUnder_le (B : Set ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (logAverage B) :=
  Filter.isBoundedUnder_of_eventually_le <|
    (eventually_logAverage_mem_Icc B).mono fun _ hx ↦ hx.2

/-- The logarithmic average is eventually bounded below along `atTop`. -/
theorem logAverage_isBoundedUnder_ge (B : Set ℕ) :
    IsBoundedUnder (· ≥ ·) atTop (logAverage B) :=
  Filter.isBoundedUnder_of_eventually_ge <|
    (eventually_logAverage_mem_Icc B).mono fun _ hx ↦ hx.1

end Erdos486
