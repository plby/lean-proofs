import ErdosProblems.Erdos1161.Basic
import Mathlib.Analysis.SpecificLimits.Normed

open Asymptotics

/-!
# Least-common-multiple bounds for Erdős Problem 1161

This file contains the elementary arithmetic estimate which makes Beker's
admissible remainders negligible compared with the degree.  The definitions
specific to Problem 1161 are imported from `Basic` below once that file is
available; the first group of lemmas is stated in the `Nat` namespace because
it is useful independently of permutations.
-/

namespace Nat

/-- Every positive integer at most `n` divides `lcmUpto n`. -/
theorem dvd_lcmUpto {d n : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) : d ∣ lcmUpto n := by
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hd, hdn⟩)

/-- `lcmUpto` is monotone for divisibility. -/
theorem lcmUpto_mono_dvd {a b : ℕ} (hab : a ≤ b) : lcmUpto a ∣ lcmUpto b := by
  rw [lcmUpto, Finset.lcm_dvd_iff]
  intro d hd
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hab⟩)

/-- Numerical monotonicity of `lcmUpto`. -/
theorem lcmUpto_mono {a b : ℕ} (hab : a ≤ b) : lcmUpto a ≤ lcmUpto b :=
  le_of_dvd (lcmUpto_pos b) (lcmUpto_mono_dvd hab)

/-- Every fixed quadratic multiple is eventually smaller than `2 ^ r`.
This is the only exponential-versus-polynomial fact needed below. -/
theorem eventually_const_mul_mul_succ_lt_two_pow (C : ℕ) :
    ∀ᶠ r : ℕ in Filter.atTop, C * r * (r + 1) < 2 ^ r := by
  by_cases hC : C = 0
  · simp [hC]
  have hexp : (fun r : ℕ ↦ (r : ℝ) ^ 2) =o[Filter.atTop]
      (fun r : ℕ ↦ (2 : ℝ) ^ r) :=
    isLittleO_pow_const_const_pow_of_one_lt 2 (by norm_num)
  have hbound := (isLittleO_iff_nat_mul_le.mp hexp) (4 * C)
  filter_upwards [hbound, Filter.eventually_gt_atTop 0] with r hr hrpos
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (r : ℝ)),
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ r)] at hr
  norm_num only [Nat.cast_mul] at hr
  have hr_nat : 4 * C * r ^ 2 ≤ 2 ^ r := by
    exact_mod_cast hr
  have hCrpos : 0 < C * r := Nat.mul_pos (Nat.pos_of_ne_zero hC) hrpos
  calc
    C * r * (r + 1) ≤ 2 * C * r ^ 2 := by nlinarith
    _ < 4 * C * r ^ 2 := by nlinarith
    _ ≤ 2 ^ r := hr_nat

/-- The basic LCM estimate.  It is deliberately stated without reference to
the problem-specific finset, so it can also be used when admissibility has
been unpacked into its two defining hypotheses. -/
theorem two_pow_le_mul_sub_of_lcmUpto_dvd {n r : ℕ} (hrn : r < n)
    (hdvd : lcmUpto r ∣ n - r) :
    2 ^ r ≤ (r + 1) * (n - r) := by
  calc
    2 ^ r ≤ (r + 1) * lcmUpto r := Chebyshev.two_pow_le_mul_lcmUpto r
    _ ≤ (r + 1) * (n - r) := by
      gcongr
      exact le_of_dvd (Nat.sub_pos_of_lt hrn) hdvd

/-- Two admissible remainders have a gap divisible by the LCM belonging to
the smaller remainder. -/
theorem lcmUpto_dvd_remainder_gap {n r s : ℕ} (hrs : r ≤ s) (hsn : s ≤ n)
    (hrdvd : lcmUpto r ∣ n - r) (hsdvd : lcmUpto s ∣ n - s) :
    lcmUpto r ∣ s - r := by
  have hsmall : lcmUpto r ∣ n - s := (lcmUpto_mono_dvd hrs).trans hsdvd
  have hsub : lcmUpto r ∣ (n - r) - (n - s) := Nat.dvd_sub hrdvd hsmall
  rw [show (n - r) - (n - s) = s - r by omega] at hsub
  exact hsub

/-- Distinct admissible remainders beyond `1` differ by at least two. -/
theorem two_le_remainder_gap {n r s : ℕ} (hrtwo : 2 ≤ r) (hrs : r < s)
    (hsn : s ≤ n) (hrdvd : lcmUpto r ∣ n - r)
    (hsdvd : lcmUpto s ∣ n - s) :
    2 ≤ s - r := by
  have hlcm : lcmUpto r ∣ s - r :=
    lcmUpto_dvd_remainder_gap hrs.le hsn hrdvd hsdvd
  have htwo : 2 ∣ lcmUpto r := dvd_lcmUpto (by omega) hrtwo
  exact le_of_dvd (Nat.sub_pos_of_lt hrs) (htwo.trans hlcm)

/-- Once a fixed quadratic multiple lies below `2 ^ r`, admissibility forces
the stronger linear inequality `C * r < n`. -/
theorem const_mul_lt_of_lcmUpto_dvd {C n r : ℕ} (hrn : r < n)
    (hdvd : lcmUpto r ∣ n - r)
    (hpoly : C * r * (r + 1) < 2 ^ r) :
    C * r < n := by
  by_contra hnot
  have hnle : n ≤ C * r := Nat.le_of_not_gt hnot
  have hpow := two_pow_le_mul_sub_of_lcmUpto_dvd hrn hdvd
  have hle : (r + 1) * (n - r) ≤ C * r * (r + 1) := by
    calc
      (r + 1) * (n - r) ≤ (r + 1) * n :=
        Nat.mul_le_mul_left _ (Nat.sub_le n r)
      _ ≤ (r + 1) * (C * r) := Nat.mul_le_mul_left _ hnle
      _ = C * r * (r + 1) := by ac_rfl
  exact (not_lt_of_ge (hpow.trans hle)) hpoly

/-- Uniform quantified form of `r = o(n)` for all pairs satisfying the
admissible-remainder conditions. -/
theorem eventually_const_mul_lt_of_lcmUpto_dvd (C : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ r : ℕ, r < n → lcmUpto r ∣ n - r → C * r < n := by
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    (eventually_const_mul_mul_succ_lt_two_pow C)
  refine Filter.eventually_atTop.mpr ⟨C * R + 1, ?_⟩
  intro n hn r hrn hdvd
  by_cases hRr : R ≤ r
  · exact const_mul_lt_of_lcmUpto_dvd hrn hdvd (hR r hRr)
  · have hmul : C * r ≤ C * R := Nat.mul_le_mul_left C (Nat.le_of_lt (lt_of_not_ge hRr))
    omega

/-- In particular, every admissible remainder is eventually less than half
the degree, uniformly over all admissible remainders. -/
theorem eventually_two_mul_lt_of_lcmUpto_dvd :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ r : ℕ, r < n → lcmUpto r ∣ n - r → 2 * r < n :=
  eventually_const_mul_lt_of_lcmUpto_dvd 2

/-- Equivalent convenient form: the complementary order `n-r` is
eventually greater than half of `n`. -/
theorem eventually_lt_two_mul_sub_of_lcmUpto_dvd :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ r : ℕ, r < n → lcmUpto r ∣ n - r → n < 2 * (n - r) := by
  filter_upwards [eventually_two_mul_lt_of_lcmUpto_dvd] with n hn r hrn hdvd
  have := hn r hrn hdvd
  omega

/-- Any sequence of admissible remainders is little-o of the degree. -/
theorem admissible_remainder_sequence_isLittleO (r : ℕ → ℕ)
    (hrlt : ∀ n, r n < n)
    (hrdvd : ∀ n, lcmUpto (r n) ∣ n - r n) :
    (fun n : ℕ ↦ (r n : ℝ)) =o[Filter.atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  rw [isLittleO_iff_nat_mul_le]
  intro C
  filter_upwards [eventually_const_mul_lt_of_lcmUpto_dvd C] with n hn
  have hnat : C * r n ≤ n :=
    (hn (r n) (hrlt n) (hrdvd n)).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r n : ℝ)),
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)),
    ← Nat.cast_mul, Nat.cast_le]
  exact hnat

/-- Removing an admissible remainder does not change the degree
asymptotically. -/
theorem sub_admissible_remainder_sequence_isEquivalent (r : ℕ → ℕ)
    (hrlt : ∀ n, r n < n)
    (hrdvd : ∀ n, lcmUpto (r n) ∣ n - r n) :
    (fun n : ℕ ↦ ((n - r n : ℕ) : ℝ)) ~[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  have hsmall := admissible_remainder_sequence_isLittleO r hrlt hrdvd
  have hreal : (fun n : ℕ ↦ (n : ℝ) - (r n : ℝ)) ~[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) :=
    (IsEquivalent.refl : (fun n : ℕ ↦ (n : ℝ)) ~[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ))).sub_isLittleO hsmall
  apply hreal.congr_left
  filter_upwards [] with n
  exact (Nat.cast_sub (Nat.le_of_lt (hrlt n)) :
    ((n - r n : ℕ) : ℝ) = (n : ℝ) - (r n : ℝ)).symm

/-- Eventual-hypothesis version of
`admissible_remainder_sequence_isLittleO`.  This is the convenient form for
sequences indexed by all naturals, since there is no remainder below degree
zero. -/
theorem admissible_remainder_sequence_isLittleO_eventually (r : ℕ → ℕ)
    (hr : ∀ᶠ n : ℕ in Filter.atTop,
      r n < n ∧ lcmUpto (r n) ∣ n - r n) :
    (fun n : ℕ ↦ (r n : ℝ)) =o[Filter.atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  rw [isLittleO_iff_nat_mul_le]
  intro C
  filter_upwards [eventually_const_mul_lt_of_lcmUpto_dvd C, hr] with n hn hnr
  have hnat : C * r n ≤ n := (hn (r n) hnr.1 hnr.2).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r n : ℝ)),
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)),
    ← Nat.cast_mul, Nat.cast_le]
  exact hnat

/-- Eventual-hypothesis version of the complementary-order equivalence. -/
theorem sub_admissible_remainder_sequence_isEquivalent_eventually (r : ℕ → ℕ)
    (hr : ∀ᶠ n : ℕ in Filter.atTop,
      r n < n ∧ lcmUpto (r n) ∣ n - r n) :
    (fun n : ℕ ↦ ((n - r n : ℕ) : ℝ)) ~[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  have hsmall := admissible_remainder_sequence_isLittleO_eventually r hr
  have hreal : (fun n : ℕ ↦ (n : ℝ) - (r n : ℝ)) ~[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) :=
    (IsEquivalent.refl : (fun n : ℕ ↦ (n : ℝ)) ~[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ))).sub_isLittleO hsmall
  apply hreal.congr_left
  filter_upwards [hr] with n hnr
  exact (Nat.cast_sub hnr.1.le :
    ((n - r n : ℕ) : ℝ) = (n : ℝ) - (r n : ℝ)).symm

end Nat

namespace Erdos1161

/-! ## The bounds in the `K_n` parametrization -/

/-- Membership in `K_n` forces `r < n`. -/
theorem admissibleRemainder_lt {n r : ℕ} (hr : r ∈ admissibleRemainders n) :
    r < n :=
  (mem_admissibleRemainders_iff.mp hr).1

/-- Membership in `K_n` supplies the defining LCM divisibility. -/
theorem lcmUpto_dvd_sub_of_mem_admissibleRemainders {n r : ℕ}
    (hr : r ∈ admissibleRemainders n) :
    Nat.lcmUpto r ∣ n - r :=
  (mem_admissibleRemainders_iff.mp hr).2

/-- For an admissible remainder, `lcmUpto r ≤ n-r`. -/
theorem lcmUpto_le_sub_of_mem_admissibleRemainders {n r : ℕ}
    (hr : r ∈ admissibleRemainders n) :
    Nat.lcmUpto r ≤ n - r := by
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt (admissibleRemainder_lt hr))
    (lcmUpto_dvd_sub_of_mem_admissibleRemainders hr)

/-- A cruder bound sometimes convenient for monotonicity arguments. -/
theorem lcmUpto_le_of_mem_admissibleRemainders {n r : ℕ}
    (hr : r ∈ admissibleRemainders n) :
    Nat.lcmUpto r ≤ n :=
  (lcmUpto_le_sub_of_mem_admissibleRemainders hr).trans (Nat.sub_le n r)

/-- The binomial/Chebyshev bound specialized to `r ∈ K_n`. -/
theorem two_pow_le_mul_sub_of_mem_admissibleRemainders {n r : ℕ}
    (hr : r ∈ admissibleRemainders n) :
    2 ^ r ≤ (r + 1) * (n - r) :=
  Nat.two_pow_le_mul_sub_of_lcmUpto_dvd (admissibleRemainder_lt hr)
    (lcmUpto_dvd_sub_of_mem_admissibleRemainders hr)

/-- A denominator-free weakening of the preceding estimate. -/
theorem two_pow_le_mul_of_mem_admissibleRemainders {n r : ℕ}
    (hr : r ∈ admissibleRemainders n) :
    2 ^ r ≤ (r + 1) * n :=
  (two_pow_le_mul_sub_of_mem_admissibleRemainders hr).trans
    (Nat.mul_le_mul_left (r + 1) (Nat.sub_le n r))

/-- If `r ≤ s` both belong to `K_n`, then `lcmUpto r ∣ s-r`. -/
theorem lcmUpto_dvd_admissibleRemainder_gap {n r s : ℕ}
    (hr : r ∈ admissibleRemainders n) (hs : s ∈ admissibleRemainders n)
    (hrs : r ≤ s) :
    Nat.lcmUpto r ∣ s - r := by
  exact Nat.lcmUpto_dvd_remainder_gap hrs (admissibleRemainder_lt hs).le
    (lcmUpto_dvd_sub_of_mem_admissibleRemainders hr)
    (lcmUpto_dvd_sub_of_mem_admissibleRemainders hs)

/-- Distinct admissible remainders `r < s`, with `r ≥ 2`, differ by at
least two. -/
theorem two_le_sub_of_mem_admissibleRemainders {n r s : ℕ}
    (hr : r ∈ admissibleRemainders n) (hs : s ∈ admissibleRemainders n)
    (hrtwo : 2 ≤ r) (hrs : r < s) :
    2 ≤ s - r := by
  exact Nat.two_le_remainder_gap hrtwo hrs (admissibleRemainder_lt hs).le
    (lcmUpto_dvd_sub_of_mem_admissibleRemainders hr)
    (lcmUpto_dvd_sub_of_mem_admissibleRemainders hs)

/-- Uniform little-o bound in quantified natural-number form. -/
theorem eventually_const_mul_admissibleRemainder_lt (C : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ r ∈ admissibleRemainders n, C * r < n := by
  filter_upwards [Nat.eventually_const_mul_lt_of_lcmUpto_dvd C] with n hn r hr
  exact hn r (admissibleRemainder_lt hr)
    (lcmUpto_dvd_sub_of_mem_admissibleRemainders hr)

/-- Every `r ∈ K_n` is eventually less than half of `n`, uniformly in
`r`. -/
theorem eventually_two_mul_admissibleRemainder_lt :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ r ∈ admissibleRemainders n, 2 * r < n :=
  eventually_const_mul_admissibleRemainder_lt 2

/-- Consequently every complementary candidate order `n-r` is eventually
strictly greater than half the degree. -/
theorem eventually_lt_two_mul_sub_admissibleRemainder :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ r ∈ admissibleRemainders n, n < 2 * (n - r) := by
  filter_upwards [eventually_two_mul_admissibleRemainder_lt] with n hn r hr
  have := hn r hr
  omega

/-- A selected sequence from `K_n` is `o(n)`. -/
theorem admissibleRemainder_sequence_isLittleO (r : ℕ → ℕ)
    (hr : ∀ᶠ n : ℕ in Filter.atTop, r n ∈ admissibleRemainders n) :
    (fun n : ℕ ↦ (r n : ℝ)) =o[Filter.atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  apply Nat.admissible_remainder_sequence_isLittleO_eventually r
  filter_upwards [hr] with n hnr
  exact mem_admissibleRemainders_iff.mp hnr

/-- Accordingly, `n-r(n) ~ n` for every selected admissible sequence. -/
theorem sub_admissibleRemainder_sequence_isEquivalent (r : ℕ → ℕ)
    (hr : ∀ᶠ n : ℕ in Filter.atTop, r n ∈ admissibleRemainders n) :
    (fun n : ℕ ↦ ((n - r n : ℕ) : ℝ)) ~[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  apply Nat.sub_admissible_remainder_sequence_isEquivalent_eventually r
  filter_upwards [hr] with n hnr
  exact mem_admissibleRemainders_iff.mp hnr

/-- The largest admissible remainder itself is `o(n)`. -/
theorem largestAdmissibleRemainder_isLittleO :
    (fun n : ℕ ↦ (largestAdmissibleRemainder n : ℝ)) =o[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  apply admissibleRemainder_sequence_isLittleO largestAdmissibleRemainder
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact largestAdmissibleRemainder_mem hn

/-- Hence the least Beker order, written as `n - max K_n`, is asymptotic
to `n`. -/
theorem sub_largestAdmissibleRemainder_isEquivalent :
    (fun n : ℕ ↦ ((n - largestAdmissibleRemainder n : ℕ) : ℝ)) ~[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  apply sub_admissibleRemainder_sequence_isEquivalent largestAdmissibleRemainder
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact largestAdmissibleRemainder_mem hn

end Erdos1161
