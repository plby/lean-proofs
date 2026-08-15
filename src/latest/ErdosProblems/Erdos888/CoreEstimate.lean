import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Squarefree
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic
import ErdosProblems.Erdos888.PrimeEstimates

/-!
# Erdős Problem 888: the one-dimensional and squarefree-core sums

This file isolates the analytic assembly in Lemmas 7.1 and 7.2 of the
mathematical proof.  The one-dimensional dyadic estimate is completely
explicit.  For the core estimate we define the exact `(largest prime, old
core)` double sum and prove the small/large-prime splitting lemma.  Its four
hypotheses are the interfaces supplied by the Euler-product and primorial
estimates: a small-prime fiber estimate, a large-prime fiber estimate, a
bounded initial series, and a reciprocal-square tail estimate.

Keeping those inputs as hypotheses makes this module independent of the
particular explicit constants chosen in `PrimeEstimates`.
-/

open Filter
open scoped BigOperators

namespace Erdos888
namespace CoreEstimate

noncomputable section

/-- The regularized logarithmic weight used in the dyadic proof. -/
abbrev logWeight (x : ℝ) : ℝ := lambda x

lemma logWeight_pos_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 < logWeight x := by
  exact lambda_pos hx

/-- The finite one-dimensional sum after writing a dyadic variable as
`X = 2^j · ρ`. -/
def dyadicXSum (A ρ : ℝ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J,
    1 / (((2 : ℝ) ^ j * ρ) * logWeight (A / (2 : ℝ) ^ j))

/-- A general half-logarithm comparison.  If `q² ≤ A`, division by `q`
loses at most a factor two in the regularized logarithmic weight.  This is
also the denominator comparison used in both ranges of the core sum. -/
lemma logWeight_le_two_mul_div {A q : ℝ} (hq : 1 ≤ q) (hqA : q ^ 2 ≤ A) :
    logWeight A ≤ 2 * logWeight (A / q) := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hApos : 0 < A := (sq_pos_of_pos hqpos).trans_le hqA
  have hratio : 1 ≤ A / q ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hqpos)]
    simpa using hqA
  have hlogratio : 0 ≤ Real.log (A / q ^ 2) := Real.log_nonneg hratio
  rw [Real.log_div hApos.ne' (sq_pos_of_pos hqpos).ne', Real.log_pow] at hlogratio
  norm_num at hlogratio
  change lambda A ≤ 2 * lambda (A / q)
  rw [lambda_eq_one_add_log hApos.ne',
    lambda_eq_one_add_log (div_pos hApos hqpos).ne',
    Real.log_div hApos.ne' hqpos.ne']
  linarith

/-- Logarithmic version of `logWeight_le_two_mul_div`, convenient after a
primorial estimate has bounded `log z`. -/
lemma logWeight_le_two_mul_div_of_log_le_half
    {n z : ℝ} (hn : 1 ≤ n) (hz : 1 ≤ z)
    (hlog : Real.log z ≤ Real.log n / 2) :
    logWeight n ≤ 2 * logWeight (n / z) := by
  apply logWeight_le_two_mul_div hz
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  have hzpos : 0 < z := zero_lt_one.trans_le hz
  rw [← Real.log_le_log_iff (sq_pos_of_pos hzpos) hnpos, Real.log_pow]
  norm_num
  linarith

/-- The large-prime denominator comparison in Lemma 7.2.  The size condition
`d r³ ≤ K n` gives `r/K ≤ n/(d r²)`, while `K² ≤ r` loses at most a
factor two in `lambda`. -/
lemma logWeight_nat_le_two_core_denominator
    {K r n d : ℕ} (hK : 1 ≤ K) (hr : K ^ 2 ≤ r) (hd : 1 ≤ d)
    (hsize : d * r ^ 3 ≤ K * n) :
    logWeight r ≤
      2 * logWeight ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)) := by
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : 0 < K := by omega
  have hrposNat : 0 < r := (pow_pos hKpos 2).trans_le hr
  have hrR : (0 : ℝ) < r := by
    exact_mod_cast hrposNat
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hquot : (r : ℝ) / K ≤
      (n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < K)
      (mul_pos hdR (sq_pos_of_pos hrR))]
    have hsizeR : (d : ℝ) * (r : ℝ) ^ 3 ≤ (K : ℝ) * n := by
      exact_mod_cast hsize
    nlinarith
  calc
    logWeight r ≤ 2 * logWeight ((r : ℝ) / K) := by
      apply logWeight_le_two_mul_div hKR
      exact_mod_cast hr
    _ ≤ 2 * logWeight ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)) := by
      gcongr
      exact lambda_mono (div_pos hrR (by positivity)) hquot

/-- Nonemptiness of a block gives enough room to compare the logarithmic
weight at `A / 2^j` with the one at `A`.

The hypothesis is the normalized form of `X ≤ n/(cX)`, namely
`(2^j)^2 ρ ≤ A`, where `A = n/(cρ)`. -/
lemma logWeight_le_two_mul_dyadic
    {A ρ : ℝ} {j : ℕ} (hρ : 1 ≤ ρ)
    (hroom : ((2 : ℝ) ^ j) ^ 2 * ρ ≤ A) :
    logWeight A ≤ 2 * logWeight (A / (2 : ℝ) ^ j) := by
  have hq1 : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  apply logWeight_le_two_mul_div hq1
  exact (le_mul_of_one_le_right (sq_nonneg _) hρ).trans hroom

/-- **Lemma 7.1 (one-dimensional `X`-sum), explicit form.**

The constant `4` is absolute.  The finite range can be any initial range of
dyadic exponents; `hroom` is precisely the normalized nonempty-block
condition. -/
theorem dyadicXSum_le
    {A ρ : ℝ} {J : ℕ} (hA : 1 ≤ A) (hρ : 1 ≤ ρ)
    (hroom : ∀ j < J, ((2 : ℝ) ^ j) ^ 2 * ρ ≤ A) :
    dyadicXSum A ρ J ≤ 4 / (ρ * logWeight A) := by
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hLApos : 0 < logWeight A := logWeight_pos_of_one_le hA
  unfold dyadicXSum
  calc
    (∑ j ∈ Finset.range J,
        1 / (((2 : ℝ) ^ j * ρ) * logWeight (A / (2 : ℝ) ^ j)))
        ≤ ∑ j ∈ Finset.range J,
          (2 / (ρ * logWeight A)) * (1 / 2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have hjJ : j < J := Finset.mem_range.mp hj
      have hq : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) _
      have hlogCompare := logWeight_le_two_mul_dyadic hρ (hroom j hjJ)
      have hAq1 : 1 ≤ A / (2 : ℝ) ^ j := by
        have hroomj := hroom j hjJ
        rw [le_div_iff₀ hq]
        have hq1 : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
        simpa using (show (2 : ℝ) ^ j ≤ A from calc
          (2 : ℝ) ^ j ≤ ((2 : ℝ) ^ j) ^ 2 * ρ := by
            calc
              (2 : ℝ) ^ j ≤ ((2 : ℝ) ^ j) ^ 2 := by
                simpa [pow_two] using
                  (le_mul_of_one_le_right (le_of_lt hq) hq1)
              _ ≤ ((2 : ℝ) ^ j) ^ 2 * ρ := by
                exact le_mul_of_one_le_right (sq_nonneg _) hρ
          _ ≤ A := hroomj)
      have hLAqpos : 0 < logWeight (A / (2 : ℝ) ^ j) :=
        logWeight_pos_of_one_le hAq1
      have hinvLog : 1 / logWeight (A / (2 : ℝ) ^ j) ≤
          2 / logWeight A := by
        rw [div_le_div_iff₀ hLAqpos hLApos]
        simpa using hlogCompare
      have hinvLog' : (logWeight (A / (2 : ℝ) ^ j))⁻¹ ≤
          2 * (logWeight A)⁻¹ := by
        simpa only [one_div, div_eq_mul_inv, one_mul] using hinvLog
      have hpowInv : (((2 : ℝ) ^ j) * ρ)⁻¹ =
          ρ⁻¹ * (1 / 2 : ℝ) ^ j := by
        rw [mul_inv_rev, one_div, inv_pow]
      calc
        1 / (((2 : ℝ) ^ j * ρ) * logWeight (A / (2 : ℝ) ^ j)) =
            (ρ⁻¹ * (1 / 2 : ℝ) ^ j) *
              (logWeight (A / (2 : ℝ) ^ j))⁻¹ := by
              rw [one_div, mul_inv_rev, hpowInv]
              ring
        _
            ≤ ρ⁻¹ * (1 / 2 : ℝ) ^ j *
                (2 * (logWeight A)⁻¹) := by
              simpa [one_div] using
                (mul_le_mul_of_nonneg_left hinvLog' (by positivity :
                  0 ≤ ρ⁻¹ * (1 / 2 : ℝ) ^ j))
        _ = (2 * (ρ * logWeight A)⁻¹) * (1 / 2 : ℝ) ^ j := by
              rw [mul_inv_rev]
              ring
    _ ≤ (2 / (ρ * logWeight A)) * 2 := by
      rw [← Finset.mul_sum]
      gcongr
      have hg := geom_sum_Ico_le_of_lt_one (K := ℝ) (m := 0) (n := J)
        (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      norm_num at hg ⊢
      simpa [one_div, inv_pow] using hg
    _ = 4 / (ρ * logWeight A) := by ring

/-! ## The squarefree-core pair sum -/

/-- The reciprocal mass of squarefree `r`-smooth old cores in the exact
range arising after extracting the largest prime `r`.

The upper endpoint `K*n/r^3` is the integer form of `d r^3 ≤ K n`.
The denominator is the one in equation (7.7) of the mathematical proof. -/
def smoothCoreFiber (K n r : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (K * n / r ^ 3),
    if Squarefree d ∧ ∀ p ∈ d.primeFactors, p < r then
      1 / ((d : ℝ) * logWeight ((n : ℝ) / ((d : ℝ) * (r : ℝ) ^ 2)))
    else 0

/-- The nontrivial (`c > 1`) part of the squarefree-core majorant, reindexed
as `c = d*r`, where `r` is the largest prime factor. -/
def squarefreeCorePairSum (K n : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 (K * n),
    if r.Prime then (1 / (r : ℝ) ^ 2) * smoothCoreFiber K n r else 0

/-- A convenient abbreviation for the positive series occurring in the
small-prime range. -/
def coreSeriesTerm (r : ℕ) : ℝ :=
  logWeight r / (r : ℝ) ^ 2

lemma coreSeriesTerm_nonneg (r : ℕ) : 0 ≤ coreSeriesTerm r := by
  by_cases hr : r = 0
  · simp [hr, coreSeriesTerm, lambda]
  · exact div_nonneg (lambda_pos (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr)).le
      (sq_nonneg _)

/-- The logarithmically weighted reciprocal-square series converges.  This
is the series budget used in the small-largest-prime range of Lemma 7.2. -/
theorem summable_coreSeriesTerm : Summable coreSeriesTerm := by
  have hcomp : ∀ r : ℕ, ‖coreSeriesTerm r‖ ≤
      1 / (r : ℝ) ^ 2 + 2 * (r : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro r
    by_cases hr0 : r = 0
    · subst r
      norm_num [coreSeriesTerm, lambda]
    · have hr : 0 < r := Nat.pos_of_ne_zero hr0
      have hrR : (0 : ℝ) < r := by exact_mod_cast hr
      have hlog := Real.log_natCast_le_rpow_div r
        (show (0 : ℝ) < 1 / 2 by norm_num)
      have hlam : logWeight r ≤ 1 + 2 * (r : ℝ) ^ (1 / 2 : ℝ) := by
        change lambda (r : ℝ) ≤ _
        rw [lambda_eq_one_add_log (by positivity)]
        norm_num at hlog ⊢
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (coreSeriesTerm_nonneg r)]
      calc
        coreSeriesTerm r ≤
            (1 + 2 * (r : ℝ) ^ (1 / 2 : ℝ)) / (r : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hlam (sq_nonneg _)
        _ = 1 / (r : ℝ) ^ 2 + 2 * (r : ℝ) ^ (-(3 / 2 : ℝ)) := by
          rw [add_div, mul_div_assoc]
          congr 1
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_sub hrR]
          norm_num
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun r ↦ norm_nonneg _) hcomp ?_
  exact (Real.summable_one_div_nat_pow.2 (by norm_num)).add
    ((Real.summable_nat_rpow.2 (by norm_num)).mul_left 2)

/-- A fixed uniform budget for every finite initial segment of the series in
the small-prime range. -/
theorem exists_uniform_coreSeries_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℕ,
      (∑ r ∈ Finset.Ico 2 R, coreSeriesTerm r) ≤ B := by
  refine ⟨∑' r : ℕ, coreSeriesTerm r,
    tsum_nonneg fun r ↦ coreSeriesTerm_nonneg r, ?_⟩
  intro R
  exact summable_coreSeriesTerm.sum_le_tsum (Finset.Ico 2 R)
    (fun r hr ↦ coreSeriesTerm_nonneg r)

/-- A single reciprocal square is bounded by the telescoping majorant
`1/(r-1) - 1/r`. -/
lemma reciprocalSquare_le_telescope {r : ℕ} (hr : 2 ≤ r) :
    1 / (r : ℝ) ^ 2 ≤ 1 / ((r - 1 : ℕ) : ℝ) - 1 / (r : ℝ) := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hrm : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  rw [hrm]
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have hrm0 : (r : ℝ) - 1 ≠ 0 := by linarith
  have heq : 1 / ((r : ℝ) - 1) - 1 / (r : ℝ) =
      1 / (((r : ℝ) - 1) * r) := by
    field_simp [hr0, hrm0]
    ring
  rw [heq]
  apply one_div_le_one_div_of_le
    (mul_pos (by linarith : (0 : ℝ) < r - 1) (by positivity : (0 : ℝ) < r))
  nlinarith

/-- The finite reciprocal-square tail has the explicit `2/R` bound. -/
theorem reciprocalSquare_Icc_le (R N : ℕ) (hR : 2 ≤ R) :
    (∑ r ∈ Finset.Icc R N, 1 / (r : ℝ) ^ 2) ≤ 2 / (R : ℝ) := by
  by_cases hRN : R ≤ N
  · have htel : (∑ r ∈ Finset.Icc R N,
        (1 / ((r - 1 : ℕ) : ℝ) - 1 / (r : ℝ))) =
        1 / ((R - 1 : ℕ) : ℝ) - 1 / (N : ℝ) := by
      induction N, hRN using Nat.le_induction with
      | base => simp
      | succ N hRN ih =>
          rw [Finset.sum_Icc_succ_top (by omega), ih]
          simp only [Nat.add_sub_cancel]
          ring
    calc
      (∑ r ∈ Finset.Icc R N, 1 / (r : ℝ) ^ 2) ≤
          ∑ r ∈ Finset.Icc R N,
            (1 / ((r - 1 : ℕ) : ℝ) - 1 / (r : ℝ)) := by
              apply Finset.sum_le_sum
              intro r hr
              exact reciprocalSquare_le_telescope
                (hR.trans (Finset.mem_Icc.mp hr).1)
      _ = 1 / ((R - 1 : ℕ) : ℝ) - 1 / (N : ℝ) := htel
      _ ≤ 1 / ((R - 1 : ℕ) : ℝ) := by
        have : 0 ≤ 1 / (N : ℝ) := by positivity
        linarith
      _ ≤ 2 / (R : ℝ) := by
        have hRR : (2 : ℝ) ≤ R := by exact_mod_cast hR
        have hRm : ((R - 1 : ℕ) : ℝ) = (R : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ R), Nat.cast_one]
        rw [hRm]
        rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < R - 1)
          (by positivity : (0 : ℝ) < R)]
        nlinarith
  · have hempty : Finset.Icc R N = ∅ := Finset.Icc_eq_empty (by omega)
    simp [hempty, div_nonneg]

/-- **Lemma 7.2 (core sum), explicit split form.**

`R` is the cutoff (eventually a small constant times `log n`).  The two fiber
bounds are exactly what the primorial/Euler-product argument supplies.  The
last two hypotheses record, in finite explicit form, convergence of
`∑ logWeight(r)/r²` and the `O(1/R)` reciprocal-square tail. -/
theorem squarefreeCorePairSum_le
    {K n R : ℕ} {a b B D E : ℝ}
    (hR : 2 ≤ R)
    (hRN : R ≤ K * n)
    (hlog : logWeight n ≤ E * R)
    (hlogpos : 0 < logWeight n)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsmall : ∀ r ∈ Finset.Ico 2 R, r.Prime →
      (1 / (r : ℝ) ^ 2) * smoothCoreFiber K n r ≤
        a * coreSeriesTerm r / logWeight n)
    (hlarge : ∀ r ∈ Finset.Icc R (K * n), r.Prime →
      (1 / (r : ℝ) ^ 2) * smoothCoreFiber K n r ≤
        b / (r : ℝ) ^ 2)
    (hseries : (∑ r ∈ Finset.Ico 2 R, coreSeriesTerm r) ≤ B)
    (htail : (∑ r ∈ Finset.Icc R (K * n), 1 / (r : ℝ) ^ 2) ≤ D / R) :
    squarefreeCorePairSum K n ≤ (a * B + b * D * E) / logWeight n := by
  classical
  have hsplit : Finset.Icc 2 (K * n) =
      Finset.Ico 2 R ∪ Finset.Icc R (K * n) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]
    omega
  rw [squarefreeCorePairSum, hsplit, Finset.sum_union]
  · calc
      (∑ r ∈ Finset.Ico 2 R,
          if r.Prime then (1 / (r : ℝ) ^ 2) * smoothCoreFiber K n r else 0) +
          (∑ r ∈ Finset.Icc R (K * n),
            if r.Prime then (1 / (r : ℝ) ^ 2) * smoothCoreFiber K n r else 0)
          ≤ (∑ r ∈ Finset.Ico 2 R,
              a * coreSeriesTerm r / logWeight n) +
            (∑ r ∈ Finset.Icc R (K * n), b / (r : ℝ) ^ 2) := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro r hr
          split_ifs with hp
          · exact hsmall r hr hp
          · have hr1 : (1 : ℝ) ≤ r := by
              exact_mod_cast (by
                have := (Finset.mem_Ico.mp hr).1
                omega : 1 ≤ r)
            have hlr : 0 < logWeight r := logWeight_pos_of_one_le hr1
            exact div_nonneg (mul_nonneg ha (by
              rw [coreSeriesTerm]
              exact div_nonneg hlr.le (sq_nonneg _))) hlogpos.le
        · apply Finset.sum_le_sum
          intro r hr
          split_ifs with hp
          · exact hlarge r hr hp
          · positivity
      _ = a * (∑ r ∈ Finset.Ico 2 R, coreSeriesTerm r) / logWeight n +
            b * (∑ r ∈ Finset.Icc R (K * n), 1 / (r : ℝ) ^ 2) := by
          simp only [div_eq_mul_inv]
          rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
          simp only [one_mul]
      _ ≤ a * B / logWeight n + b * (D / R) := by
          gcongr
      _ ≤ (a * B + b * D * E) / logWeight n := by
          have hRpos : (0 : ℝ) < R := by positivity
          have htailNonneg : 0 ≤ D / (R : ℝ) := by
            refine (Finset.sum_nonneg (fun r hr ↦ ?_)).trans htail
            positivity
          have hD : 0 ≤ D := by
            rcases div_nonneg_iff.mp htailNonneg with h | h
            · exact h.1
            · exfalso
              linarith [h.2]
          have hcut : D / (R : ℝ) ≤ D * E / logWeight n := by
            rw [div_le_div_iff₀ hRpos hlogpos]
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hlog hD
          rw [add_div]
          apply add_le_add le_rfl
          calc
            b * (D / (R : ℝ)) ≤ b * (D * E / logWeight n) :=
              mul_le_mul_of_nonneg_left hcut hb
            _ = b * D * E / logWeight n := by ring
  · exact Finset.disjoint_left.mpr fun r hrSmall hrLarge ↦ by
      have := (Finset.mem_Ico.mp hrSmall).2
      have := (Finset.mem_Icc.mp hrLarge).1
      omega

/-- Eventual wrapper for `squarefreeCorePairSum_le`.  This is the form used
when a fixed collection of constants has been obtained from prime estimates
and the cutoff `R n` has been chosen proportional to `log n`. -/
theorem eventually_squarefreeCorePairSum_le
    {K : ℕ} {R : ℕ → ℕ} {a b B D E : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hR : ∀ᶠ n : ℕ in atTop, 2 ≤ R n)
    (hRN : ∀ᶠ n : ℕ in atTop, R n ≤ K * n)
    (hlogpos : ∀ᶠ n : ℕ in atTop, 0 < logWeight n)
    (hlog : ∀ᶠ n : ℕ in atTop, logWeight n ≤ E * R n)
    (hsmall : ∀ᶠ n : ℕ in atTop, ∀ r ∈ Finset.Ico 2 (R n), r.Prime →
      (1 / (r : ℝ) ^ 2) * smoothCoreFiber K n r ≤
        a * coreSeriesTerm r / logWeight n)
    (hlarge : ∀ᶠ n : ℕ in atTop, ∀ r ∈ Finset.Icc (R n) (K * n), r.Prime →
      (1 / (r : ℝ) ^ 2) * smoothCoreFiber K n r ≤ b / (r : ℝ) ^ 2)
    (hseries : ∀ᶠ n : ℕ in atTop,
      (∑ r ∈ Finset.Ico 2 (R n), coreSeriesTerm r) ≤ B)
    (htail : ∀ᶠ n : ℕ in atTop,
      (∑ r ∈ Finset.Icc (R n) (K * n), 1 / (r : ℝ) ^ 2) ≤ D / R n) :
    ∀ᶠ n : ℕ in atTop,
      squarefreeCorePairSum K n ≤ (a * B + b * D * E) / logWeight n := by
  filter_upwards [hR, hRN, hlogpos, hlog, hsmall, hlarge, hseries, htail]
    with n hnR hnRN hnlogpos hnlog hnsmall hnlarge hnseries hntail
  exact squarefreeCorePairSum_le hnR hnRN hnlog hnlogpos ha hb
    hnsmall hnlarge hnseries hntail

/-- Closing interface for the core estimate after only the two arithmetic
fiber bounds and the cutoff comparison have been proved.  The convergent
series and reciprocal-square tail budgets are discharged internally. -/
theorem eventually_squarefreeCorePairSum_le_of_fiber_bounds
    {K : ℕ} {R : ℕ → ℕ} {a b E : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hE : 0 ≤ E)
    (hR : ∀ᶠ n : ℕ in atTop, 2 ≤ R n)
    (hRN : ∀ᶠ n : ℕ in atTop, R n ≤ K * n)
    (hlogpos : ∀ᶠ n : ℕ in atTop, 0 < logWeight n)
    (hlog : ∀ᶠ n : ℕ in atTop, logWeight n ≤ E * R n)
    (hsmall : ∀ᶠ n : ℕ in atTop, ∀ r ∈ Finset.Ico 2 (R n), r.Prime →
      (1 / (r : ℝ) ^ 2) * smoothCoreFiber K n r ≤
        a * coreSeriesTerm r / logWeight n)
    (hlarge : ∀ᶠ n : ℕ in atTop, ∀ r ∈ Finset.Icc (R n) (K * n), r.Prime →
      (1 / (r : ℝ) ^ 2) * smoothCoreFiber K n r ≤ b / (r : ℝ) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      squarefreeCorePairSum K n ≤ C / logWeight n := by
  obtain ⟨B, hB, hseries⟩ := exists_uniform_coreSeries_bound
  refine ⟨a * B + b * 2 * E,
    add_nonneg (mul_nonneg ha hB) (mul_nonneg (mul_nonneg hb (by norm_num)) hE), ?_⟩
  apply eventually_squarefreeCorePairSum_le ha hb hR hRN hlogpos hlog hsmall hlarge
  · exact Filter.Eventually.of_forall fun n ↦ hseries (R n)
  · filter_upwards [hR] with n hnR
    exact reciprocalSquare_Icc_le (R n) (K * n) hnR

end
end CoreEstimate
end Erdos888
