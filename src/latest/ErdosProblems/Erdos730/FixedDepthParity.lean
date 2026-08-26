/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import Mathlib

/-!
# Erdős 730: a character-free fixed-depth digit-parity estimate

This file isolates a finite combinatorial shadow of the fixed-depth Fourier
step in the positive-density proof.  Suppose an independent base-`p` digit
has `marked` possible values which toggle a parity bit and `unmarked` possible
values which preserve it.  `digitParityCounts marked unmarked d` is the exact
two-state recurrence for the number of length-`d` strings ending in even and
odd parity.

For the half-digit alphabet used in the Erdős 730 argument, `p = 2*H-1`,
`marked = H`, and `unmarked = H-1`.  The two parity classes then differ by
exactly one string at every depth.  In particular the doubled even count has
absolute error exactly `1` from the uniform main term `p^d`; after
normalization the error is exactly `1/(2*p^d)`.

This is deliberately character-free: it is the order-two finite Fourier
calculation written as an exact integer recurrence.  It does not assert the
quadratic incomplete-sum estimate of Lemma 2 in the paper proof.
-/

namespace Erdos730

/-- Exact even/odd counts for `d` independent digits.  A marked digit toggles
the parity state, while an unmarked digit preserves it. -/
def digitParityCounts (marked unmarked : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | d + 1 =>
      let previous := digitParityCounts marked unmarked d
      (unmarked * previous.1 + marked * previous.2,
        marked * previous.1 + unmarked * previous.2)

/-- Number of digit strings with even marked-digit parity. -/
def evenDigitParityCount (marked unmarked d : ℕ) : ℕ :=
  (digitParityCounts marked unmarked d).1

/-- Number of digit strings with odd marked-digit parity. -/
def oddDigitParityCount (marked unmarked d : ℕ) : ℕ :=
  (digitParityCounts marked unmarked d).2

@[simp] theorem evenDigitParityCount_zero (marked unmarked : ℕ) :
    evenDigitParityCount marked unmarked 0 = 1 := rfl

@[simp] theorem oddDigitParityCount_zero (marked unmarked : ℕ) :
    oddDigitParityCount marked unmarked 0 = 0 := rfl

@[simp] theorem evenDigitParityCount_succ (marked unmarked d : ℕ) :
    evenDigitParityCount marked unmarked (d + 1) =
      unmarked * evenDigitParityCount marked unmarked d +
        marked * oddDigitParityCount marked unmarked d := by
  rfl

@[simp] theorem oddDigitParityCount_succ (marked unmarked d : ℕ) :
    oddDigitParityCount marked unmarked (d + 1) =
      marked * evenDigitParityCount marked unmarked d +
        unmarked * oddDigitParityCount marked unmarked d := by
  rfl

/-- The two parity classes partition all `(marked + unmarked)^d` strings. -/
theorem digitParityCounts_total (marked unmarked d : ℕ) :
    evenDigitParityCount marked unmarked d +
        oddDigitParityCount marked unmarked d =
      (marked + unmarked) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [evenDigitParityCount_succ, oddDigitParityCount_succ, pow_succ]
      calc
        unmarked * evenDigitParityCount marked unmarked d +
              marked * oddDigitParityCount marked unmarked d +
            (marked * evenDigitParityCount marked unmarked d +
              unmarked * oddDigitParityCount marked unmarked d) =
            (marked + unmarked) *
              (evenDigitParityCount marked unmarked d +
                oddDigitParityCount marked unmarked d) := by ring
        _ = (marked + unmarked) * (marked + unmarked) ^ d := by rw [ih]
        _ = (marked + unmarked) ^ d * (marked + unmarked) := by ring

/-- The signed parity imbalance is the `d`-th power of the one-digit
imbalance.  This is the character-free form of the nontrivial order-two
Fourier coefficient. -/
theorem digitParityCounts_intDifference (marked unmarked d : ℕ) :
    (evenDigitParityCount marked unmarked d : ℤ) -
        oddDigitParityCount marked unmarked d =
      ((unmarked : ℤ) - marked) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [evenDigitParityCount_succ, oddDigitParityCount_succ, pow_succ]
      push_cast
      rw [← ih]
      ring

/-- For an odd alphabet of size `2*H-1`, split into `H` marked and `H-1`
unmarked digits, the signed parity discrepancy is exactly `(-1)^d`. -/
theorem halfDigitParity_intDifference (H d : ℕ) (hH : 1 ≤ H) :
    (evenDigitParityCount H (H - 1) d : ℤ) -
        oddDigitParityCount H (H - 1) d = (-1 : ℤ) ^ d := by
  rw [digitParityCounts_intDifference]
  have hcast : ((H - 1 : ℕ) : ℤ) = (H : ℤ) - 1 := by omega
  rw [hcast]
  ring_nf

/-- The exact total count for the odd half-alphabet specialization. -/
theorem halfDigitParity_total (H d : ℕ) (hH : 1 ≤ H) :
    evenDigitParityCount H (H - 1) d +
        oddDigitParityCount H (H - 1) d =
      (2 * H - 1) ^ d := by
  rw [digitParityCounts_total]
  congr 1
  omega

/-- Explicit absolute-error estimate: twice the even-parity count differs
from its uniform main term `(2*H-1)^d` by exactly one. -/
theorem halfDigitParity_exactAbsoluteError (H d : ℕ) (hH : 1 ≤ H) :
    Int.natAbs
        (2 * (evenDigitParityCount H (H - 1) d : ℤ) -
          ((2 * H - 1) ^ d : ℕ)) = 1 := by
  have htotal := halfDigitParity_total H d hH
  have hdiff := halfDigitParity_intDifference H d hH
  have hrewrite :
      2 * (evenDigitParityCount H (H - 1) d : ℤ) -
          ((2 * H - 1) ^ d : ℕ) =
        (evenDigitParityCount H (H - 1) d : ℤ) -
          oddDigitParityCount H (H - 1) d := by
    have htotalZ :
        (evenDigitParityCount H (H - 1) d : ℤ) +
            oddDigitParityCount H (H - 1) d =
          ((2 * H - 1) ^ d : ℕ) := by
      exact_mod_cast htotal
    rw [← htotalZ]
    ring
  rw [hrewrite, hdiff, Int.natAbs_pow]
  norm_num

/-- Real-valued version of the exact error.  This is often the most useful
form when the finite count is inserted into a density estimate. -/
theorem halfDigitParity_realAbsoluteError (H d : ℕ) (hH : 1 ≤ H) :
    |2 * (evenDigitParityCount H (H - 1) d : ℝ) -
        ((2 * H - 1) ^ d : ℕ)| = 1 := by
  have hdiff := halfDigitParity_intDifference H d hH
  have htotal := halfDigitParity_total H d hH
  have hint :
      2 * (evenDigitParityCount H (H - 1) d : ℤ) -
          ((2 * H - 1) ^ d : ℕ) = (-1 : ℤ) ^ d := by
    calc
      2 * (evenDigitParityCount H (H - 1) d : ℤ) -
            ((2 * H - 1) ^ d : ℕ) =
          (evenDigitParityCount H (H - 1) d : ℤ) -
            oddDigitParityCount H (H - 1) d := by
              have htotalZ :
                  (evenDigitParityCount H (H - 1) d : ℤ) +
                      oddDigitParityCount H (H - 1) d =
                    ((2 * H - 1) ^ d : ℕ) := by
                exact_mod_cast htotal
              rw [← htotalZ]
              ring
      _ = (-1 : ℤ) ^ d := hdiff
  have hreal :
      2 * (evenDigitParityCount H (H - 1) d : ℝ) -
          ((2 * H - 1) ^ d : ℕ) = (-1 : ℝ) ^ d := by
    exact_mod_cast hint
  rw [hreal, abs_pow]
  norm_num

/-- Normalized discrepancy of the even-parity probability from `1/2`.
The denominator is nonzero because `H>=1`. -/
theorem halfDigitParity_probabilityError (H d : ℕ) (hH : 1 ≤ H) :
    |(evenDigitParityCount H (H - 1) d : ℝ) /
          ((2 * H - 1) ^ d : ℕ) - 1 / 2| =
      1 / (2 * ((2 * H - 1) ^ d : ℕ)) := by
  have hbase : 0 < (2 * H - 1 : ℕ) := by omega
  have hden : (0 : ℝ) < ((2 * H - 1) ^ d : ℕ) := by positivity
  have herr := halfDigitParity_realAbsoluteError H d hH
  rw [abs_sub_comm]
  rw [show (1 / 2 : ℝ) -
          (evenDigitParityCount H (H - 1) d : ℝ) /
            ((2 * H - 1) ^ d : ℕ) =
        -((2 * (evenDigitParityCount H (H - 1) d : ℝ) -
              ((2 * H - 1) ^ d : ℕ)) /
            (2 * ((2 * H - 1) ^ d : ℕ))) by field_simp; ring]
  rw [abs_neg, abs_div, herr]
  rw [abs_of_pos (by positivity : (0 : ℝ) <
    2 * ((2 * H - 1) ^ d : ℕ))]

#print axioms digitParityCounts_total
#print axioms digitParityCounts_intDifference
#print axioms halfDigitParity_intDifference
#print axioms halfDigitParity_total
#print axioms halfDigitParity_exactAbsoluteError
#print axioms halfDigitParity_realAbsoluteError
#print axioms halfDigitParity_probabilityError

end Erdos730
