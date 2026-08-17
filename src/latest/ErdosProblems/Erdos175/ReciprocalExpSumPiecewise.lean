/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.ReciprocalExpSumOneStep
import ErdosProblems.Erdos175.ReciprocalExpSumRounding

/-!
# A branch-selective reciprocal exponential-sum bound

This file packages the first-derivative, one-difference, and two-difference
estimates into one piecewise bound.  Unlike a sum of the three bounds, the
definition below retains only the estimate belonging to the active frequency
range.  A final trivial branch covers short intervals on which the two-step
high-frequency hypothesis fails.
-/

namespace Erdos175

noncomputable section

/-- The branch-selective majorant for a reciprocal exponential sum on
`A < n ≤ B`.  The branches are, in order: direct Kusmin--Landau, one Weyl
difference, two Weyl differences, and the trivial interval-length bound. -/
def piecewiseReciprocalBound (x : ℝ) (A B : ℕ) : ℝ :=
  if x / ((A + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 2 then
    ((B + 1 : ℕ) : ℝ) ^ 2 / x
  else if 4 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 3 then
    24 * ((A + 1 : ℕ) : ℝ) *
      Real.sqrt (x / ((A + 1 : ℕ) : ℝ) ^ 3) *
      Real.sqrt (1 + Real.log ((A + 1 : ℕ) : ℝ))
  else if ((A + 1 : ℕ) : ℝ) ^ 4 <
      12 * x * (Nat.sqrt (B - A) : ℝ) ^ 3 then
    128 * ((B - A : ℕ) : ℝ) *
      (x / ((A + 1 : ℕ) : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
      Real.sqrt (1 + Real.log ((A + 1 : ℕ) : ℝ))
  else
    ((B - A : ℕ) : ℝ)

/-- The selective majorant is nonnegative at nonnegative frequency. -/
theorem piecewiseReciprocalBound_nonneg
    (x : ℝ) (A B : ℕ) (hx : 0 ≤ x) :
    0 ≤ piecewiseReciprocalBound x A B := by
  unfold piecewiseReciprocalBound
  split_ifs <;> positivity

/-- Positive-frequency form of the branch-selective reciprocal exponential
sum estimate.  The global upper-frequency hypothesis is needed only in the
two-difference branch. -/
theorem norm_reciprocalExpSum_le_piecewise
    (x : ℝ) (A B : ℕ) (hx : 0 < x) (hAB : A ≤ B)
    (hdyadic : B - A ≤ A + 1)
    (hglobal : 12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4) :
    ‖reciprocalExpSum x A B‖ ≤ piecewiseReciprocalBound x A B := by
  unfold piecewiseReciprocalBound
  split_ifs with hdirect hone hhigh
  · exact norm_reciprocalExpSum_le_firstDerivative x A B hx hAB hdirect
  · have hC2 : ((A + 1 : ℕ) : ℝ) ^ 2 < 2 * x := by
      have hC2pos : 0 < ((A + 1 : ℕ) : ℝ) ^ 2 := by positivity
      have hlt : 1 / 2 < x / ((A + 1 : ℕ) : ℝ) ^ 2 :=
        lt_of_not_ge hdirect
      rw [lt_div_iff₀ hC2pos] at hlt
      nlinarith
    have hmiddle : ((A + 1 : ℕ) : ℝ) ^ 3 <
        4 * x * ((A + 1 : ℕ) : ℝ) := by
      have hCpos : 0 < ((A + 1 : ℕ) : ℝ) := by positivity
      have hm := mul_lt_mul_of_pos_right hC2 hCpos
      nlinarith
    exact norm_reciprocalExpSum_le_dyadic_qfree_k1
      x A B hx hAB hdyadic hone hmiddle
  · have hne : A < B := by
      by_contra hnlt
      have hBA : B - A = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hnlt)
      have hbad : ((A + 1 : ℕ) : ℝ) ^ 4 < 0 := by
        simpa [hBA] using hhigh
      exact (not_lt_of_ge (by positivity)) hbad
    exact norm_reciprocalExpSum_le_dyadic_qfree
      x A B hx hAB hne hdyadic hglobal hhigh
  · exact norm_reciprocalExpSum_le x A B

/-- Sign-symmetric branch-selective estimate.  This is the form used when a
correlation produces a reciprocal phase coefficient of unknown sign. -/
theorem norm_reciprocalExpSum_le_piecewise_abs
    (t : ℝ) (A B : ℕ) (ht : t ≠ 0) (hAB : A ≤ B)
    (hdyadic : B - A ≤ A + 1)
    (hglobal : 12 * |t| ≤ ((A + 1 : ℕ) : ℝ) ^ 4) :
    ‖reciprocalExpSum t A B‖ ≤ piecewiseReciprocalBound |t| A B := by
  have habs : 0 < |t| := abs_pos.mpr ht
  have hbase := norm_reciprocalExpSum_le_piecewise
    |t| A B habs hAB hdyadic hglobal
  by_cases htpos : 0 < t
  · simpa only [abs_of_pos htpos] using hbase
  · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) ht
    calc
      ‖reciprocalExpSum t A B‖ = ‖reciprocalExpSum |t| A B‖ := by
        simpa only [abs_of_neg htneg, neg_neg] using
          norm_reciprocalExpSum_neg (-t) A B
      _ ≤ piecewiseReciprocalBound |t| A B := hbase

end

end Erdos175
