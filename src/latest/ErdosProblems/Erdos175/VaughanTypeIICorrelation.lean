/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.ReciprocalExpSumRounding
import ErdosProblems.Erdos175.TypeII

/-!
# Reciprocal-sum form of the Type-II Gram correlations

After Cauchy--Schwarz, the off-diagonal terms in a reciprocal bilinear sum
are ordinary reciprocal exponential sums.  This file packages the exact
phase and endpoints and applies the proved q-free estimate without changing
the product support.
-/

noncomputable section

namespace Erdos175.VaughanTypeIICorrelation

open scoped BigOperators

/-- The positive off-diagonal phase when `w < v`. -/
def correlationPhase (x : ℝ) (v w : ℕ) : ℝ :=
  x * (1 / (w : ℝ) - 1 / (v : ℝ))

/-- Lower endpoint of the common product support. -/
def correlationLower (y A v w : ℕ) : ℕ :=
  max A (max (y / v) (y / w))

/-- Upper endpoint of the common product support. -/
def correlationUpper (y' B v w : ℕ) : ℕ :=
  min B (min (y' / v) (y' / w))

theorem correlationPhase_pos
    {x : ℝ} {v w : ℕ} (hx : 0 < x) (hw : 0 < w) (hwv : w < v) :
    0 < correlationPhase x v w := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hwvR : (w : ℝ) < v := by exact_mod_cast hwv
  have hrecip : 1 / (v : ℝ) < 1 / (w : ℝ) :=
    one_div_lt_one_div_of_lt hwR hwvR
  exact mul_pos hx (sub_pos.mpr hrecip)

/-- Exact identification of a product-restricted Gram correlation with a
single reciprocal exponential sum. -/
theorem kernelCorrelation_eq_reciprocalExpSum
    (x : ℝ) (y y' A B v w : ℕ) (hv : 0 < v) (hw : 0 < w) :
    TypeII.kernelCorrelation (Finset.Ioc A B)
        (TypeII.restrictedReciprocalKernel (Finset.Ioc y y') x) v w =
      reciprocalExpSum (correlationPhase x v w)
        (correlationLower y A v w) (correlationUpper y' B v w) := by
  rw [TypeII.kernelCorrelation_restrictedReciprocalKernel_Ioc_eq
    x y y' A B v w hv hw]
  rfl

/-- Proposition 8.1, in its q-free high-frequency form, applied directly to
an off-diagonal Type-II Gram correlation. -/
theorem norm_kernelCorrelation_le_dyadic_qfree
    (x : ℝ) (y y' A B v w : ℕ)
    (hx : 0 < x) (hv : 0 < v) (hw : 0 < w) (hwv : w < v)
    (hAB : correlationLower y A v w ≤ correlationUpper y' B v w)
    (hne : correlationLower y A v w < correlationUpper y' B v w)
    (hdyadic :
      correlationUpper y' B v w - correlationLower y A v w ≤
        correlationLower y A v w + 1)
    (hone :
      12 * correlationPhase x v w ≤
        (((correlationLower y A v w + 1 : ℕ) : ℝ)) ^ 4)
    (hhigh :
      (((correlationLower y A v w + 1 : ℕ) : ℝ)) ^ 4 <
        12 * correlationPhase x v w *
          (Nat.sqrt (correlationUpper y' B v w -
            correlationLower y A v w) : ℝ) ^ 3) :
    ‖TypeII.kernelCorrelation (Finset.Ioc A B)
        (TypeII.restrictedReciprocalKernel (Finset.Ioc y y') x) v w‖ ≤
      128 * ((correlationUpper y' B v w -
          correlationLower y A v w : ℕ) : ℝ) *
        (correlationPhase x v w /
          (((correlationLower y A v w + 1 : ℕ) : ℝ)) ^ 4) ^
            (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log
          (((correlationLower y A v w + 1 : ℕ) : ℝ))) := by
  rw [kernelCorrelation_eq_reciprocalExpSum x y y' A B v w hv hw]
  exact norm_reciprocalExpSum_le_dyadic_qfree
    (correlationPhase x v w)
    (correlationLower y A v w) (correlationUpper y' B v w)
    (correlationPhase_pos hx hw hwv) hAB hne hdyadic hone hhigh

#print axioms kernelCorrelation_eq_reciprocalExpSum
#print axioms norm_kernelCorrelation_le_dyadic_qfree

end Erdos175.VaughanTypeIICorrelation
