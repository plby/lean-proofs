import ErdosProblems.Erdos239.External.Erdos67.MRGSA10SourceMaximumModulus
import ErdosProblems.Erdos239.External.Erdos67.MRGSA9ContourScalar

/-!
# Scalar form of the A.10 maximum-modulus envelope

This file separates the elementary normalization in `log X` and the loss
from the natural-number halving of the Archimedean distance parameter.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

/-- A fixed positive decay rate left by the deleted-function maximum
modulus argument. -/
def gsA10SourceArchDecayRate : ℝ := Real.exp (-1) / 8

/-- The fixed scalar which absorbs the maximum-modulus boundary constants. -/
def gsA10SourceArchDecayConstant : ℝ :=
  2 * Real.exp
    (Real.exp (-1) / 2 +
      3 * Erdos67.EulerQuantitative.primeQuadraticConstant / 2)

theorem gsA10SourceArchDecayRate_pos :
    0 < gsA10SourceArchDecayRate := by
  unfold gsA10SourceArchDecayRate
  positivity

theorem gsA10SourceArchDecayRate_le_one :
    gsA10SourceArchDecayRate ≤ 1 := by
  unfold gsA10SourceArchDecayRate
  have he : Real.exp (-1) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_monotone (by norm_num : (-1 : ℝ) ≤ 0)
  linarith [Real.exp_pos (-1)]

theorem gsA10SourceArchDecayConstant_nonneg :
    0 ≤ gsA10SourceArchDecayConstant := by
  unfold gsA10SourceArchDecayConstant
  positivity

/-- After division by `sqrt (log X)`, the maximum-modulus square-root
envelope is the expected exponential Archimedean saving plus the vanishing
logarithmic error. -/
theorem gsA10SourceMaximumModulusSqrtScalar_div_sqrt_log_le
    {A X : ℕ} (hlogX : 1 ≤ Real.log (X : ℝ)) :
    gsA10SourceMaximumModulusSqrtScalar A X /
        Real.sqrt (Real.log (X : ℝ)) ≤
      2 * Real.exp
          ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
            3 * Erdos67.EulerQuantitative.primeQuadraticConstant) / 2) +
        1 / Real.sqrt (Real.log (X : ℝ)) := by
  let L : ℝ := Real.log (X : ℝ)
  let q : ℝ :=
    (-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
      3 * Erdos67.EulerQuantitative.primeQuadraticConstant) / 2
  have hratio : Real.sqrt (1 + L) / Real.sqrt L ≤ 2 :=
    Erdos67.sqrt_one_add_div_sqrt_le_two (by simpa only [L] using hlogX)
  have hq : 0 ≤ Real.exp q := (Real.exp_pos q).le
  dsimp only [gsA10SourceMaximumModulusSqrtScalar]
  change (Real.sqrt (1 + L) * Real.exp q + 1) / Real.sqrt L ≤ _
  have hmain :
      Real.sqrt (1 + L) / Real.sqrt L * Real.exp q ≤
        2 * Real.exp q :=
    mul_le_mul_of_nonneg_right hratio hq
  calc
    (Real.sqrt (1 + L) * Real.exp q + 1) / Real.sqrt L =
        Real.sqrt (1 + L) / Real.sqrt L * Real.exp q +
          1 / Real.sqrt L := by ring
    _ ≤ 2 * Real.exp q + 1 / Real.sqrt L :=
      by
        simpa only [add_comm] using
          add_le_add_right hmain (1 / Real.sqrt L)
    _ = _ := by rfl

/-- A real lower bound for the natural-number half used after deleting the
fixed small primes. -/
theorem natHalf_cast_ge_sub_one (A : ℕ) :
    (A : ℝ) / 2 - 1 ≤ ((A / 2 : ℕ) : ℝ) := by
  have hnat : A ≤ 2 * (A / 2) + 1 := by omega
  have hnatR : (A : ℝ) ≤ 2 * ((A / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hnat
  linarith

/-- Replace the floor in the preceding normalized maximum-modulus estimate
by a genuine exponential in the original Archimedean parameter. -/
theorem gsA10SourceMaximumModulusSqrtScalar_div_sqrt_log_le_exp
    {A X : ℕ} (hlogX : 1 ≤ Real.log (X : ℝ)) :
    gsA10SourceMaximumModulusSqrtScalar A X /
        Real.sqrt (Real.log (X : ℝ)) ≤
      2 * Real.exp
          (-Real.exp (-1) * (A : ℝ) / 4 +
            Real.exp (-1) / 2 +
            3 * Erdos67.EulerQuantitative.primeQuadraticConstant / 2) +
        1 / Real.sqrt (Real.log (X : ℝ)) := by
  refine (gsA10SourceMaximumModulusSqrtScalar_div_sqrt_log_le hlogX).trans ?_
  have hhalf := natHalf_cast_ge_sub_one A
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  have hq :
      (-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
          3 * Erdos67.EulerQuantitative.primeQuadraticConstant) / 2 ≤
        -Real.exp (-1) * (A : ℝ) / 4 +
          Real.exp (-1) / 2 +
          3 * Erdos67.EulerQuantitative.primeQuadraticConstant / 2 := by
    nlinarith
  have hmain := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hq)
    (show (0 : ℝ) ≤ 2 by norm_num)
  simpa only [add_comm] using
    add_le_add_right hmain (1 / Real.sqrt (Real.log (X : ℝ)))

/-- Final source-facing form: the maximum-modulus contribution is charged
to `(A+1) exp (-c A)`, while the only spatial remainder is
`1 / sqrt (log X)`. -/
theorem gsA10SourceMaximumModulusSqrtScalar_div_sqrt_log_le_archError
    {A X : ℕ} (hlogX : 1 ≤ Real.log (X : ℝ)) :
    gsA10SourceMaximumModulusSqrtScalar A X /
        Real.sqrt (Real.log (X : ℝ)) ≤
      gsA10SourceArchDecayConstant * ((A : ℝ) + 1) *
          Real.exp (-gsA10SourceArchDecayRate * (A : ℝ)) +
        1 / Real.sqrt (Real.log (X : ℝ)) := by
  refine (gsA10SourceMaximumModulusSqrtScalar_div_sqrt_log_le_exp
    hlogX).trans ?_
  let e : ℝ := Real.exp (-1)
  let q : ℝ := e / 2 +
    3 * Erdos67.EulerQuantitative.primeQuadraticConstant / 2
  have he0 : 0 < e := by dsimp only [e]; positivity
  have hA0 : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
  have hdecay : Real.exp (-e * (A : ℝ) / 4) ≤
      Real.exp (-e * (A : ℝ) / 8) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hAone : 1 ≤ (A : ℝ) + 1 := by linarith
  have hmain :
      2 * Real.exp (-Real.exp (-1) * (A : ℝ) / 4 +
          Real.exp (-1) / 2 +
          3 * Erdos67.EulerQuantitative.primeQuadraticConstant / 2) ≤
        gsA10SourceArchDecayConstant * ((A : ℝ) + 1) *
          Real.exp (-gsA10SourceArchDecayRate * (A : ℝ)) := by
    dsimp only [gsA10SourceArchDecayConstant,
      gsA10SourceArchDecayRate]
    calc
      2 * Real.exp (-Real.exp (-1) * (A : ℝ) / 4 +
          Real.exp (-1) / 2 +
          3 * Erdos67.EulerQuantitative.primeQuadraticConstant / 2) =
          (2 * Real.exp q) * Real.exp (-e * (A : ℝ) / 4) := by
        rw [show -Real.exp (-1) * (A : ℝ) / 4 +
            Real.exp (-1) / 2 +
            3 * Erdos67.EulerQuantitative.primeQuadraticConstant / 2 =
          (-e * (A : ℝ) / 4) + q by
            simp only [e, q]
            ring,
          Real.exp_add]
        ring
      _ ≤ (2 * Real.exp q) * Real.exp (-e * (A : ℝ) / 8) := by
        gcongr
      _ ≤ (2 * Real.exp q) * ((A : ℝ) + 1) *
          Real.exp (-(e / 8) * (A : ℝ)) := by
        have hq0 : 0 ≤ 2 * Real.exp q := by positivity
        have hexp0 : 0 ≤ Real.exp (-e * (A : ℝ) / 8) :=
          (Real.exp_pos _).le
        have hfactor : (2 * Real.exp q) * 1 ≤
            (2 * Real.exp q) * ((A : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hAone hq0
        have hprod := mul_le_mul_of_nonneg_right hfactor hexp0
        rw [show -(e / 8) * (A : ℝ) = -e * (A : ℝ) / 8 by ring]
        simpa only [mul_one] using hprod
      _ = (2 * Real.exp
            (Real.exp (-1) / 2 +
              3 * Erdos67.EulerQuantitative.primeQuadraticConstant / 2)) *
            ((A : ℝ) + 1) *
              Real.exp (-(Real.exp (-1) / 8) * (A : ℝ)) := by
        rfl
  simpa only [add_comm] using add_le_add_right hmain
    (1 / Real.sqrt (Real.log (X : ℝ)))

end

end Erdos67.MRHalaszBands
