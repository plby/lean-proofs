import ErdosProblems.Erdos67b.MRGSA10Shift

/-!
# The tailored four-fold coefficient in the GS A.10 integral

After the change of variable `z = s - α - β` in source equation
(A.10), the four Dirichlet factors have shifts `0`, `α+2β`, `α`, and
`α+2β`.  This file defines their Dirichlet convolution and proves that
its L-series is exactly the product in the contour integrand.  The two
generalized-Mangoldt factors are cut to the finite source range
`y < n < X/y` before any convergence argument.
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The finite generalized-Mangoldt window `y < n < X/y`. -/
def gsA10LambdaWindow (lambda : ArithmeticFunction ℂ) (y X : ℕ) :
    ArithmeticFunction ℂ :=
  ⟨fun n ↦ if y < n ∧ n < X / y then lambda n else 0,
    by simp⟩

@[simp] theorem gsA10LambdaWindow_apply
    (lambda : ArithmeticFunction ℂ) (y X n : ℕ) :
    gsA10LambdaWindow lambda y X n =
      if y < n ∧ n < X / y then lambda n else 0 := rfl

theorem gsA10LambdaWindow_eq_zero_of_ge
    (lambda : ArithmeticFunction ℂ) (y X : ℕ)
    {n : ℕ} (hn : X / y ≤ n) :
    gsA10LambdaWindow lambda y X n = 0 := by
  simp [gsA10LambdaWindow, not_lt.mpr hn]

/-- The finite window has an absolutely convergent L-series at every point. -/
theorem gsA10LambdaWindow_LSeriesSummable
    (lambda : ArithmeticFunction ℂ) (y X : ℕ) (s : ℂ) :
    LSeriesSummable (gsA10LambdaWindow lambda y X) s := by
  apply summable_of_ne_finset_zero (s := Finset.range (X / y))
  intro n hn
  have hnUpper : X / y ≤ n := by
    simpa only [Finset.mem_range, not_lt] using hn
  by_cases hn0 : n = 0
  · subst n
    simp
  rw [LSeries.term_of_ne_zero hn0,
    gsA10LambdaWindow_eq_zero_of_ge lambda y X hnUpper, zero_div]

/-- Summability transfers exactly across a real coefficient shift. -/
theorem gsRealShift_LSeriesSummable_iff
    (rho : ℝ) (a : ArithmeticFunction ℂ) (s : ℂ) :
    LSeriesSummable (gsRealShift rho a) s ↔
      LSeriesSummable a (s + (rho : ℂ)) := by
  unfold LSeriesSummable
  constructor
  · intro h
    exact h.congr (fun n ↦ LSeries_term_gsRealShift rho a s n)
  · intro h
    exact h.congr (fun n ↦ (LSeries_term_gsRealShift rho a s n).symm)

private theorem arithmetic_mul_LSeriesSummable
    {a b : ArithmeticFunction ℂ} {s : ℂ}
    (ha : LSeriesSummable a s) (hb : LSeriesSummable b s) :
    LSeriesSummable ((a * b : ArithmeticFunction ℂ) : ℕ → ℂ) s := by
  rw [← ArithmeticFunction.coe_mul]
  exact ha.convolution hb

private theorem LSeries_arithmetic_mul
    {a b : ArithmeticFunction ℂ} {s : ℂ}
    (ha : LSeriesSummable a s) (hb : LSeriesSummable b s) :
    LSeries ((a * b : ArithmeticFunction ℂ) : ℕ → ℂ) s =
      LSeries a s * LSeries b s := by
  rw [← ArithmeticFunction.coe_mul]
  exact LSeries_convolution' ha hb

/-- The coefficient whose Perron transform is the inner contour in A.10
after the change of variable `z = s - α - β`. -/
def gsA10TailoredCoefficient
    (low high lambda : ArithmeticFunction ℂ)
    (y X : ℕ) (alpha beta : ℝ) : ArithmeticFunction ℂ :=
  (low * gsRealShift (alpha + 2 * beta) high) *
    (gsRealShift alpha (gsA10LambdaWindow lambda y X) *
      gsRealShift (alpha + 2 * beta) (gsA10LambdaWindow lambda y X))

/-- Absolute convergence of the tailored coefficient requires convergence
only of the low and high factors; both Mangoldt windows are finite. -/
theorem gsA10TailoredCoefficient_LSeriesSummable
    (low high lambda : ArithmeticFunction ℂ)
    (y X : ℕ) (alpha beta : ℝ) (s : ℂ)
    (hlow : LSeriesSummable low s)
    (hhigh : LSeriesSummable high
      (s + ((alpha + 2 * beta : ℝ) : ℂ))) :
    LSeriesSummable
      (gsA10TailoredCoefficient low high lambda y X alpha beta) s := by
  let W := gsA10LambdaWindow lambda y X
  have hhigh' : LSeriesSummable
      (gsRealShift (alpha + 2 * beta) high) s :=
    (gsRealShift_LSeriesSummable_iff _ _ _).2 hhigh
  have hWalpha : LSeriesSummable (gsRealShift alpha W) s :=
    (gsRealShift_LSeriesSummable_iff _ _ _).2
      (gsA10LambdaWindow_LSeriesSummable lambda y X _)
  have hWbeta : LSeriesSummable
      (gsRealShift (alpha + 2 * beta) W) s :=
    (gsRealShift_LSeriesSummable_iff _ _ _).2
      (gsA10LambdaWindow_LSeriesSummable lambda y X _)
  exact arithmetic_mul_LSeriesSummable
    (arithmetic_mul_LSeriesSummable hlow hhigh')
    (arithmetic_mul_LSeriesSummable hWalpha hWbeta)

/-- Exact four-factor L-series identity for the tailored A.10 coefficient. -/
theorem LSeries_gsA10TailoredCoefficient
    (low high lambda : ArithmeticFunction ℂ)
    (y X : ℕ) (alpha beta : ℝ) (s : ℂ)
    (hlow : LSeriesSummable low s)
    (hhigh : LSeriesSummable high
      (s + ((alpha + 2 * beta : ℝ) : ℂ))) :
    LSeries (gsA10TailoredCoefficient
        low high lambda y X alpha beta) s =
      (LSeries low s *
        LSeries high (s + ((alpha + 2 * beta : ℝ) : ℂ))) *
      (LSeries (gsA10LambdaWindow lambda y X)
          (s + (alpha : ℂ)) *
        LSeries (gsA10LambdaWindow lambda y X)
          (s + ((alpha + 2 * beta : ℝ) : ℂ))) := by
  let W := gsA10LambdaWindow lambda y X
  have hhigh' : LSeriesSummable
      (gsRealShift (alpha + 2 * beta) high) s :=
    (gsRealShift_LSeriesSummable_iff _ _ _).2 hhigh
  have hWalpha : LSeriesSummable (gsRealShift alpha W) s :=
    (gsRealShift_LSeriesSummable_iff _ _ _).2
      (gsA10LambdaWindow_LSeriesSummable lambda y X _)
  have hWbeta : LSeriesSummable
      (gsRealShift (alpha + 2 * beta) W) s :=
    (gsRealShift_LSeriesSummable_iff _ _ _).2
      (gsA10LambdaWindow_LSeriesSummable lambda y X _)
  unfold gsA10TailoredCoefficient
  rw [LSeries_arithmetic_mul
      (arithmetic_mul_LSeriesSummable hlow hhigh')
      (arithmetic_mul_LSeriesSummable hWalpha hWbeta),
    LSeries_arithmetic_mul hlow hhigh',
    LSeries_arithmetic_mul hWalpha hWbeta,
    LSeries_gsRealShift, LSeries_gsRealShift,
    LSeries_gsRealShift]

end

end Erdos67b.MRHalaszBands
