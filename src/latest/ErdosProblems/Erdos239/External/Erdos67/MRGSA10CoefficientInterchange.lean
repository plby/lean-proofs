import ErdosProblems.Erdos239.External.Erdos67.MRGSA10ExponentialAverage

/-!
# Finite coefficient interchange for the GS A.10 auxiliary averages

The tailored A.10 coefficient is a four-fold Dirichlet convolution.  This
file expands one coefficient into three nested divisor sums, commutes those
finite sums with the two auxiliary interval integrals, and evaluates the
three resulting real coefficient shifts.
-/

open scoped BigOperators

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The three real coefficient shifts at a fixed A.10 factorization. -/
def gsA10ThreeShiftAverageIntegrand
    (highIndex lambdaIndex₁ lambdaIndex₂ : ℕ)
    (alpha beta : ℝ) : ℂ :=
  (Real.exp (-(alpha + 2 * beta) * Real.log highIndex) : ℂ) *
    (Real.exp (-alpha * Real.log lambdaIndex₁) : ℂ) *
      (Real.exp (-(alpha + 2 * beta) * Real.log lambdaIndex₂) : ℂ)

/-- The rectangular average of the three A.10 coefficient shifts. -/
def gsA10ThreeShiftAverage
    (highIndex lambdaIndex₁ lambdaIndex₂ : ℕ) (eta : ℝ) : ℂ :=
  ∫ alpha : ℝ in 0..eta,
    ∫ beta : ℝ in 0..eta,
      gsA10ThreeShiftAverageIntegrand
        highIndex lambdaIndex₁ lambdaIndex₂ alpha beta

/-- Explicit nested divisor expansion of one tailored A.10 coefficient. -/
theorem gsA10TailoredCoefficient_apply_eq_nested
    (low high lambda : ArithmeticFunction ℂ)
    (y X : ℕ) (alpha beta : ℝ) {n : ℕ} (hn : n ≠ 0) :
    gsA10TailoredCoefficient low high lambda y X alpha beta n =
      ∑ uv ∈ n.divisorsAntidiagonal,
        ∑ ab ∈ uv.1.divisorsAntidiagonal,
          ∑ cd ∈ uv.2.divisorsAntidiagonal,
            (low ab.1 * high ab.2 *
              gsA10LambdaWindow lambda y X cd.1 *
                gsA10LambdaWindow lambda y X cd.2) *
              gsA10ThreeShiftAverageIntegrand
                ab.2 cd.1 cd.2 alpha beta := by
  classical
  rw [gsA10TailoredCoefficient, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro uv huv
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro cd hcd
  have huvEq := (Nat.mem_divisorsAntidiagonal.mp huv).1
  have habEq := (Nat.mem_divisorsAntidiagonal.mp hab).1
  have hcdEq := (Nat.mem_divisorsAntidiagonal.mp hcd).1
  have huv1 : uv.1 ≠ 0 := by
    intro h
    simp [h] at huvEq
    exact hn huvEq.symm
  have huv2 : uv.2 ≠ 0 := by
    intro h
    simp [h] at huvEq
    exact hn huvEq.symm
  have hab2 : ab.2 ≠ 0 := by
    intro h
    simp [h] at habEq
    exact huv1 habEq.symm
  have hcd1 : cd.1 ≠ 0 := by
    intro h
    simp [h] at hcdEq
    exact huv2 hcdEq.symm
  have hcd2 : cd.2 ≠ 0 := by
    intro h
    simp [h] at hcdEq
    exact huv2 hcdEq.symm
  rw [gsRealShift_apply_of_ne_zero _ _ hab2,
    gsRealShift_apply_of_ne_zero _ _ hcd1,
    gsRealShift_apply_of_ne_zero _ _ hcd2]
  simp only [gsA10ThreeShiftAverageIntegrand]
  ring

private theorem continuous_gsA10ThreeShiftAverageIntegrand_beta
    (highIndex lambdaIndex₁ lambdaIndex₂ : ℕ) (alpha : ℝ) :
    Continuous (fun beta : ℝ ↦
      gsA10ThreeShiftAverageIntegrand
        highIndex lambdaIndex₁ lambdaIndex₂ alpha beta) := by
  unfold gsA10ThreeShiftAverageIntegrand
  fun_prop

/-- The beta-dependent part left after separating a fixed `alpha`. -/
def gsA10ThreeShiftBetaMass
    (highIndex lambdaIndex₂ : ℕ) (eta : ℝ) : ℂ :=
  ∫ beta : ℝ in 0..eta,
    (Real.exp (-(2 * beta) * Real.log highIndex) : ℂ) *
      (Real.exp (-(2 * beta) * Real.log lambdaIndex₂) : ℂ)

private theorem integral_gsA10ThreeShiftAverageIntegrand_beta
    (highIndex lambdaIndex₁ lambdaIndex₂ : ℕ) (eta alpha : ℝ) :
    (∫ beta : ℝ in 0..eta,
      gsA10ThreeShiftAverageIntegrand
        highIndex lambdaIndex₁ lambdaIndex₂ alpha beta) =
      ((Real.exp (-alpha * Real.log highIndex) : ℂ) *
        (Real.exp (-alpha * Real.log lambdaIndex₁) : ℂ) *
          (Real.exp (-alpha * Real.log lambdaIndex₂) : ℂ)) *
        gsA10ThreeShiftBetaMass highIndex lambdaIndex₂ eta := by
  have hpoint (beta : ℝ) :
      gsA10ThreeShiftAverageIntegrand
          highIndex lambdaIndex₁ lambdaIndex₂ alpha beta =
        ((Real.exp (-alpha * Real.log highIndex) : ℂ) *
          (Real.exp (-alpha * Real.log lambdaIndex₁) : ℂ) *
            (Real.exp (-alpha * Real.log lambdaIndex₂) : ℂ)) *
          ((Real.exp (-(2 * beta) * Real.log highIndex) : ℂ) *
            (Real.exp (-(2 * beta) * Real.log lambdaIndex₂) : ℂ)) := by
    have hh : Real.exp (-(alpha + 2 * beta) * Real.log highIndex) =
        Real.exp (-alpha * Real.log highIndex) *
          Real.exp (-(2 * beta) * Real.log highIndex) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf
    have htwo : Real.exp (-(alpha + 2 * beta) * Real.log lambdaIndex₂) =
        Real.exp (-alpha * Real.log lambdaIndex₂) *
          Real.exp (-(2 * beta) * Real.log lambdaIndex₂) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf
    simp only [gsA10ThreeShiftAverageIntegrand, hh, htwo]
    push_cast
    ring_nf
  rw [intervalIntegral.integral_congr (fun beta _ ↦ hpoint beta),
    intervalIntegral.integral_const_mul]
  rfl

private theorem continuous_integral_gsA10ThreeShiftAverageIntegrand_beta
    (highIndex lambdaIndex₁ lambdaIndex₂ : ℕ) (eta : ℝ) :
    Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta,
        gsA10ThreeShiftAverageIntegrand
          highIndex lambdaIndex₁ lambdaIndex₂ alpha beta) := by
  simp_rw [integral_gsA10ThreeShiftAverageIntegrand_beta]
  fun_prop

/-- Finite divisor sums commute with the two A.10 auxiliary integrals. -/
theorem intervalIntegral_intervalIntegral_gsA10TailoredCoefficient_eq_nested
    (low high lambda : ArithmeticFunction ℂ)
    (y X : ℕ) (eta : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        gsA10TailoredCoefficient low high lambda y X alpha beta n) =
      ∑ uv ∈ n.divisorsAntidiagonal,
        ∑ ab ∈ uv.1.divisorsAntidiagonal,
          ∑ cd ∈ uv.2.divisorsAntidiagonal,
            (low ab.1 * high ab.2 *
              gsA10LambdaWindow lambda y X cd.1 *
                gsA10LambdaWindow lambda y X cd.2) *
              gsA10ThreeShiftAverage ab.2 cd.1 cd.2 eta := by
  classical
  simp_rw [gsA10TailoredCoefficient_apply_eq_nested
    low high lambda y X _ _ hn]
  have hinner (alpha : ℝ) :
      (∫ beta : ℝ in 0..eta,
        ∑ uv ∈ n.divisorsAntidiagonal,
          ∑ ab ∈ uv.1.divisorsAntidiagonal,
            ∑ cd ∈ uv.2.divisorsAntidiagonal,
              (low ab.1 * high ab.2 *
                gsA10LambdaWindow lambda y X cd.1 *
                  gsA10LambdaWindow lambda y X cd.2) *
                gsA10ThreeShiftAverageIntegrand
                  ab.2 cd.1 cd.2 alpha beta) =
        ∑ uv ∈ n.divisorsAntidiagonal,
          ∑ ab ∈ uv.1.divisorsAntidiagonal,
            ∑ cd ∈ uv.2.divisorsAntidiagonal,
              (low ab.1 * high ab.2 *
                gsA10LambdaWindow lambda y X cd.1 *
                  gsA10LambdaWindow lambda y X cd.2) *
                (∫ beta : ℝ in 0..eta,
                  gsA10ThreeShiftAverageIntegrand
                    ab.2 cd.1 cd.2 alpha beta) := by
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro uv huv
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro ab hab
        rw [intervalIntegral.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro cd hcd
          rw [intervalIntegral.integral_const_mul]
        · intro cd hcd
          apply Continuous.intervalIntegrable
          apply Continuous.const_mul
          exact continuous_gsA10ThreeShiftAverageIntegrand_beta
            ab.2 cd.1 cd.2 alpha
      · intro ab hab
        apply Continuous.intervalIntegrable
        apply continuous_finsetSum
        intro cd hcd
        apply Continuous.const_mul
        exact continuous_gsA10ThreeShiftAverageIntegrand_beta
          ab.2 cd.1 cd.2 alpha
    · intro uv huv
      apply Continuous.intervalIntegrable
      apply continuous_finsetSum
      intro ab hab
      apply continuous_finsetSum
      intro cd hcd
      apply Continuous.const_mul
      exact continuous_gsA10ThreeShiftAverageIntegrand_beta
        ab.2 cd.1 cd.2 alpha
  rw [intervalIntegral.integral_congr (fun alpha _ ↦ hinner alpha)]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro uv huv
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro ab hab
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro cd hcd
        rw [intervalIntegral.integral_const_mul]
        rfl
      · intro cd hcd
        apply Continuous.intervalIntegrable
        apply Continuous.const_mul
        exact continuous_integral_gsA10ThreeShiftAverageIntegrand_beta
          ab.2 cd.1 cd.2 eta
    · intro ab hab
      apply Continuous.intervalIntegrable
      apply continuous_finsetSum
      intro cd hcd
      apply Continuous.const_mul
      exact continuous_integral_gsA10ThreeShiftAverageIntegrand_beta
        ab.2 cd.1 cd.2 eta
  · intro uv huv
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro ab hab
    apply continuous_finsetSum
    intro cd hcd
    apply Continuous.const_mul
    exact continuous_integral_gsA10ThreeShiftAverageIntegrand_beta
      ab.2 cd.1 cd.2 eta

/-- Closed form of the three-shift average when the two generalized-Mangoldt
indices are nontrivial.  The high-factor index need only be nonzero. -/
theorem gsA10ThreeShiftAverage_eq
    {highIndex lambdaIndex₁ lambdaIndex₂ : ℕ} {eta : ℝ}
    (hhigh : highIndex ≠ 0) (hlambda₁ : 2 ≤ lambdaIndex₁)
    (hlambda₂ : 2 ≤ lambdaIndex₂) :
    gsA10ThreeShiftAverage highIndex lambdaIndex₁ lambdaIndex₂ eta =
      (((1 : ℂ) - Complex.exp (-(((Real.log lambdaIndex₁ +
          (Real.log highIndex + Real.log lambdaIndex₂) : ℝ) : ℂ) *
          (eta : ℂ)))) /
        ((Real.log lambdaIndex₁ +
          (Real.log highIndex + Real.log lambdaIndex₂) : ℝ) : ℂ)) *
      (((1 : ℂ) - Complex.exp (-(((2 *
          (Real.log highIndex + Real.log lambdaIndex₂) : ℝ) : ℂ) *
          (eta : ℂ)))) /
        ((2 * (Real.log highIndex + Real.log lambdaIndex₂) : ℝ) : ℂ)) := by
  have hhighPos : 0 < highIndex := Nat.pos_of_ne_zero hhigh
  have hprod : 2 ≤ highIndex * lambdaIndex₂ :=
    hlambda₂.trans (Nat.le_mul_of_pos_left lambdaIndex₂ hhighPos)
  have hhighR : (highIndex : ℝ) ≠ 0 := by exact_mod_cast hhigh
  have hlambda₂R : (lambdaIndex₂ : ℝ) ≠ 0 := by
    exact_mod_cast (show lambdaIndex₂ ≠ 0 by omega)
  have hpoint (alpha beta : ℝ) :
      gsA10ThreeShiftAverageIntegrand
          highIndex lambdaIndex₁ lambdaIndex₂ alpha beta =
        (Real.exp (-alpha * Real.log lambdaIndex₁) : ℂ) *
          (Real.exp (-(alpha + 2 * beta) *
            (Real.log highIndex + Real.log lambdaIndex₂)) : ℂ) := by
    have hlog : Real.log (highIndex * lambdaIndex₂) =
        Real.log highIndex + Real.log lambdaIndex₂ := by
      rw [Real.log_mul hhighR hlambda₂R]
    have hexp : Real.exp (-(alpha + 2 * beta) *
          Real.log (highIndex * lambdaIndex₂)) =
        Real.exp (-(alpha + 2 * beta) * Real.log highIndex) *
          Real.exp (-(alpha + 2 * beta) * Real.log lambdaIndex₂) := by
      rw [hlog, show -(alpha + 2 * beta) *
          (Real.log highIndex + Real.log lambdaIndex₂) =
        (-(alpha + 2 * beta) * Real.log highIndex) +
          (-(alpha + 2 * beta) * Real.log lambdaIndex₂) by ring,
        Real.exp_add]
    have hreal :
        Real.exp (-(alpha + 2 * beta) * Real.log highIndex) *
            Real.exp (-alpha * Real.log lambdaIndex₁) *
              Real.exp (-(alpha + 2 * beta) * Real.log lambdaIndex₂) =
          Real.exp (-alpha * Real.log lambdaIndex₁) *
            Real.exp (-(alpha + 2 * beta) *
              (Real.log highIndex + Real.log lambdaIndex₂)) := by
      rw [← hlog, hexp]
      ring
    have hc := congrArg Complex.ofReal hreal
    simpa only [gsA10ThreeShiftAverageIntegrand, Complex.ofReal_mul] using hc
  unfold gsA10ThreeShiftAverage
  simp_rw [hpoint]
  have h := intervalIntegral_intervalIntegral_realExp_natLog_two_shift
    (eta := eta) hlambda₁ hprod
  simp only [Nat.cast_mul] at h
  rw [Real.log_mul hhighR hlambda₂R] at h
  exact h

/-- The closed logarithmic factor produced by the two A.10 averages. -/
def gsA10ThreeShiftClosedForm
    (highIndex lambdaIndex₁ lambdaIndex₂ : ℕ) (eta : ℝ) : ℂ :=
  (((1 : ℂ) - Complex.exp (-(((Real.log lambdaIndex₁ +
      (Real.log highIndex + Real.log lambdaIndex₂) : ℝ) : ℂ) *
      (eta : ℂ)))) /
    ((Real.log lambdaIndex₁ +
      (Real.log highIndex + Real.log lambdaIndex₂) : ℝ) : ℂ)) *
  (((1 : ℂ) - Complex.exp (-(((2 *
      (Real.log highIndex + Real.log lambdaIndex₂) : ℝ) : ℂ) *
      (eta : ℂ)))) /
    ((2 * (Real.log highIndex + Real.log lambdaIndex₂) : ℝ) : ℂ))

/-- Fully closed nested coefficient formula.  The window makes both
Mangoldt indices at least two, so no zero-denominator branch remains. -/
theorem intervalIntegral_intervalIntegral_gsA10TailoredCoefficient_eq_closed
    (low high lambda : ArithmeticFunction ℂ)
    {y X : ℕ} (hy : 1 ≤ y) (eta : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        gsA10TailoredCoefficient low high lambda y X alpha beta n) =
      ∑ uv ∈ n.divisorsAntidiagonal,
        ∑ ab ∈ uv.1.divisorsAntidiagonal,
          ∑ cd ∈ uv.2.divisorsAntidiagonal,
            (low ab.1 * high ab.2 *
              gsA10LambdaWindow lambda y X cd.1 *
                gsA10LambdaWindow lambda y X cd.2) *
              gsA10ThreeShiftClosedForm ab.2 cd.1 cd.2 eta := by
  classical
  rw [intervalIntegral_intervalIntegral_gsA10TailoredCoefficient_eq_nested
    low high lambda y X eta hn]
  apply Finset.sum_congr rfl
  intro uv huv
  apply Finset.sum_congr rfl
  intro ab hab
  apply Finset.sum_congr rfl
  intro cd hcd
  by_cases hcd1 : y < cd.1 ∧ cd.1 < X / y
  · by_cases hcd2 : y < cd.2 ∧ cd.2 < X / y
    · have habEq := (Nat.mem_divisorsAntidiagonal.mp hab).1
      have huvEq := (Nat.mem_divisorsAntidiagonal.mp huv).1
      have huv1 : uv.1 ≠ 0 := by
        intro h
        simp [h] at huvEq
        exact hn huvEq.symm
      have hab2 : ab.2 ≠ 0 := by
        intro h
        simp [h] at habEq
        exact huv1 habEq.symm
      rw [gsA10ThreeShiftAverage_eq hab2 (by omega) (by omega)]
      rfl
    · simp [gsA10LambdaWindow, hcd2]
  · simp [gsA10LambdaWindow, hcd1]

end

end Erdos67.MRHalaszBands
