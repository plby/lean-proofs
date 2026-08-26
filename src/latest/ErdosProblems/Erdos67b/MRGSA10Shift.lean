import ErdosProblems.Erdos67b.MRGSA10Coefficient

/-!
# Real shifts of arithmetic functions for the A.10 contour integrand

The two auxiliary integrations in the many-convolutions argument repeatedly
replace `LSeries a s` by `LSeries a (s + ρ)`.  This module packages the
corresponding coefficient shift and proves the equality term by term,
including the value at zero required by `ArithmeticFunction`.
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Multiplication of coefficients by `n^{-ρ}`, expressed with the real
exponential so that the coefficient is unambiguous at `n = 0`. -/
def gsRealShift (rho : ℝ) (a : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else
      (Real.exp (-rho * Real.log n) : ℂ) * a n,
    by simp⟩

@[simp] theorem gsRealShift_zero (rho : ℝ) (a : ArithmeticFunction ℂ) :
    gsRealShift rho a 0 = 0 := by
  simp [gsRealShift]

theorem gsRealShift_apply_of_ne_zero (rho : ℝ)
    (a : ArithmeticFunction ℂ) {n : ℕ} (hn : n ≠ 0) :
    gsRealShift rho a n =
      (Real.exp (-rho * Real.log n) : ℂ) * a n := by
  simp [gsRealShift, hn]

private theorem exp_neg_mul_log_nat_eq_cpow_neg
    {n : ℕ} (hn : n ≠ 0) (rho : ℝ) :
    (Real.exp (-rho * Real.log n) : ℂ) =
      (n : ℂ) ^ (-((rho : ℂ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hR : Real.exp (-rho * Real.log n) = (n : ℝ) ^ (-rho) := by
    rw [Real.rpow_def_of_pos hnR]
    congr 1
    ring
  calc
    (Real.exp (-rho * Real.log n) : ℂ) =
        (Real.rpow (n : ℝ) (-rho) : ℂ) := congrArg Complex.ofReal hR
    _ = ((n : ℝ) : ℂ) ^ (((-rho : ℝ) : ℂ)) :=
      Complex.ofReal_cpow hnR.le (-rho)
    _ = (n : ℂ) ^ (-((rho : ℂ))) := by
      congr 2
      exact Complex.ofReal_neg rho

/-- A shifted coefficient term at `s` is the original coefficient term at
`s + ρ`. -/
theorem LSeries_term_gsRealShift
    (rho : ℝ) (a : ArithmeticFunction ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (gsRealShift rho a) s n =
      LSeries.term a (s + (rho : ℂ)) n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    gsRealShift_apply_of_ne_zero rho a hn,
    exp_neg_mul_log_nat_eq_cpow_neg hn rho]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_neg, Complex.cpow_add _ _ hnC]
  have hs0 : (n : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  have hr0 : (n : ℂ) ^ (rho : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  field_simp

/-- Exact shift identity for L-series, valid definitionally even outside
the half-plane of convergence because both sides are the same `tsum`. -/
theorem LSeries_gsRealShift
    (rho : ℝ) (a : ArithmeticFunction ℂ) (s : ℂ) :
    LSeries (gsRealShift rho a) s = LSeries a (s + (rho : ℂ)) := by
  unfold LSeries
  apply tsum_congr
  exact LSeries_term_gsRealShift rho a s

/-- Real shifts add on positive coefficients. -/
theorem gsRealShift_add_apply_of_ne_zero
    (rho tau : ℝ) (a : ArithmeticFunction ℂ)
    {n : ℕ} (hn : n ≠ 0) :
    gsRealShift rho (gsRealShift tau a) n =
      gsRealShift (rho + tau) a n := by
  rw [gsRealShift_apply_of_ne_zero rho _ hn,
    gsRealShift_apply_of_ne_zero tau _ hn,
    gsRealShift_apply_of_ne_zero (rho + tau) _ hn]
  have hR :
      Real.exp (-rho * Real.log n) * Real.exp (-tau * Real.log n) =
        Real.exp (-(rho + tau) * Real.log n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hC :
      (Real.exp (-rho * Real.log n) : ℂ) *
          (Real.exp (-tau * Real.log n) : ℂ) =
        (Real.exp (-(rho + tau) * Real.log n) : ℂ) := by
    exact_mod_cast hR
  rw [← mul_assoc, hC]

/-- Bundled equality for addition of two real coefficient shifts. -/
theorem gsRealShift_add
    (rho tau : ℝ) (a : ArithmeticFunction ℂ) :
    gsRealShift rho (gsRealShift tau a) =
      gsRealShift (rho + tau) a := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  exact gsRealShift_add_apply_of_ne_zero rho tau a hn

end

end Erdos67b.MRHalaszBands
