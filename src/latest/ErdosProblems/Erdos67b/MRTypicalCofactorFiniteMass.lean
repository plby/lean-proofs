import ErdosProblems.Erdos67b.MRTypicalCofactorMass
import ErdosProblems.Erdos67b.MRGSA10FiniteMassScalar

/-! # Finite low mass of the actual typical cofactor -/

open scoped BigOperators Classical LSeries.notation ComplexOrder

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrOne_le_norm_positiveHighLSeries (y : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    1 ≤ ‖LSeries (gsA9High (fun _ : ℕ ↦ (1 : ℂ)) y) (sigma : ℂ)‖ := by
  let a := gsA9HighArithmetic (fun _ : ℕ ↦ (1 : ℂ)) y
  have hsum : LSeriesSummable a (sigma : ℂ) :=
    gsA9HighArithmetic_LSeriesSummable (fun _ _ ↦ by simp) y (by simpa using hsigma)
  have hnonneg : ∀ n, 0 ≤ a n := by
    intro n
    by_cases hn : n = 0
    · subst n; simp
    rw [gsA9HighArithmetic_apply_of_ne_zero _ y hn]
    unfold gsA9High primeBandCoefficient
    split_ifs <;> simp
  have hmajor : ∀ n ∈ Finset.Icc 1 1, ‖(1 : ArithmeticFunction ℂ) n‖ ≤ ‖a n‖ := by
    intro n hn
    have hn1 : n = 1 := by simp only [Finset.mem_Icc] at hn; omega
    subst n
    have hone : IsMultiplicativeOnPositiveNat (fun _ : ℕ ↦ (1 : ℂ)) := by
      constructor <;> simp
    simp [a, gsA9HighArithmetic_one hone]
  have h := gsFiniteNormDirichletMass_le_norm_LSeries_of_major
    (b := (1 : ArithmeticFunction ℂ)) (X := 1) hsum hnonneg hmajor
  simpa [gsFiniteNormDirichletMass, a, LSeries_gsA9HighArithmetic] using h

theorem mrFiniteNormMass_typicalCofactorLow_le_positive {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y X : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    gsFiniteNormDirichletMass (mrTypicalCofactorLowArithmetic A J B f y) X sigma ≤
      ‖LSeries (gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y) (sigma : ℂ)‖ := by
  have hsum := mrPrimeBandCoefficient_LSeriesSummable_of_bounded_pos_re
    (fun _ _ ↦ by simp : ∀ n : ℕ, 0 < n → ‖(1 : ℂ)‖ ≤ 1)
    (fun p ↦ p ≤ y) y (fun _ hp ↦ hp) (s := (sigma : ℂ)) (by simpa using hsigma)
  apply gsFiniteNormDirichletMass_le_norm_LSeries_of_major hsum
  · intro n
    unfold primeBandCoefficient
    split_ifs <;> simp
  · intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    by_cases hsupp : PrimeSupported (fun p ↦ p ≤ y) n
    · simpa [mrTypicalCofactorLowArithmetic, toArithmeticFunction, gsA9Low,
        primeBandCoefficient, hnpos.ne', hsupp] using
        mrIndexedTypicalCofactorCoefficient_norm_le_one A J B hbound hnpos
    · simp [mrTypicalCofactorLowArithmetic, toArithmeticFunction, gsA9Low,
        primeBandCoefficient, hnpos.ne', hsupp]

theorem mrFiniteNormMass_typicalCofactorLow_le_source {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hy : 23 ≤ y) (hlogy : 6 ≤ Real.log (y : ℝ))
    {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha : alpha ≤ (Real.log (y : ℝ))⁻¹) :
    gsFiniteNormDirichletMass (mrTypicalCofactorLowArithmetic A J B f y) X (1 - alpha) ≤
      gsA10SourceCoefficientMassConstant * (1 + Real.log (y : ℝ)) := by
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  have heta0 : 0 < eta := inv_pos.mpr (by linarith)
  have heta : eta ≤ 1 / 6 := by
    simpa only [eta, one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hhalf : 1 / 2 ≤ 1 - alpha := by change alpha ≤ eta at ha; linarith
  have hhigh : 1 < 1 + eta := by linarith
  have hprod := mrNorm_positiveLow_mul_positiveHigh_le hy
    (sigmaLow := 1 - alpha) (sigmaHigh := 1 + eta) hhalf hhigh (by linarith)
    (by rw [div_eq_mul_inv]; change 1 - 3 * eta ≤ 1 - alpha; linarith)
    (by rw [div_eq_mul_inv]; change 1 + eta - (1 - alpha) ≤ 3 * eta; linarith)
  have hlow : ‖LSeries (gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y) ((1 - alpha : ℝ) : ℂ)‖ ≤
      gsA10SourceCoefficientMassConstant * (1 + Real.log (y : ℝ)) := by
    calc
      _ ≤ ‖LSeries (gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y) ((1 - alpha : ℝ) : ℂ)‖ *
          ‖LSeries (gsA9High (fun _ : ℕ ↦ (1 : ℂ)) y) ((1 + eta : ℝ) : ℂ)‖ :=
        le_mul_of_one_le_right (norm_nonneg _) (mrOne_le_norm_positiveHighLSeries y hhigh)
      _ ≤ gsA10SourceCoefficientMassConstant * (1 + ((1 + eta) - 1)⁻¹) := hprod
      _ = _ := by simp [eta]
  exact (mrFiniteNormMass_typicalCofactorLow_le_positive A J B hbound y X (by linarith)).trans hlow

end

end Erdos67b
