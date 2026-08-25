import ErdosProblems.Erdos1141b.QuadraticAbel
import ErdosProblems.Erdos1141b.AbelTail
import BoundedGaps.BombieriVinogradov.Analytic.QuadraticLValueLowerBound

/-!
# Positivity at a finite cutoff and the value at one
-/

open Complex
open scoped BigOperators ComplexOrder

namespace Erdos1141b

lemma natCast_neg_cpow_eq_rpow (n : ℕ) (β : ℝ) :
    (n : ℂ) ^ (-(β : ℂ)) = (((n : ℝ) ^ (-β) : ℝ) : ℂ) := by
  simpa only [Complex.ofReal_natCast, Complex.ofReal_neg] using
    (Complex.ofReal_cpow (Nat.cast_nonneg n) (-β)).symm

lemma one_le_weighted_zetaMul_prefix {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ ^ 2 = 1) (β : ℝ) (X : ℕ) (hX : 0 < X) :
    (1 : ℂ) ≤ ∑ n ∈ Finset.Icc 1 X, χ.zetaMul n * (n : ℂ) ^ (-(β : ℂ)) := by
  have hnonneg : ∀ n ∈ Finset.Icc 1 X, (0 : ℂ) ≤ χ.zetaMul n * (n : ℂ) ^ (-(β : ℂ)) := by
    intro n _
    apply mul_nonneg (χ.zetaMul_nonneg hχ n)
    rw [natCast_neg_cpow_eq_rpow]
    exact_mod_cast Real.rpow_nonneg (Nat.cast_nonneg n) (-β)
  have h := Finset.single_le_sum hnonneg (Finset.mem_Icc.mpr ⟨le_rfl, hX⟩ : 1 ∈ Finset.Icc 1 X)
  simpa only [Nat.cast_one, one_cpow, mul_one, χ.isMultiplicative_zetaMul.map_one] using h

lemma centeredZeta_weighted_prefix {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (β : ℝ) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, centeredZetaCoefficients χ n * (n : ℂ) ^ (-(β : ℂ))) =
      (∑ n ∈ Finset.Icc 1 X, χ.zetaMul n * (n : ℂ) ^ (-(β : ℂ))) -
      χ.LFunction 1 * ((∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (-β) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  simp only [centeredZetaCoefficients, ArithmeticFunction.zeta_apply, hn0, if_false,
    Nat.cast_one, mul_one, sub_mul, natCast_neg_cpow_eq_rpow]

theorem norm_centeredZetaLFunction_sub_prefix_le {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {β : ℝ} (hβ : 3 / 4 ≤ β) (X : ℕ) (hX : 0 < X) :
    ‖centeredZetaLFunction χ (β : ℂ) -
      (∑ n ∈ Finset.Icc 1 X, centeredZetaCoefficients χ n * (n : ℂ) ^ (-(β : ℂ)))‖ ≤
      4 * (1 + 16 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) * (X : ℝ) ^ (1 / 2 - β) := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq.le)
  rw [centeredZetaLFunction_eq_abelIntegral hq χ hχ _ (by simp; linarith)]
  apply norm_abelValue_sub_prefix_le _ (centeredZetaCoefficients_zero χ) _ (by positivity)
  · intro n
    rw [centeredZetaCoefficients_prefix]
    exact norm_zetaMul_prefix_sub_main_le_sqrt hq χ hχ n
  · exact hβ
  · exact hX

/-- If `ζ(β)L(β,χ)` is nonpositive, positivity of the coefficients forces a lower bound at one. -/
theorem one_le_LValue_mul_cutoff_add_error {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsquare : χ ^ 2 = 1)
    {β : ℝ} (hβ : 3 / 4 ≤ β) (hβ1 : β < 1)
    (hproduct : (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ)).re ≤ 0)
    (X : ℕ) (hX : 0 < X) :
    1 ≤ (χ.LFunction 1).re *
        ((∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (-β)) - (riemannZeta (β : ℂ)).re) +
      4 * (1 + 16 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) * (X : ℝ) ^ (1 / 2 - β) := by
  have hpositive := Complex.re_le_re (one_le_weighted_zetaMul_prefix χ hsquare β X hX)
  simp only [one_re] at hpositive
  have herror := norm_centeredZetaLFunction_sub_prefix_le hq χ hχ hβ X hX
  rw [norm_sub_rev, centeredZeta_weighted_prefix] at herror
  have hreal := (Complex.re_le_norm _).trans herror
  have hLreal := BoundedGaps.Maynard.LFunction_one_im_eq_zero_of_sq_eq_one χ hχ hsquare
  have hβne : (β : ℂ) ≠ 1 := by exact_mod_cast hβ1.ne
  rw [centeredZetaLFunction_of_ne_one χ hβne, mul_sub] at hreal
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, hLreal, mul_zero, sub_zero] at hreal
  simp only [mul_re] at hproduct
  nlinarith

end Erdos1141b
