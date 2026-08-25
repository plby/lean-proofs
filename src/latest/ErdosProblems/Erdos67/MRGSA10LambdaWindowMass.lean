import ErdosProblems.Erdos67.MRGSA10WeightedChebyshev
import ErdosProblems.Erdos67.MRGSA10HighGeneralizedMangoldt
import ErdosProblems.Erdos67.MRGSA10TailoredCoefficient
import ErdosProblems.Erdos67.MRGSA9SmallPrimeDeletion

/-!
# Absolute mass of the finite A.10 Mangoldt window

The two auxiliary L-series in the tailored Perron integrand are finite
windows of the high generalized-Mangoldt coefficient.  For completely
multiplicative one-bounded coefficients their absolute masses are bounded
directly by weighted Chebyshev, uniformly through the critical exponent.
-/

open scoped BigOperators
open Complex Finset

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- Prime-band deletion preserves complete multiplicativity on positive
integers. -/
theorem gsDeletePrimeBand_isCompletelyMultiplicativeOnPositive
    {f : ℕ → ℂ} (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (Q : ℕ → Prop) [DecidablePred Q] :
    IsCompletelyMultiplicativeOnPositive (gsDeletePrimeBand f Q) := by
  exact primeBandCoefficient_isCompletelyMultiplicativeOnPositive
    hcomp (fun p ↦ ¬ Q p)

/-- Increasing the real exponent can only decrease the absolute mass of a
finite Mangoldt window.  The coefficient at zero vanishes, so there is no
exception to the usual monotonicity of `n^(-sigma)`. -/
theorem dirichletPerronCoefficientMass_gsA10LambdaWindow_anti
    (lambda : ArithmeticFunction ℂ) (y X : ℕ)
    {sigma tau : ℝ} (hst : sigma ≤ tau) :
    dirichletPerronCoefficientMass (gsA10LambdaWindow lambda y X) tau ≤
      dirichletPerronCoefficientMass (gsA10LambdaWindow lambda y X) sigma := by
  let W : ArithmeticFunction ℂ := gsA10LambdaWindow lambda y X
  have hsupport (rho : ℝ) : ∀ n ∉ Finset.range (X / y),
      ‖LSeries.term W (rho : ℂ) n‖ = 0 := by
    intro n hn
    have hnUpper : X / y ≤ n := by
      simpa only [Finset.mem_range, not_lt] using hn
    by_cases hn0 : n = 0
    · subst n
      simp
    rw [LSeries.norm_term_eq, if_neg hn0,
      gsA10LambdaWindow_eq_zero_of_ge lambda y X hnUpper,
      norm_zero, zero_div]
  unfold dirichletPerronCoefficientMass
  rw [tsum_eq_sum (hsupport tau), tsum_eq_sum (hsupport sigma)]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn0, if_neg hn0]
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hpow : (n : ℝ) ^ sigma ≤ (n : ℝ) ^ tau :=
    Real.rpow_le_rpow_of_exponent_le hnOne hst
  exact div_le_div_of_nonneg_left (norm_nonneg _)
    (Real.rpow_pos_of_pos (by positivity) _)
    hpow

/-- The finite Mangoldt window has the expected weighted-Chebyshev mass on
every real line between zero and one. -/
theorem dirichletPerronCoefficientMass_gsA10LambdaWindow_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X)
    {sigma : ℝ} (hsigma0 : 0 ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    dirichletPerronCoefficientMass
        (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
        sigma ≤
      2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ) *
        (X : ℝ) ^ (1 - sigma) := by
  let W : ArithmeticFunction ℂ :=
    gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  have hsupport : ∀ n ∉ Finset.range (X / y),
      ‖LSeries.term W (sigma : ℂ) n‖ = 0 := by
    intro n hn
    have hnUpper : X / y ≤ n := by
      simpa only [Finset.mem_range, not_lt] using hn
    by_cases hn0 : n = 0
    · subst n
      simp
    rw [LSeries.norm_term_eq, if_neg hn0,
      gsA10LambdaWindow_eq_zero_of_ge
        (gsA9HighGeneralizedMangoldt hmul y) y X hnUpper,
      norm_zero, zero_div]
  have hfinite :
      dirichletPerronCoefficientMass W sigma =
        ∑ n ∈ Finset.range (X / y),
          ‖LSeries.term W (sigma : ℂ) n‖ := by
    unfold dirichletPerronCoefficientMass
    exact tsum_eq_sum hsupport
  have hterm : ∀ n ∈ Finset.range (X / y),
      ‖LSeries.term W (sigma : ℂ) n‖ ≤
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma) := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    rw [LSeries.norm_term_eq, if_neg hn0]
    have hW : ‖W n‖ ≤ ArithmeticFunction.vonMangoldt n := by
      dsimp only [W]
      rw [gsA10LambdaWindow_apply]
      split_ifs
      · exact norm_gsA9HighGeneralizedMangoldt_le_vonMangoldt
          hmul hcomp hbound y n
      · simp only [norm_zero]
        exact ArithmeticFunction.vonMangoldt_nonneg
    change ‖W n‖ / (n : ℝ) ^ sigma ≤
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma)
    rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity)]
    exact mul_le_mul_of_nonneg_right hW (Real.rpow_nonneg (by positivity) _)
  have hzeroExtend :
      (∑ n ∈ Finset.Icc 0 X,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma)) =
        ∑ n ∈ Finset.Icc 1 X,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma) := by
    rw [show Finset.Icc 0 X = insert 0 (Finset.Icc 1 X) by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega]
    rw [Finset.sum_insert]
    · simp
    · simp
  rw [hfinite]
  calc
    (∑ n ∈ Finset.range (X / y),
        ‖LSeries.term W (sigma : ℂ) n‖) ≤
        ∑ n ∈ Finset.range (X / y),
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma) := by
      exact Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.Icc 0 X,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hnlt : n < X / y := Finset.mem_range.mp hn
        have hnle : n ≤ X := by
          exact hnlt.le.trans (Nat.div_le_self X y)
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, hnle⟩
      · intro n _ _
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.rpow_nonneg (by positivity) _)
    _ = ∑ n ∈ Finset.Icc 1 X,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma) :=
      hzeroExtend
    _ ≤ _ := sum_vonMangoldt_mul_rpow_neg_le_one
      hX hsigma0 hsigmaOne

/-- Joint bound for the two finite Mangoldt masses on the actual A.10
source lines.  The `min` records the harmless case in which the lower line
has already moved to the right of one. -/
theorem mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_sourceLines_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {beta : ℝ} (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let c := Erdos67.EulerResidue.taoExponent X
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
    dirichletPerronCoefficientMass W (c - beta) *
        dirichletPerronCoefficientMass W (c + beta) ≤
      (2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ)) ^ 2 *
        (X : ℝ) ^ (1 - min (c - beta) 1) := by
  dsimp only
  let c : ℝ := Erdos67.EulerResidue.taoExponent X
  let rho : ℝ := min (c - beta) 1
  let W : ArithmeticFunction ℂ :=
    gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  let B : ℝ := 2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ)
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hcOne : 1 ≤ c := by
    dsimp only [c, Erdos67.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hetaQuarter : (Real.log (y : ℝ))⁻¹ ≤ 1 / 4 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlogy
  have hlineLow : 0 ≤ c - beta := by linarith
  have hrho0 : 0 ≤ rho := by
    exact le_min hlineLow (by norm_num)
  have hrhoOne : rho ≤ 1 := min_le_right _ _
  have hrhoLine : rho ≤ c - beta := min_le_left _ _
  have honeHigh : 1 ≤ c + beta := by linarith
  have hlowBase := dirichletPerronCoefficientMass_gsA10LambdaWindow_le
    hmul hcomp hbound (y := y) (X := X) hX hrho0 hrhoOne
  have hhighBase := dirichletPerronCoefficientMass_gsA10LambdaWindow_le
    hmul hcomp hbound (y := y) (X := X) hX
      (show (0 : ℝ) ≤ 1 by norm_num) (le_refl 1)
  have hlow : dirichletPerronCoefficientMass W (c - beta) ≤
      B * (X : ℝ) ^ (1 - rho) := by
    exact (dirichletPerronCoefficientMass_gsA10LambdaWindow_anti
      (gsA9HighGeneralizedMangoldt hmul y) y X hrhoLine).trans
        (by simpa only [W, B] using hlowBase)
  have hhigh : dirichletPerronCoefficientMass W (c + beta) ≤ B := by
    have hanti := dirichletPerronCoefficientMass_gsA10LambdaWindow_anti
      (gsA9HighGeneralizedMangoldt hmul y) y X honeHigh
    refine hanti.trans ?_
    simpa only [W, B, sub_self, Real.rpow_zero, mul_one] using hhighBase
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hmassHigh0 :
      0 ≤ dirichletPerronCoefficientMass W (c + beta) := by
    unfold dirichletPerronCoefficientMass
    positivity
  have hlowUpper0 : 0 ≤ B * (X : ℝ) ^ (1 - rho) :=
    mul_nonneg hB0 (Real.rpow_nonneg (by positivity) _)
  calc
    dirichletPerronCoefficientMass W (c - beta) *
        dirichletPerronCoefficientMass W (c + beta) ≤
      (B * (X : ℝ) ^ (1 - rho)) * B :=
        mul_le_mul hlow hhigh hmassHigh0 hlowUpper0
    _ = B ^ 2 * (X : ℝ) ^ (1 - rho) := by ring

/-- Source-deleted specialization used by the lossless A.13--A.14 product
in the tailored Perron window. -/
theorem mul_dirichletPerronCoefficientMass_gsA10SourceDeleted_sourceLines_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {beta : ℝ} (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let hmulG := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
      hmul gsA9SmallPrime
    let c := Erdos67.EulerResidue.taoExponent X
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmulG y) y X
    dirichletPerronCoefficientMass W (c - beta) *
        dirichletPerronCoefficientMass W (c + beta) ≤
      (2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ)) ^ 2 *
        (X : ℝ) ^ (1 - min (c - beta) 1) := by
  dsimp only
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hcompG : IsCompletelyMultiplicativeOnPositive g :=
    gsDeletePrimeBand_isCompletelyMultiplicativeOnPositive hcomp gsA9SmallPrime
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  simpa only [g, hmulG] using
    (mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_sourceLines_le
      hmulG hcompG hboundG hX hlogy hbeta0 hbeta)

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.dirichletPerronCoefficientMass_gsA10LambdaWindow_anti
#print axioms
  Erdos67.MRHalaszBands.dirichletPerronCoefficientMass_gsA10LambdaWindow_le
#print axioms
  Erdos67.MRHalaszBands.mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_sourceLines_le
#print axioms
  Erdos67.MRHalaszBands.mul_dirichletPerronCoefficientMass_gsA10SourceDeleted_sourceLines_le
