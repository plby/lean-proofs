import ErdosProblems.Erdos67b.MRPerronNearTripleConvolution
import ErdosProblems.Erdos67b.MRGSA10SpecializedPerron
import ErdosProblems.Erdos67b.MRGSA10SecondaryCoefficientMajorant
import ErdosProblems.Erdos67b.MRGSA10LambdaWindowMass

/-!
# A lossless near-mass bound for the tailored A.10 coefficient

The two finite generalized-Mangoldt windows are kept distinguished.  The
remaining low--high coefficient is bounded by the single whole Shiu weight;
there is no four-deletion triangle inequality and no global coefficient-mass
loss.
-/

open scoped BigOperators ArithmeticFunction.zeta
open Finset

namespace Erdos67b.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard
open MRPerronNearTripleConvolution

theorem gsA10ShiuWeight_le_one_of_nonneg
    (y : ℕ) {rho : ℝ} (hrho : 0 ≤ rho) (n : ℕ) :
    gsA10ShiuWeight y rho n ≤ 1 := by
  unfold gsA10ShiuWeight
  split
  · exact zero_le_one
  · apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (primeBandPart_ne_zero (fun p ↦ ¬ p ≤ y) n)
    · exact neg_nonpos.mpr hrho

theorem norm_gsRealShift_gsA10LambdaWindow_le_vonMangoldt
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y X : ℕ) {rho : ℝ} (hrho : 0 ≤ rho) (n : ℕ) :
    ‖gsRealShift rho
        (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X) n‖ ≤
      ArithmeticFunction.vonMangoldt n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  rw [gsRealShift_apply_of_ne_zero rho _ hn, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  have hexp : Real.exp (-rho * Real.log (n : ℝ)) =
      (n : ℝ) ^ (-rho) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hnpos)]
    congr 1
    ring
  have hpow : (n : ℝ) ^ (-rho) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (show 1 ≤ n by omega)) (neg_nonpos.mpr hrho)
  have hwindow :
      ‖gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X n‖ ≤
        ArithmeticFunction.vonMangoldt n := by
    rw [gsA10LambdaWindow_apply]
    split_ifs
    · exact norm_gsA9HighGeneralizedMangoldt_le_vonMangoldt
        hmul hcomp hbound y n
    · simp only [norm_zero]
      exact ArithmeticFunction.vonMangoldt_nonneg
  rw [hexp]
  exact (mul_le_mul hpow hwindow (norm_nonneg _)
    (by norm_num)).trans_eq (one_mul _)

theorem norm_gsA10TwoBlockLowHighShift_le_one
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {rho : ℝ} (hrho : 0 ≤ rho) (n : ℕ) :
    ‖(gsA10TwoBlockAlternatingLow f P₁ P₂ y *
        gsRealShift rho (gsA9HighArithmetic f y)) n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  exact (norm_gsA10FirstSecondaryCoefficient_le_shiuWeight
    hmul hbound P₁ P₂ y hQ₂ hQ₃ rho (Nat.pos_of_ne_zero hn)).trans
      (gsA10ShiuWeight_le_one_of_nonneg y hrho n)

/-- Pointwise in the auxiliary rectangle, the complete tailored near mass
is bounded by the two distinguished von-Mangoldt hyperbola sum. -/
theorem dirichletPerronNearMass_gsA10TwoBlockTailoredCoefficient_le_vonMangoldt
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ}
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (hX : 0 < X) {T : ℝ} (hT : 0 < T)
    {alpha beta : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) :
    dirichletPerronNearMass
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta) X T ≤
      ∑ a ∈ gsPositiveBelow (2 * X + 1),
        ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
            (fun b ↦ a * b < 2 * X + 1),
          ArithmeticFunction.vonMangoldt a *
            ArithmeticFunction.vonMangoldt b *
              (2 + (4 * (X : ℝ) / T) * ((a * b : ℕ) : ℝ)⁻¹ *
                (harmonic (2 * X) : ℝ)) := by
  let base : ArithmeticFunction ℂ :=
    gsA10TwoBlockAlternatingLow f P₁ P₂ y *
      gsRealShift (alpha + 2 * beta) (gsA9HighArithmetic f y)
  let W₁ : ArithmeticFunction ℂ :=
    gsRealShift alpha
      (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
  let W₂ : ArithmeticFunction ℂ :=
    gsRealShift (alpha + 2 * beta)
      (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
  have hbase : ∀ n, ‖base n‖ ≤ (1 : ℝ) := by
    intro n
    exact norm_gsA10TwoBlockLowHighShift_le_one hmul hbound P₁ P₂ y
      hQ₂ hQ₃ (by linarith) n
  have hW₁ : ∀ n, ‖W₁ n‖ ≤ ArithmeticFunction.vonMangoldt n := by
    intro n
    exact norm_gsRealShift_gsA10LambdaWindow_le_vonMangoldt
      hmul hcomp hbound y X halpha n
  have hW₂ : ∀ n, ‖W₂ n‖ ≤ ArithmeticFunction.vonMangoldt n := by
    intro n
    exact norm_gsRealShift_gsA10LambdaWindow_le_vonMangoldt
      hmul hcomp hbound y X (by linarith) n
  have hgeneric := dirichletPerronNearMass_mul_mul_le hX hT
    base W₁ W₂ (fun _ ↦ (1 : ℝ))
    ArithmeticFunction.vonMangoldt ArithmeticFunction.vonMangoldt
    hbase hW₁ hW₂ (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)
    (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
    (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
  have hcoeff :
      gsA10TwoBlockTailoredCoefficient f hmul P₁ P₂ y X alpha beta =
        (W₁ * W₂) * base := by
    dsimp only [gsA10TwoBlockTailoredCoefficient, gsA10TailoredCoefficient,
      base, W₁, W₂]
    rw [mul_comm]
  rw [hcoeff]
  exact hgeneric

/-- The three-factor von-Mangoldt divisor mass at one integer is at most
the square of its logarithm.  Algebraically this is
`(Λ * Λ) * ζ = Λ * log`. -/
theorem sum_nested_vonMangoldt_le_log_sq
    {N : ℕ} (hN : 0 < N) :
    (∑ uv ∈ N.divisorsAntidiagonal,
      ∑ ab ∈ uv.1.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt ab.1 *
          ArithmeticFunction.vonMangoldt ab.2) ≤
      (Real.log (N : ℝ)) ^ 2 := by
  let L := ArithmeticFunction.vonMangoldt
  have heq :
      (∑ uv ∈ N.divisorsAntidiagonal,
        ∑ ab ∈ uv.1.divisorsAntidiagonal,
          L ab.1 * L ab.2) =
        (((L * L) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) N) := by
    rw [ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro uv huv
    have huvData := Nat.mem_divisorsAntidiagonal.mp huv
    have huv2 : uv.2 ≠ 0 := by
      intro h
      simp [h] at huvData
      exact hN.ne' huvData.1.symm
    rw [ArithmeticFunction.mul_apply]
    rw [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne huv2]
    simp only [Nat.cast_one, mul_one]
  rw [heq]
  dsimp only [L]
  rw [mul_assoc, ArithmeticFunction.vonMangoldt_mul_zeta,
    ArithmeticFunction.mul_apply]
  calc
    (∑ ab ∈ N.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt ab.1 *
          ArithmeticFunction.log ab.2) ≤
      ∑ ab ∈ N.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt ab.1 * Real.log (N : ℝ) := by
        apply Finset.sum_le_sum
        intro ab hab
        have habData := Nat.mem_divisorsAntidiagonal.mp hab
        have hab2pos : 0 < ab.2 := by
          by_contra h
          have : ab.2 = 0 := Nat.eq_zero_of_not_pos h
          simp [this] at habData
          exact hN.ne' habData.1.symm
        have hab2le : ab.2 ≤ N := by
          rw [← habData.1]
          exact Nat.le_mul_of_pos_left _ (by
            have hab1pos : 0 < ab.1 := by
              by_contra h
              have : ab.1 = 0 := Nat.eq_zero_of_not_pos h
              simp [this] at habData
              exact hN.ne' habData.1.symm
            exact hab1pos)
        rw [ArithmeticFunction.log_apply]
        apply mul_le_mul_of_nonneg_left
        · exact Real.strictMonoOn_log.monotoneOn
            (by
              simpa only [Set.mem_Ioi] using
                (show (0 : ℝ) < ab.2 by exact_mod_cast hab2pos))
            (by
              simpa only [Set.mem_Ioi] using
                (show (0 : ℝ) < N by exact_mod_cast hN))
            (by exact_mod_cast hab2le)
        · exact ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log (N : ℝ) *
          (∑ d ∈ N.divisors, ArithmeticFunction.vonMangoldt d) := by
        rw [Nat.sum_divisorsAntidiagonal
          (fun d _ ↦ ArithmeticFunction.vonMangoldt d * Real.log (N : ℝ)),
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
    _ = (Real.log (N : ℝ)) ^ 2 := by
      rw [ArithmeticFunction.vonMangoldt_sum]
      ring

/-- The half-jump coefficient in Perron inversion has the same lossless
three-factor majorant, and is only logarithmic squared pointwise. -/
theorem norm_gsA10TwoBlockTailoredCoefficient_apply_le_log_sq
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ}
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (hX : 0 < X) {alpha beta : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) :
    ‖gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta X‖ ≤
      (Real.log (X : ℝ)) ^ 2 := by
  let base : ArithmeticFunction ℂ :=
    gsA10TwoBlockAlternatingLow f P₁ P₂ y *
      gsRealShift (alpha + 2 * beta) (gsA9HighArithmetic f y)
  let W₁ : ArithmeticFunction ℂ :=
    gsRealShift alpha
      (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
  let W₂ : ArithmeticFunction ℂ :=
    gsRealShift (alpha + 2 * beta)
      (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
  have hbase : ∀ n, ‖base n‖ ≤ (1 : ℝ) := by
    intro n
    exact norm_gsA10TwoBlockLowHighShift_le_one hmul hbound P₁ P₂ y
      hQ₂ hQ₃ (by linarith) n
  have hW₁ : ∀ n, ‖W₁ n‖ ≤ ArithmeticFunction.vonMangoldt n := by
    intro n
    exact norm_gsRealShift_gsA10LambdaWindow_le_vonMangoldt
      hmul hcomp hbound y X halpha n
  have hW₂ : ∀ n, ‖W₂ n‖ ≤ ArithmeticFunction.vonMangoldt n := by
    intro n
    exact norm_gsRealShift_gsA10LambdaWindow_le_vonMangoldt
      hmul hcomp hbound y X (by linarith) n
  have hcoeff :
      gsA10TwoBlockTailoredCoefficient f hmul P₁ P₂ y X alpha beta =
        (W₁ * W₂) * base := by
    dsimp only [gsA10TwoBlockTailoredCoefficient, gsA10TailoredCoefficient,
      base, W₁, W₂]
    rw [mul_comm]
  rw [hcoeff]
  have hraw := norm_mul_mul_apply_le_nested base W₁ W₂
    (fun _ ↦ (1 : ℝ)) ArithmeticFunction.vonMangoldt
    ArithmeticFunction.vonMangoldt hbase hW₁ hW₂
    (fun _ ↦ by norm_num)
    (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
    (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg) X
  exact hraw.trans (by
    simpa only [one_mul] using sum_nested_vonMangoldt_le_log_sq hX)

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.dirichletPerronNearMass_gsA10TwoBlockTailoredCoefficient_le_vonMangoldt
#print axioms
  Erdos67b.MRHalaszBands.norm_gsA10TwoBlockTailoredCoefficient_apply_le_log_sq
