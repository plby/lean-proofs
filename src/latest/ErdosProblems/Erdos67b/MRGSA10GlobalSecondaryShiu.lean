import ErdosProblems.Erdos67b.MRGSA10SecondaryCoefficientMajorant
import ErdosProblems.Erdos67b.MRGSA10SecondSecondaryIntegral
import ErdosProblems.Erdos67b.MRGSA10FiniteHighMass
import ErdosProblems.Erdos67b.MRGSA10FiniteLowMassScalar

/-!
# The source-size GS A.10 global secondary

The two source Lemma 2.4 secondary terms are bounded together here.  The
first term uses the direct Shiu majorant.  For the integrated generalized-
Mangoldt term, Chebyshev is applied to its distinguished prime-power
variable before integration; the remaining two finite Euler masses are the
whole alternating low factor and the whole high factor.  Thus no deletion-
block triangle inequality or cardinality loss is introduced.
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The fixed constant for the integrated generalized-Mangoldt secondary. -/
def gsA10SecondSecondaryShiuConstant : ℝ :=
  24 * (Real.log 4 + 4) * gsA10FiniteLowMassConstant *
    Real.exp (Real.log 2 + 2 * Erdos67b.PrimeEstimates.mertensBound +
      3 * Erdos67b.EulerQuantitative.primeQuadraticConstant)

theorem gsA10SecondSecondaryShiuConstant_nonneg :
    0 ≤ gsA10SecondSecondaryShiuConstant := by
  unfold gsA10SecondSecondaryShiuConstant
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hfront : 0 ≤ 24 * (Real.log 4 + 4) := by positivity
  exact mul_nonneg
    (mul_nonneg hfront gsA10FiniteLowMassConstant_nonneg)
    (Real.exp_nonneg _)

/-- Source Lemma 2.4 for the single, whole alternating two-block
coefficient.  The constant is independent of the prime predicates, `f`,
`y`, and the prefix cutoff `X`. -/
theorem norm_gsA10TwoBlockSecondSecondaryPrefix_le_log
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hyX : y ≤ X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    ‖gsA10SecondSecondaryPrefix
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y) X
        (Real.log (y : ℝ))⁻¹‖ ≤
      gsA10SecondSecondaryShiuConstant *
        ((X : ℝ) / Real.log (X : ℝ)) * Real.log (y : ℝ) := by
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  have hy2 : 2 ≤ y := by omega
  have hX2 : 2 ≤ X := hy2.trans hyX
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have heta0 : 0 ≤ eta := (inv_pos.mpr hlogy).le
  have hexpTwo : Real.exp 2 < (y : ℝ) := by
    calc
      Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      _ < 3 * 3 := by
        nlinarith [Real.exp_pos 1, Real.exp_one_lt_three]
      _ < 23 := by norm_num
      _ ≤ y := by exact_mod_cast hy
  have hlogTwo : 2 < Real.log (y : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact hexpTwo
  have hetaHalf : eta ≤ 1 / 2 := by
    dsimp only [eta]
    have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hlogTwo.le
    norm_num at hinv ⊢
    exact hinv
  have hlow :=
    gsFiniteNormDirichletMass_twoBlockAlternatingLow_le_sourceConstant
      hmul hbound P₁ P₂ (X := X) hy hQ₂ hQ₃
        (alpha := eta) heta0 le_rfl
  have hhigh :=
    gsFiniteNormDirichletMass_gsA9HighArithmetic_le_sourceConstant
      hbound hy2 hyX
  have hraw := norm_gsA10SecondSecondaryPrefix_le_chebyshev_masses
    hmul hcomp hbound P₁ P₂ hQ₂ hQ₃ heta0 hetaHalf hX2
  have hlogOne : 1 ≤ Real.log (y : ℝ) := hlogTwo.le.trans' (by norm_num)
  have hlow' :
      gsFiniteNormDirichletMass
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y) X (1 - eta) ≤
        2 * gsA10FiniteLowMassConstant * Real.log (y : ℝ) := by
    calc
      _ ≤ gsA10FiniteLowMassConstant * (1 + Real.log (y : ℝ)) := hlow
      _ ≤ gsA10FiniteLowMassConstant * (2 * Real.log (y : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (by linarith)
          gsA10FiniteLowMassConstant_nonneg
      _ = 2 * gsA10FiniteLowMassConstant * Real.log (y : ℝ) := by ring
  have hbase : 0 ≤
      12 * (Real.log 4 + 4) * ((X : ℝ) / Real.log (X : ℝ)) := by
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    positivity
  have hhighMass : 0 ≤
      gsFiniteNormDirichletMass
        (gsA9HighArithmetic f y) X (1 + 2 * eta) := by
    unfold gsFiniteNormDirichletMass
    positivity
  have hlowBound : 0 ≤
      2 * gsA10FiniteLowMassConstant * Real.log (y : ℝ) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) gsA10FiniteLowMassConstant_nonneg)
      hlogy.le
  calc
    _ ≤ 12 * (Real.log 4 + 4) *
        ((X : ℝ) / Real.log (X : ℝ)) *
        gsFiniteNormDirichletMass
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y) X (1 - eta) *
        gsFiniteNormDirichletMass
          (gsA9HighArithmetic f y) X (1 + 2 * eta) := by
      simpa only [eta] using hraw
    _ ≤ 12 * (Real.log 4 + 4) *
        ((X : ℝ) / Real.log (X : ℝ)) *
        (2 * gsA10FiniteLowMassConstant * Real.log (y : ℝ)) *
        Real.exp (Real.log 2 + 2 * Erdos67b.PrimeEstimates.mertensBound +
          3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hlow' hbase) hhigh
        hhighMass (mul_nonneg hbase hlowBound)
    _ = gsA10SecondSecondaryShiuConstant *
        ((X : ℝ) / Real.log (X : ℝ)) * Real.log (y : ℝ) := by
      unfold gsA10SecondSecondaryShiuConstant
      ring

/-- The fixed source-independent constant for both global A.10
secondaries. -/
def gsA10GlobalSecondaryShiuConstant : ℝ :=
  gsA10ShiuConstant + gsA10SecondSecondaryShiuConstant

theorem gsA10GlobalSecondaryShiuConstant_nonneg :
    0 ≤ gsA10GlobalSecondaryShiuConstant := by
  exact add_nonneg gsA10ShiuConstant_nonneg
    gsA10SecondSecondaryShiuConstant_nonneg

/-- The full GS A.10 global secondary error has the source size
`O(X / log X * log y)`.  The full-window discrepancy is exactly zero. -/
theorem gsA10TwoBlockGlobalSecondaryError_le_log
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hyX : y ≤ X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    gsA10TwoBlockGlobalSecondaryError f hmul P₁ P₂ y X
        (Real.log (y : ℝ))⁻¹ ≤
      gsA10GlobalSecondaryShiuConstant *
        ((X : ℝ) / Real.log (X : ℝ)) * Real.log (y : ℝ) := by
  have hfirst := gsA10TwoBlockGlobalSecondaryError_le_firstLog_add_second
    hmul hbound P₁ P₂ (show 2 ≤ y by omega) hyX hQ₂ hQ₃
  have hsecond := norm_gsA10TwoBlockSecondSecondaryPrefix_le_log
    hmul hcomp hbound P₁ P₂ hy hyX hQ₂ hQ₃
  calc
    _ ≤ gsA10ShiuConstant * ((X : ℝ) / Real.log (X : ℝ)) *
          Real.log (y : ℝ) +
        ‖gsA10SecondSecondaryPrefix
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y) X
          (Real.log (y : ℝ))⁻¹‖ := by
      simpa only [mul_div_assoc] using hfirst
    _ ≤ gsA10ShiuConstant * ((X : ℝ) / Real.log (X : ℝ)) *
          Real.log (y : ℝ) +
        gsA10SecondSecondaryShiuConstant *
          ((X : ℝ) / Real.log (X : ℝ)) * Real.log (y : ℝ) :=
      add_le_add (le_refl _) hsecond
    _ = gsA10GlobalSecondaryShiuConstant *
        ((X : ℝ) / Real.log (X : ℝ)) * Real.log (y : ℝ) := by
      unfold gsA10GlobalSecondaryShiuConstant
      ring

/-- Direct reconstructed-prefix form for insertion into the A.9 central
contour estimate. -/
theorem norm_positivePrefixSum_gsA10TwoBlockReconstructed_le_tailored_add_log
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hyX : y ≤ X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    ‖positivePrefixSum
        (gsA10TwoBlockReconstructedCoefficient f P₁ P₂ y) X‖ ≤
      ‖gsA10TwoBlockTailoredIntegratedPrefix f hmul P₁ P₂ y X
        (Real.log (y : ℝ))⁻¹‖ +
      gsA10GlobalSecondaryShiuConstant *
        ((X : ℝ) / Real.log (X : ℝ)) * Real.log (y : ℝ) := by
  exact (norm_positivePrefixSum_gsA10TwoBlockReconstructed_le
      hmul P₁ P₂ y X (Real.log (y : ℝ))⁻¹).trans
    (add_le_add (le_refl _)
      (gsA10TwoBlockGlobalSecondaryError_le_log
        hmul hcomp hbound P₁ P₂ hy hyX hQ₂ hQ₃))

/-- Removing an Archimedean twist preserves complete multiplicativity on
the positive integers. -/
theorem archimedeanUntwist_isCompletelyMultiplicative
    {f : ℕ → ℂ} (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (t : ℝ) :
    IsCompletelyMultiplicativeOnPositive (archimedeanUntwist f t) := by
  constructor
  · simp [archimedeanUntwist, hcomp.1, archimedeanTwist]
  · intro m n hm hn
    rw [archimedeanUntwist, archimedeanUntwist, archimedeanUntwist,
      if_neg (Nat.mul_ne_zero hm.ne' hn.ne'), if_neg hm.ne', if_neg hn.ne',
      hcomp.2 m n hm hn, archimedeanTwist_mul t hm hn, map_mul]
    ring

/-- Prefix-mean form at the already-removed minimizing Archimedean twist.
The sole remaining central analytic object is the one tailored rectangular
integral; the complete global secondary has been scalarized. -/
theorem norm_positivePrefixMean_gsA10TwoBlock_archimedeanUntwist_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y N : ℕ} (hy : 23 ≤ y) (hyN : y ≤ N)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (t : ℝ) :
    ‖positivePrefixMean
        (gsA10TwoBlockReconstructedCoefficient
          (archimedeanUntwist f t) P₁ P₂ y) N‖ ≤
      (‖gsA10TwoBlockTailoredIntegratedPrefix
          (archimedeanUntwist f t)
          (archimedeanUntwist_isMultiplicative hmul t)
          P₁ P₂ y N (Real.log (y : ℝ))⁻¹‖ +
        gsA10GlobalSecondaryShiuConstant *
          ((N : ℝ) / Real.log (N : ℝ)) * Real.log (y : ℝ)) /
        (N : ℝ) := by
  have hutBound : ∀ n, 0 < n → ‖archimedeanUntwist f t n‖ ≤ 1 := by
    intro n hn
    rw [archimedeanUntwist, if_neg hn.ne', norm_mul,
      Complex.norm_conj, norm_archimedeanTwist hn, mul_one]
    exact hbound n hn
  have hsum :=
    norm_positivePrefixSum_gsA10TwoBlockReconstructed_le_tailored_add_log
      (archimedeanUntwist_isMultiplicative hmul t)
      (archimedeanUntwist_isCompletelyMultiplicative hcomp t)
      hutBound P₁ P₂ hy hyN hQ₂ hQ₃
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  unfold positivePrefixMean
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hsum hNpos.le

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.gsA10TwoBlockGlobalSecondaryError_le_log
#print axioms Erdos67b.MRHalaszBands.norm_positivePrefixSum_gsA10TwoBlockReconstructed_le_tailored_add_log
#print axioms Erdos67b.MRHalaszBands.norm_positivePrefixMean_gsA10TwoBlock_archimedeanUntwist_le
