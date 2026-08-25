import ErdosProblems.Erdos67.MRGSA10ShiuMean
import ErdosProblems.Erdos67.MRGSA10PrefixIntegralMajorant

/-!
# Coefficient majorants for the two A.10 secondary sums

The four deletion terms are never estimated separately.  Their alternating
low coefficient is supported on the low prime band, so complementary-band
uniqueness extracts one common shifted high factor from the entire
convolution.
-/

open scoped BigOperators

namespace Erdos67.MRHalaszBands

noncomputable section

theorem gsA10TwoBlockAlternatingLow_eq_zero_of_not_lowSupported
    (f : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ) {n : ℕ} (hn : n ≠ 0)
    (hnot : ¬ PrimeSupported (fun p ↦ p ≤ y) n) :
    gsA10TwoBlockAlternatingLow f P₁ P₂ y n = 0 := by
  classical
  have hnot₂ :
      ¬ PrimeSupported (fun p ↦ p ≤ y ∧ ¬ (¬ P₁ p ∧ P₂ p)) n := by
    intro h
    exact hnot ⟨h.1, fun p hp ↦ (h.2 p hp).1⟩
  have hnot₃ :
      ¬ PrimeSupported (fun p ↦ p ≤ y ∧ ¬ (¬ P₁ p ∧ ¬ P₂ p)) n := by
    intro h
    exact hnot ⟨h.1, fun p hp ↦ (h.2 p hp).1⟩
  have hnot₂₃ :
      ¬ PrimeSupported (fun p ↦ p ≤ y ∧
        ¬ ((¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p))) n := by
    intro h
    exact hnot ⟨h.1, fun p hp ↦ (h.2 p hp).1⟩
  have h₀ : gsA9LowArithmetic f y n = 0 := by
    simp [gsA9LowArithmetic, toArithmeticFunction, gsA9Low,
      primeBandCoefficient, hn, hnot]
  have h₂ : gsA9LowDeletionArithmetic f (fun p ↦ ¬ P₁ p ∧ P₂ p) y n = 0 := by
    simp [gsA9LowDeletionArithmetic, toArithmeticFunction, gsA9LowDeletion,
      primeBandCoefficient, hn]
    intro hs
    exact (hnot ⟨hs.1, fun p hp ↦ (hs.2 p hp).1⟩).elim
  have h₃ : gsA9LowDeletionArithmetic f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) y n = 0 := by
    simp [gsA9LowDeletionArithmetic, toArithmeticFunction, gsA9LowDeletion,
      primeBandCoefficient, hn]
    intro hs
    exact (hnot ⟨hs.1, fun p hp ↦ (hs.2 p hp).1⟩).elim
  have h₂₃ : gsA9LowDeletionArithmetic f
      (fun p ↦ (¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p)) y n = 0 := by
    simp [gsA9LowDeletionArithmetic, toArithmeticFunction, gsA9LowDeletion,
      primeBandCoefficient, hn]
    intro hs
    exact (hnot ⟨hs.1, fun p hp ↦ (hs.2 p hp).1⟩).elim
  change gsA9LowArithmetic f y n -
      gsA9LowDeletionArithmetic f (fun p ↦ ¬ P₁ p ∧ P₂ p) y n -
      gsA9LowDeletionArithmetic f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) y n +
      gsA9LowDeletionArithmetic f
        (fun p ↦ (¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p)) y n = 0
  rw [h₀, h₂, h₃, h₂₃]
  ring

/-- A shifted complementary-band convolution is the unshifted convolution
times the shift of the unique high-prime part. -/
theorem low_mul_shift_high_apply
    (low high : ArithmeticFunction ℂ) (y : ℕ) (eta : ℝ)
    {n : ℕ} (hn : 0 < n)
    (hlow : ∀ d, d ≠ 0 →
      ¬ PrimeSupported (fun p ↦ p ≤ y) d → low d = 0)
    (hhigh : ∀ e, e ≠ 0 →
      ¬ PrimeSupported (fun p ↦ ¬ p ≤ y) e → high e = 0) :
    (low * gsRealShift eta high) n =
      (((primeBandPart (fun p ↦ ¬ p ≤ y) n : ℝ) ^ (-eta) : ℝ) : ℂ) *
        (low * high) n := by
  let d := primeBandPart (fun p ↦ p ≤ y) n
  let e := primeBandPart (fun p ↦ ¬ p ≤ y) n
  have hn0 : n ≠ 0 := hn.ne'
  have hde : d * e = n := primeBandPart_mul_compl (fun p ↦ p ≤ y) hn0
  have hd : PrimeSupported (fun p ↦ p ≤ y) d :=
    primeSupported_primeBandPart (fun p ↦ p ≤ y) n
  have he : PrimeSupported (fun p ↦ ¬ p ≤ y) e :=
    primeSupported_primeBandPart (fun p ↦ ¬ p ≤ y) n
  have hmem : (d, e) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨hde, hn0⟩
  have hshift : gsRealShift eta high e =
      ((((e : ℝ) ^ (-eta)) : ℝ) : ℂ) * high e := by
    rw [gsRealShift_apply_of_ne_zero eta high he.1]
    have hepos : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he.1
    have hexp : Real.exp (-eta * Real.log (e : ℝ)) =
        (e : ℝ) ^ (-eta) := by
      rw [Real.rpow_def_of_pos hepos]
      congr 1
      ring
    rw [hexp]
  rw [ArithmeticFunction.mul_apply]
  rw [Finset.sum_eq_single (d, e)]
  · rw [hshift, ArithmeticFunction.mul_apply]
    rw [Finset.sum_eq_single (d, e)]
    · dsimp only [e]
      ring
    · intro q hq hqne
      have hq1 : q.1 ≠ 0 :=
        (Nat.ne_zero_of_mem_divisorsAntidiagonal hq).1
      have hq2 : q.2 ≠ 0 :=
        (Nat.ne_zero_of_mem_divisorsAntidiagonal hq).2
      by_cases hqLow : PrimeSupported (fun p ↦ p ≤ y) q.1
      · by_cases hqHigh : PrimeSupported (fun p ↦ ¬ p ≤ y) q.2
        · have hu := eq_primeBandParts_of_mul_eq (fun p ↦ p ≤ y)
            (Nat.mem_divisorsAntidiagonal.mp hq).1 hqLow hqHigh
          exact (hqne (Prod.ext hu.1 hu.2)).elim
        · rw [hhigh q.2 hq2 hqHigh, mul_zero]
      · rw [hlow q.1 hq1 hqLow, zero_mul]
    · intro hnot
      exact (hnot hmem).elim
  · intro q hq hqne
    have hq1 : q.1 ≠ 0 :=
      (Nat.ne_zero_of_mem_divisorsAntidiagonal hq).1
    have hq2 : q.2 ≠ 0 :=
      (Nat.ne_zero_of_mem_divisorsAntidiagonal hq).2
    by_cases hqLow : PrimeSupported (fun p ↦ p ≤ y) q.1
    · by_cases hqHigh : PrimeSupported (fun p ↦ ¬ p ≤ y) q.2
      · have hu := eq_primeBandParts_of_mul_eq (fun p ↦ p ≤ y)
          (Nat.mem_divisorsAntidiagonal.mp hq).1 hqLow hqHigh
        exact (hqne (Prod.ext hu.1 hu.2)).elim
      · rw [gsRealShift_apply_of_ne_zero eta high hq2,
          hhigh q.2 hq2 hqHigh, mul_zero, mul_zero]
    · rw [hlow q.1 hq1 hqLow, zero_mul]
  · intro hnot
    exact (hnot hmem).elim

/-- Exact whole-alternating-low formula for the first source secondary
coefficient. -/
theorem gsA10FirstSecondaryCoefficient_apply
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (eta : ℝ) {n : ℕ} (hn : 0 < n) :
    (gsA10TwoBlockAlternatingLow f P₁ P₂ y *
        gsRealShift eta (gsA9HighArithmetic f y)) n =
      ((gsA10ShiuWeight y eta n : ℝ) : ℂ) *
        finiteHalaszTypicalCoefficient f P₁ P₂ n := by
  have hhigh : ∀ e, e ≠ 0 →
      ¬ PrimeSupported (fun p ↦ ¬ p ≤ y) e →
        gsA9HighArithmetic f y e = 0 := by
    intro e he hnot
    rw [gsA9HighArithmetic_apply_of_ne_zero f y he]
    unfold gsA9High primeBandCoefficient
    rw [if_neg]
    intro hs
    apply hnot
    exact ⟨hs.1, fun p hp ↦ by
      have := hs.2 p hp
      omega⟩
  rw [low_mul_shift_high_apply
    (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
    (gsA9HighArithmetic f y) y eta hn
    (fun d hd hnot ↦
      gsA10TwoBlockAlternatingLow_eq_zero_of_not_lowSupported
        f P₁ P₂ y hd hnot) hhigh]
  rw [gsA10TwoBlockAlternatingLow_mul_high_eq_typical
    hmul P₁ P₂ y hQ₂ hQ₃]
  rw [show toArithmeticFunction
      (finiteHalaszTypicalCoefficient f P₁ P₂) n =
        finiteHalaszTypicalCoefficient f P₁ P₂ n by
      simp [toArithmeticFunction, hn.ne']]
  rw [gsA10ShiuWeight, if_neg hn.ne']

/-- The first secondary coefficient is pointwise dominated by the single
multiplicative Shiu weight. -/
theorem norm_gsA10FirstSecondaryCoefficient_le_shiuWeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (eta : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖(gsA10TwoBlockAlternatingLow f P₁ P₂ y *
        gsRealShift eta (gsA9HighArithmetic f y)) n‖ ≤
      gsA10ShiuWeight y eta n := by
  rw [gsA10FirstSecondaryCoefficient_apply
    hmul P₁ P₂ y hQ₂ hQ₃ eta hn, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gsA10ShiuWeight_nonneg y eta n)]
  apply mul_le_of_le_one_right (gsA10ShiuWeight_nonneg y eta n)
  unfold finiteHalaszTypicalCoefficient
  split
  · exact hbound n hn
  · simp

/-- The whole first A.10 secondary prefix is bounded by one Shiu partial
sum, with no four-term triangle inequality. -/
theorem norm_gsA10TwoBlockFirstSecondaryPrefix_le_partialSum
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (eta : ℝ) :
    ‖gsA10FirstSecondaryPrefix
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y) X eta‖ ≤
      HalberstamScratch.partialSum (gsA10ShiuWeight y eta) X := by
  unfold gsA10FirstSecondaryPrefix
  apply norm_positivePrefixSum_le_partialSum
  intro n hnmem
  apply norm_gsA10FirstSecondaryCoefficient_le_shiuWeight
    hmul hbound P₁ P₂ y hQ₂ hQ₃ eta
  have hnone := (Finset.mem_Icc.mp hnmem).1
  omega

/-- Fully explicit Shiu bound for the first source Lemma 2.4 secondary
prefix at the canonical shift. -/
theorem norm_gsA10TwoBlockFirstSecondaryPrefix_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 2 ≤ y) (hyX : y ≤ X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    ‖gsA10FirstSecondaryPrefix
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y) X (Real.log (y : ℝ))⁻¹‖ ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (X : ℝ) / Real.log (X : ℝ) *
          Real.exp
            (PrimeEstimates.primeReciprocals y +
              (Real.log 2 + 2 * PrimeEstimates.mertensBound) +
              EulerQuantitative.primeQuadraticConstant) := by
  exact (norm_gsA10TwoBlockFirstSecondaryPrefix_le_partialSum
    hmul hbound P₁ P₂ y X hQ₂ hQ₃
      (Real.log (y : ℝ))⁻¹).trans
    (gsA10ShiuWeight_partialSum_le hy hyX)

/-- A fixed source-independent constant for the two A.10 Shiu sums. -/
def gsA10ShiuConstant : ℝ :=
  (HalberstamScratch.explicitMassConstant 1 1 + 1) *
    Real.exp (Real.log 2 + 3 * PrimeEstimates.mertensBound +
      EulerQuantitative.primeQuadraticConstant)

theorem gsA10ShiuConstant_nonneg : 0 ≤ gsA10ShiuConstant := by
  unfold gsA10ShiuConstant
  exact mul_nonneg
    (add_nonneg
      (HalberstamScratch.explicitMassConstant_nonneg
        (by norm_num) (by norm_num)) zero_le_one)
    (Real.exp_nonneg _)

/-- Fixed-constant `X / log X * log y` form of the first secondary bound. -/
theorem norm_gsA10TwoBlockFirstSecondaryPrefix_le_log
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 2 ≤ y) (hyX : y ≤ X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    ‖gsA10FirstSecondaryPrefix
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y) X (Real.log (y : ℝ))⁻¹‖ ≤
      gsA10ShiuConstant * (X : ℝ) / Real.log (X : ℝ) *
        Real.log (y : ℝ) := by
  have hraw := norm_gsA10TwoBlockFirstSecondaryPrefix_le
    hmul hbound P₁ P₂ hy hyX hQ₂ hQ₃
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hmertens := PrimeEstimates.abs_primeReciprocals_sub_log_log_le hy
  have hprime : PrimeEstimates.primeReciprocals y ≤
      Real.log (Real.log (y : ℝ)) + PrimeEstimates.mertensBound := by
    have := le_of_abs_le hmertens
    linarith
  have harg :
      PrimeEstimates.primeReciprocals y +
          (Real.log 2 + 2 * PrimeEstimates.mertensBound) +
          EulerQuantitative.primeQuadraticConstant ≤
        Real.log (Real.log (y : ℝ)) +
          (Real.log 2 + 3 * PrimeEstimates.mertensBound +
            EulerQuantitative.primeQuadraticConstant) := by
    linarith
  have hexp :
      Real.exp
          (PrimeEstimates.primeReciprocals y +
            (Real.log 2 + 2 * PrimeEstimates.mertensBound) +
            EulerQuantitative.primeQuadraticConstant) ≤
        Real.log (y : ℝ) *
          Real.exp (Real.log 2 + 3 * PrimeEstimates.mertensBound +
            EulerQuantitative.primeQuadraticConstant) := by
    calc
      _ ≤ Real.exp
          (Real.log (Real.log (y : ℝ)) +
            (Real.log 2 + 3 * PrimeEstimates.mertensBound +
              EulerQuantitative.primeQuadraticConstant)) :=
        Real.exp_le_exp.mpr harg
      _ = _ := by rw [Real.exp_add, Real.exp_log hlogy]
  have hfactor : 0 ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (X : ℝ) / Real.log (X : ℝ) := by
    exact div_nonneg
      (mul_nonneg
        (add_nonneg
          (HalberstamScratch.explicitMassConstant_nonneg
            (by norm_num) (by norm_num)) zero_le_one)
        (Nat.cast_nonneg _)) hlogX.le
  calc
    _ ≤ (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (X : ℝ) / Real.log (X : ℝ) *
          Real.exp
            (PrimeEstimates.primeReciprocals y +
              (Real.log 2 + 2 * PrimeEstimates.mertensBound) +
              EulerQuantitative.primeQuadraticConstant) := hraw
    _ ≤ (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (X : ℝ) / Real.log (X : ℝ) *
          (Real.log (y : ℝ) *
            Real.exp (Real.log 2 + 3 * PrimeEstimates.mertensBound +
              EulerQuantitative.primeQuadraticConstant)) :=
      mul_le_mul_of_nonneg_left hexp hfactor
    _ = gsA10ShiuConstant * (X : ℝ) / Real.log (X : ℝ) *
        Real.log (y : ℝ) := by
      unfold gsA10ShiuConstant
      ring

/-- Exact residual form of the complete global secondary scalar: the first
term is source-small and the full-to-window discrepancy is zero, leaving
only the genuine integrated generalized-Mangoldt secondary. -/
theorem gsA10TwoBlockGlobalSecondaryError_le_firstLog_add_second
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 2 ≤ y) (hyX : y ≤ X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    gsA10TwoBlockGlobalSecondaryError f hmul P₁ P₂ y X
        (Real.log (y : ℝ))⁻¹ ≤
      gsA10ShiuConstant * (X : ℝ) / Real.log (X : ℝ) *
          Real.log (y : ℝ) +
        ‖gsA10SecondSecondaryPrefix
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y) X
          (Real.log (y : ℝ))⁻¹‖ := by
  rw [gsA10TwoBlockGlobalSecondaryError_eq_two_secondaries
    hmul P₁ P₂ (by omega) (Real.log (y : ℝ))⁻¹]
  exact add_le_add
    (norm_gsA10TwoBlockFirstSecondaryPrefix_le_log
      hmul hbound P₁ P₂ hy hyX hQ₂ hQ₃) le_rfl

end

end Erdos67.MRHalaszBands
