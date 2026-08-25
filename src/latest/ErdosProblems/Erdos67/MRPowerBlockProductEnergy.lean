import ErdosProblems.Erdos67.MRCofactorBadFrequency
import ErdosProblems.Erdos67.MRPrimeBlockSquareMass

/-!
# The complete good/bad energy bound for one Ramaré power block

This file performs the frequency split for the *finite rectangular product*
which occurs after the denominator-corrected Ramaré decomposition.  On the
good set the prime factor is small and the cofactor is bounded by the
beta-averaged Halász estimate.  On the complementary set we use the proved
prime-polynomial high-moment bound from `MRCofactorBadFrequency`.
-/

open scoped BigOperators ComplexConjugate Interval
open Finset

namespace Erdos67

noncomputable section

/-- The unrestricted square energy of the finite prime/cofactor product. -/
def ramareTruncationProductEnergy
    (sigma : ℝ) (I : ℕ × ℕ) (S : Finset ℕ) (f : ℕ → ℂ)
    (T : ℝ) : ℝ :=
  ∫ t in -T..T, Complex.normSq
    (ramarePrimePerronFactorAt sigma I f t *
      mrCofactorPerronPolynomial (primesInBlock I) S f sigma t)

/-- The elementary good/bad split for a finite Ramaré product. -/
theorem ramareTruncationProductEnergy_le_good_add_bad
    {sigma : ℝ} {I : ℕ × ℕ} {S : Finset ℕ} {f : ℕ → ℂ}
    {T V E : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) (hE : 0 ≤ E)
    (hcofactor : ∀ t ∈ Set.Icc (-T) T,
      ‖mrCofactorPerronPolynomial (primesInBlock I) S f sigma t‖ ≤ E) :
    ramareTruncationProductEnergy sigma I S f T ≤
      2 * T * (V ^ 2 * E ^ 2) +
        ramareBadFrequencyTruncationEnergy sigma I S f T V := by
  let Q : ℝ → ℂ := ramarePrimePerronFactorAt sigma I f
  let R : ℝ → ℂ :=
    mrCofactorPerronPolynomial (primesInBlock I) S f sigma
  let bad : Set ℝ := {t | V ≤ ‖Q t‖}
  let base : ℝ → ℝ := fun t ↦ Complex.normSq (Q t * R t)
  let goodMajor : ℝ → ℝ := fun _ ↦ V ^ 2 * E ^ 2
  let rhs : ℝ → ℝ := fun t ↦ goodMajor t + bad.indicator base t
  have hQ : Continuous Q :=
    continuous_ramarePrimePerronFactorAt sigma I f
  have hR : Continuous R :=
    continuous_mrCofactorPerronPolynomial (primesInBlock I) S f sigma
  have hbad : MeasurableSet bad := by
    exact measurableSet_le measurable_const hQ.norm.measurable
  have hbase : Continuous base := by
    have hbaseEq : base = fun t ↦ ‖Q t * R t‖ ^ 2 := by
      funext t
      dsimp only [base]
      rw [Complex.normSq_eq_norm_sq]
    rw [hbaseEq]
    exact (hQ.mul hR).norm.pow 2
  have hbaseInt : IntervalIntegrable base MeasureTheory.volume (-T) T :=
    hbase.intervalIntegrable _ _
  have hgoodInt : IntervalIntegrable goodMajor MeasureTheory.volume (-T) T := by
    exact intervalIntegrable_const
  have hbadInt : IntervalIntegrable (bad.indicator base)
      MeasureTheory.volume (-T) T := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp hbaseInt).indicator hbad
  have hrhsInt : IntervalIntegrable rhs MeasureTheory.volume (-T) T :=
    hgoodInt.add hbadInt
  have hpoint : ∀ t ∈ Set.Icc (-T) T, base t ≤ rhs t := by
    intro t ht
    by_cases htbad : t ∈ bad
    · dsimp only [rhs]
      rw [Set.indicator_of_mem htbad]
      have : 0 ≤ goodMajor t := by
        dsimp only [goodMajor]
        positivity
      linarith
    · have hprime : ‖Q t‖ ≤ V := by
        have : ¬ V ≤ ‖Q t‖ := htbad
        exact (not_le.mp this).le
      have hmul : ‖Q t‖ * ‖R t‖ ≤ V * E :=
        mul_le_mul hprime (hcofactor t ht) (norm_nonneg _) hV
      have hsq : (‖Q t‖ * ‖R t‖) ^ 2 ≤ (V * E) ^ 2 :=
        (sq_le_sq₀
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_nonneg hV hE)).2 hmul
      dsimp only [rhs]
      simp only [Set.indicator, htbad, ↓reduceIte, add_zero]
      dsimp only [base, goodMajor]
      rw [Complex.normSq_eq_norm_sq, norm_mul]
      nlinarith
  have hmono := intervalIntegral.integral_mono_on
    (by linarith : -T ≤ T) hbaseInt hrhsInt hpoint
  unfold ramareTruncationProductEnergy
  change (∫ t in -T..T, base t) ≤ _
  calc
    (∫ t in -T..T, base t) ≤ ∫ t in -T..T, rhs t := hmono
    _ = (∫ t in -T..T, goodMajor t) +
        ∫ t in -T..T, bad.indicator base t := by
      dsimp only [rhs]
      rw [intervalIntegral.integral_add hgoodInt hbadInt]
    _ = 2 * T * (V ^ 2 * E ^ 2) +
        ramareBadFrequencyTruncationEnergy sigma I S f T V := by
      unfold goodMajor ramareBadFrequencyTruncationEnergy
      change (∫ _ in -T..T, V ^ 2 * E ^ 2) + _ = _
      rw [intervalIntegral.integral_const]
      change (T - -T) * (V ^ 2 * E ^ 2) + _ = _
      dsimp only [bad, base, Q, R]
      ring

/-- The explicit bound produced by the full good/bad split on a power
block.  It is stated separately so parameter choices can use the same
quantity without unfolding the two contributions. -/
def mrPowerBlockProductEnergyBound
    (C : ℝ) (K A X Y k : ℕ) (I : ℕ × ℕ) (S : Finset ℕ)
    (f : ℕ → ℂ) (T V : ℝ) : ℝ :=
  let E := mrPowerBlockCofactorPerronBound C K A X Y I S f
  2 * T * (V ^ 2 * E ^ 2) +
    E ^ 2 / V ^ (2 * (k - 1)) *
      ((2 * T + 2 * Real.pi * (I.2 ^ k : ℕ)) *
        ((k.factorial : ℝ) *
          (∑ p ∈ primesInBlock I,
            Complex.normSq
              (weightedPrimeCoefficient f
                (EulerResidue.taoExponent Y) p)) ^ k))

/-- Unconditional complete energy estimate for the finite rectangular
Ramaré product on one power-sized prime block. -/
theorem exists_uniform_ramareTruncationProductEnergy_powerBlock_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {I : ℕ × ℕ} {K : ℕ},
        3 ≤ I.1 → I.1 ≤ I.2 → 0 < K →
        I.2 ≤ (I.1 - 1) ^ K →
      ∀ {S : Finset ℕ} {f : ℕ → ℂ} {A X Y k : ℕ} {T V : ℝ},
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        (∀ n ∈ S, 0 < n) →
        2 ≤ Y → Y < X →
        MRArchimedeanNonpretentious f A X →
        0 < k → 0 ≤ T → T ≤ X → 0 < V →
        ramareTruncationProductEnergy
            (EulerResidue.taoExponent Y) I S f T ≤
          mrPowerBlockProductEnergyBound C K A X Y k I S f T V := by
  obtain ⟨C, hC, hEuler⟩ :=
    exists_uniform_norm_mrCofactorLSeries_powerBlock_le
  refine ⟨C, hC, ?_⟩
  intro I K hlo hI hK hpow S f A X Y k T V
    hmul hbound hSpos hY hYX hnonpret hk hT hTX hV
  let E : ℝ := mrPowerBlockCofactorPerronBound C K A X Y I S f
  have hE : 0 ≤ E :=
    mrPowerBlockCofactorPerronBound_nonneg C K A X Y I S f
  have hcofactor : ∀ t ∈ Set.Icc (-T) T,
      ‖mrCofactorPerronPolynomial (primesInBlock I) S f
        (EulerResidue.taoExponent Y) t‖ ≤ E := by
    intro t ht
    have htAbs : |t| ≤ X := by
      rw [abs_le]
      exact ⟨(neg_le_neg hTX).trans ht.1, ht.2.trans hTX⟩
    have hsline : 1 < (MRHalaszEuler.halaszPoint Y t).re := by
      rw [MRHalaszEuler.halaszPoint_re]
      exact EulerResidue.one_lt_taoExponent (show 1 < Y by omega)
    rw [mrCofactorPerronPolynomial_eq_LSeriesTruncation
      (primesInBlock I) S f (EulerResidue.taoExponent Y) t hSpos]
    change ‖mrCofactorLSeriesTruncation (primesInBlock I) S f
      (MRHalaszEuler.halaszPoint Y t)‖ ≤ E
    have htrunc := norm_mrCofactorLSeriesTruncation_le_full_add_tail
      (s := MRHalaszEuler.halaszPoint Y t)
      (primesInBlock I) S hbound hsline
    calc
      ‖mrCofactorLSeriesTruncation (primesInBlock I) S f
          (MRHalaszEuler.halaszPoint Y t)‖ ≤
        ‖mrCofactorLSeries (primesInBlock I) f
          (MRHalaszEuler.halaszPoint Y t)‖ +
            mrCofactorLSeriesTail (primesInBlock I) S f
              (MRHalaszEuler.halaszPoint Y t) := htrunc
      _ ≤ Real.exp
          (Real.log (riemannZeta
              (EulerResidue.taoExponent Y : ℂ)).re -
            Real.exp (-1) *
              ((A : ℝ) -
                2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
                  Real.log (Y + 1 : ℝ) -
                (Real.log (K : ℝ) +
                  2 * PrimeEstimates.mertensBound)) +
            3 * EulerQuantitative.primeQuadraticConstant) +
          mrCofactorLSeriesTail (primesInBlock I) S f
            (MRHalaszEuler.halaszPoint Y 0) := by
        rw [mrCofactorLSeriesTail_halaszPoint_eq_zero]
        exact add_le_add
          (hEuler hlo hI hK hpow hmul hbound hY hYX hnonpret t htAbs)
          le_rfl
      _ = E := by rfl
  have hsplit := ramareTruncationProductEnergy_le_good_add_bad
    hT hV.le hE hcofactor
  have hbad' := ramareBadFrequencyTruncationEnergy_le_of_uniform
    (N := I.2) (k := k) (by omega)
    (fun p hp ↦ (mem_primesInBlock.mp hp).2.2)
    hT hV hE hk hcofactor
  exact hsplit.trans (by
    dsimp [mrPowerBlockProductEnergyBound, E]
    gcongr)

/-- Version of the product bound with the prime square mass replaced by the
scalar p-series tail `1/(I.lo-1)`. -/
def mrPowerBlockProductEnergyScalarBound
    (C : ℝ) (K A X Y k : ℕ) (I : ℕ × ℕ) (S : Finset ℕ)
    (f : ℕ → ℂ) (T V : ℝ) : ℝ :=
  let E := mrPowerBlockCofactorPerronBound C K A X Y I S f
  2 * T * (V ^ 2 * E ^ 2) +
    E ^ 2 / V ^ (2 * (k - 1)) *
      ((2 * T + 2 * Real.pi * (I.2 ^ k : ℕ)) *
        ((k.factorial : ℝ) *
          (((I.1 - 1 : ℕ) : ℝ)⁻¹) ^ k))

theorem exists_uniform_ramareTruncationProductEnergy_powerBlock_scalar_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {I : ℕ × ℕ} {K : ℕ},
        3 ≤ I.1 → I.1 ≤ I.2 → 0 < K →
        I.2 ≤ (I.1 - 1) ^ K →
      ∀ {S : Finset ℕ} {f : ℕ → ℂ} {A X Y k : ℕ} {T V : ℝ},
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        (∀ n ∈ S, 0 < n) →
        2 ≤ Y → Y < X →
        MRArchimedeanNonpretentious f A X →
        0 < k → 0 ≤ T → T ≤ X → 0 < V →
        ramareTruncationProductEnergy
            (EulerResidue.taoExponent Y) I S f T ≤
          mrPowerBlockProductEnergyScalarBound C K A X Y k I S f T V := by
  obtain ⟨C, hC, hmain⟩ :=
    exists_uniform_ramareTruncationProductEnergy_powerBlock_le
  refine ⟨C, hC, ?_⟩
  intro I K hlo hI hK hpow S f A X Y k T V
    hmul hbound hSpos hY hYX hnonpret hk hT hTX hV
  have hbase := hmain hlo hI hK hpow hmul hbound hSpos hY hYX
    hnonpret hk hT hTX hV
  have hmass :=
    sum_normSq_weightedPrimeCoefficient_primesInBlock_le
      (I := I) (sigma := EulerResidue.taoExponent Y)
      (by omega : 2 ≤ I.1) hI hbound
      (EulerResidue.one_lt_taoExponent (show 1 < Y by omega)).le
  apply hbase.trans
  unfold mrPowerBlockProductEnergyBound
    mrPowerBlockProductEnergyScalarBound
  dsimp only
  gcongr
  · exact Finset.sum_nonneg fun p hp ↦ Complex.normSq_nonneg _

end

end Erdos67
