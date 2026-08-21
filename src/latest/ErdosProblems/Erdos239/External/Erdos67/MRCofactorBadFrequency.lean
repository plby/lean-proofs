import ErdosProblems.Erdos239.External.Erdos67.MRCofactorBlock

/-!
# Bad-frequency energy for the corrected Ramaré cofactor

This file combines the finite denominator-weighted cofactor polynomial with
the unconditional high-moment estimate for its prime factor.  The exact
height-zero truncation tail is retained, so the final result does not assume
an abstract cofactor bound.
-/

open scoped BigOperators ComplexConjugate Interval
open Finset

namespace Erdos67

noncomputable section

/-- Square energy of the corrected finite Ramaré product on frequencies
where its prime factor is at least `V`. -/
def ramareBadFrequencyTruncationEnergy
    (sigma : ℝ) (I : ℕ × ℕ) (S : Finset ℕ) (f : ℕ → ℂ)
    (T V : ℝ) : ℝ :=
  ∫ t in -T..T,
    ({t : ℝ | V ≤ ‖ramarePrimePerronFactorAt sigma I f t‖}.indicator
      (fun t ↦ Complex.normSq
        (ramarePrimePerronFactorAt sigma I f t *
          mrCofactorPerronPolynomial (primesInBlock I) S f sigma t))) t

theorem continuous_ramarePrimePerronFactorAt
    (sigma : ℝ) (I : ℕ × ℕ) (f : ℕ → ℂ) :
    Continuous (ramarePrimePerronFactorAt sigma I f) := by
  unfold ramarePrimePerronFactorAt logarithmicDirichletPolynomial
    logarithmicPhase
  fun_prop

theorem continuous_mrCofactorPerronPolynomial
    (P S : Finset ℕ) (f : ℕ → ℂ) (sigma : ℝ) :
    Continuous (mrCofactorPerronPolynomial P S f sigma) := by
  unfold mrCofactorPerronPolynomial logarithmicDirichletPolynomial
    logarithmicPhase
  fun_prop

/-- The elementary Chebyshev power trade used on the bad-frequency set. -/
theorem normSq_mul_le_div_pow_mul_pow
    {z w : ℂ} {V E : ℝ} {k : ℕ}
    (hV : 0 < V) (hE : 0 ≤ E) (hk : 0 < k)
    (hz : V ≤ ‖z‖) (hw : ‖w‖ ≤ E) :
    Complex.normSq (z * w) ≤
      E ^ 2 / V ^ (2 * (k - 1)) * ‖z‖ ^ (2 * k) := by
  have hVpow : 0 < V ^ (2 * (k - 1)) := pow_pos hV _
  have hzpow : V ^ (2 * (k - 1)) ≤
      ‖z‖ ^ (2 * (k - 1)) :=
    pow_le_pow_left₀ hV.le hz _
  have hwSq : ‖w‖ ^ 2 ≤ E ^ 2 :=
    (sq_le_sq₀ (norm_nonneg w) hE).2 hw
  rw [Complex.normSq_eq_norm_sq, norm_mul]
  rw [show E ^ 2 / V ^ (2 * (k - 1)) * ‖z‖ ^ (2 * k) =
      (E ^ 2 * ‖z‖ ^ (2 * k)) / V ^ (2 * (k - 1)) by ring]
  apply (le_div_iff₀ hVpow).2
  calc
    (‖z‖ * ‖w‖) ^ 2 * V ^ (2 * (k - 1)) =
        ‖w‖ ^ 2 * (‖z‖ ^ 2 * V ^ (2 * (k - 1))) := by ring
    _ ≤ E ^ 2 * (‖z‖ ^ 2 * ‖z‖ ^ (2 * (k - 1))) := by
      exact mul_le_mul hwSq
        (mul_le_mul_of_nonneg_left hzpow (sq_nonneg ‖z‖))
        (mul_nonneg (sq_nonneg ‖z‖) hVpow.le)
        (sq_nonneg E)
    _ = E ^ 2 * ‖z‖ ^ (2 * k) := by
      rw [← pow_add]
      congr 2
      omega

/-- Deterministic bad-frequency estimate for a uniformly bounded finite
cofactor.  Its hypotheses are discharged by the unconditional theorem
below. -/
theorem ramareBadFrequencyTruncationEnergy_le_of_uniform
    {sigma : ℝ} {I : ℕ × ℕ} {S : Finset ℕ} {f : ℕ → ℂ}
    {N k : ℕ} (hN : 0 < N)
    (hPN : ∀ p ∈ primesInBlock I, p ≤ N)
    {T V E : ℝ} (hT : 0 ≤ T) (hV : 0 < V) (hE : 0 ≤ E)
    (hk : 0 < k)
    (hcofactor : ∀ t ∈ Set.Icc (-T) T,
      ‖mrCofactorPerronPolynomial (primesInBlock I) S f sigma t‖ ≤ E) :
    ramareBadFrequencyTruncationEnergy sigma I S f T V ≤
      E ^ 2 / V ^ (2 * (k - 1)) *
        ((2 * T + 2 * Real.pi * (N ^ k : ℕ)) *
          ((k.factorial : ℝ) *
            (∑ p ∈ primesInBlock I,
              Complex.normSq (weightedPrimeCoefficient f sigma p)) ^ k)) := by
  let Q : ℝ → ℂ := ramarePrimePerronFactorAt sigma I f
  let R : ℝ → ℂ :=
    mrCofactorPerronPolynomial (primesInBlock I) S f sigma
  let bad : Set ℝ := {t | V ≤ ‖Q t‖}
  let base : ℝ → ℝ := fun t ↦ Complex.normSq (Q t * R t)
  let major : ℝ → ℝ := fun t ↦
    E ^ 2 / V ^ (2 * (k - 1)) * ‖Q t‖ ^ (2 * k)
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
  have hmajor : Continuous major := by
    dsimp only [major]
    fun_prop
  have hbaseInt : IntervalIntegrable (bad.indicator base)
      MeasureTheory.volume (-T) T := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp (hbase.intervalIntegrable (-T) T)).indicator hbad
  have hmajorInt : IntervalIntegrable major MeasureTheory.volume (-T) T :=
    hmajor.intervalIntegrable _ _
  have hpoint : ∀ t ∈ Set.Icc (-T) T,
      bad.indicator base t ≤ major t := by
    intro t ht
    by_cases htbad : t ∈ bad
    · rw [Set.indicator_of_mem htbad]
      exact normSq_mul_le_div_pow_mul_pow hV hE hk htbad
        (hcofactor t ht)
    · simp only [Set.indicator, htbad, ↓reduceIte]
      dsimp only [major]
      positivity
  have hmono := intervalIntegral.integral_mono_on
    (by linarith : -T ≤ T) hbaseInt hmajorInt hpoint
  have hflip :
      (∫ t in -T..T, ‖Q t‖ ^ (2 * k)) =
        ∫ t in -T..T,
          ‖logarithmicDirichletPolynomial (primesInBlock I)
            (weightedPrimeCoefficient f sigma) t‖ ^ (2 * k) := by
    dsimp only [Q, ramarePrimePerronFactorAt]
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (a := -T) (b := T)
        (fun t ↦ ‖logarithmicDirichletPolynomial (primesInBlock I)
          (weightedPrimeCoefficient f sigma) t‖ ^ (2 * k)))
  have hmoment := primePolynomial_highMoment_intervalIntegral_le
    (k := k) (fun p hp ↦ (mem_primesInBlock.mp hp).1)
    hN hPN (weightedPrimeCoefficient f sigma) hT
  unfold ramareBadFrequencyTruncationEnergy
  change (∫ t in -T..T, bad.indicator base t) ≤ _
  calc
    (∫ t in -T..T, bad.indicator base t) ≤
        ∫ t in -T..T, major t := hmono
    _ = E ^ 2 / V ^ (2 * (k - 1)) *
        (∫ t in -T..T, ‖Q t‖ ^ (2 * k)) := by
      dsimp only [major]
      rw [intervalIntegral.integral_const_mul]
    _ ≤ E ^ 2 / V ^ (2 * (k - 1)) *
        ((2 * T + 2 * Real.pi * (N ^ k : ℕ)) *
          ((k.factorial : ℝ) *
            (∑ p ∈ primesInBlock I,
              Complex.normSq (weightedPrimeCoefficient f sigma p)) ^ k)) := by
      rw [hflip]
      exact mul_le_mul_of_nonneg_left hmoment (by positivity)

/-- Explicit uniform size of the finite cofactor on a power-sized prime
block.  The first term is the beta-averaged Euler suppression and the
second is the exact absolute truncation tail. -/
def mrPowerBlockCofactorPerronBound
    (C : ℝ) (K A X Y : ℕ) (I : ℕ × ℕ) (S : Finset ℕ)
    (f : ℕ → ℂ) : ℝ :=
  Real.exp
      (Real.log (riemannZeta (EulerResidue.taoExponent Y : ℂ)).re -
        Real.exp (-1) *
          ((A : ℝ) -
            2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
              Real.log (Y + 1 : ℝ) -
            (Real.log (K : ℝ) +
              2 * PrimeEstimates.mertensBound)) +
        3 * EulerQuantitative.primeQuadraticConstant) +
    mrCofactorLSeriesTail (primesInBlock I) S f
      (MRHalaszEuler.halaszPoint Y 0)

theorem mrPowerBlockCofactorPerronBound_nonneg
    (C : ℝ) (K A X Y : ℕ) (I : ℕ × ℕ) (S : Finset ℕ)
    (f : ℕ → ℂ) :
    0 ≤ mrPowerBlockCofactorPerronBound C K A X Y I S f := by
  unfold mrPowerBlockCofactorPerronBound mrCofactorLSeriesTail
  apply add_nonneg (Real.exp_pos _).le
  exact tsum_nonneg fun n ↦ by
    split_ifs
    · exact le_rfl
    · exact norm_nonneg _

/-- Fully unconditional bad-frequency square-energy bound for the finite
denominator-weighted cofactor.  Every analytic input is discharged here:
the cofactor bound comes from the beta-average Euler theorem, its truncation
error is the exact height-independent tail, and the prime factor is handled
by the proved `2k`-th mean-value estimate. -/
theorem exists_uniform_ramareBadFrequencyTruncationEnergy_powerBlock_le :
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
        ramareBadFrequencyTruncationEnergy
            (EulerResidue.taoExponent Y) I S f T V ≤
          (mrPowerBlockCofactorPerronBound C K A X Y I S f) ^ 2 /
              V ^ (2 * (k - 1)) *
            ((2 * T + 2 * Real.pi * (I.2 ^ k : ℕ)) *
              ((k.factorial : ℝ) *
                (∑ p ∈ primesInBlock I,
                  Complex.normSq
                    (weightedPrimeCoefficient f
                      (EulerResidue.taoExponent Y) p)) ^ k)) := by
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
      constructor
      · exact (neg_le_neg hTX).trans ht.1
      · exact ht.2.trans hTX
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
  exact ramareBadFrequencyTruncationEnergy_le_of_uniform
    (N := I.2) (k := k) (by omega)
    (fun p hp ↦ (mem_primesInBlock.mp hp).2.2)
    hT hV hE hk hcofactor

end

end Erdos67
