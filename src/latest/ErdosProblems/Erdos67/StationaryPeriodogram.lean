import ErdosProblems.Erdos67.StationaryFourierKernel

/-!
# Probability measures from finite sign periodograms

Each finite sign law gives a nonnegative continuous density of mass one on
the frequency circle. This provides the approximating spectral measures.
-/

open scoped BigOperators ComplexConjugate ENNReal
open Finset MeasureTheory

namespace Erdos67.StationaryModel

open FiniteEntropy

noncomputable def periodogramDensity {N : ℕ} (p : FinProb (Fin N → Bool))
    (θ : FrequencyCircle) : ℝ :=
  (∑ x, p x * Complex.normSq (signPolynomial N (fun j ↦ signValue (x j)) θ)) / N

theorem periodogramDensity_nonneg {N : ℕ} (p : FinProb (Fin N → Bool)) (θ : FrequencyCircle) :
    0 ≤ periodogramDensity p θ := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact sum_nonneg fun x _ ↦ mul_nonneg (prob_nonneg p x) (Complex.normSq_nonneg _)

theorem continuous_periodogramDensity {N : ℕ} (p : FinProb (Fin N → Bool)) :
    Continuous (periodogramDensity p) := by
  apply Continuous.div_const
  exact continuous_finsetSum _ fun x _ ↦ continuous_const.mul
    (Complex.continuous_normSq.comp (continuous_signPolynomial N (fun j ↦ signValue (x j))))

theorem integral_periodogramDensity {N : ℕ} (p : FinProb (Fin N → Bool)) (hN : 0 < N) :
    (∫ θ, periodogramDensity p θ ∂frequencyHaar) = 1 := by
  unfold periodogramDensity
  rw [integral_div, integral_finsetSum]
  · simp_rw [integral_const_mul, integral_signPolynomial_normSq, sq_signValue]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      ← sum_mul, stdSimplex.sum_eq_one, one_mul]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))
  · intro x _
    exact integrable_frequency_continuous _ (continuous_const.mul
      (Complex.continuous_normSq.comp (continuous_signPolynomial N (fun j ↦ signValue (x j)))))

noncomputable def periodogramMeasure {N : ℕ} (p : FinProb (Fin N → Bool)) (hN : 0 < N) :
    ProbabilityMeasure FrequencyCircle :=
  ⟨frequencyHaar.withDensity (fun θ ↦ ENNReal.ofReal (periodogramDensity p θ)), by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal
        (integrable_frequency_continuous _ (continuous_periodogramDensity p))
        (Filter.Eventually.of_forall (periodogramDensity_nonneg p)),
      integral_periodogramDensity p hN, ENNReal.ofReal_one]⟩

theorem integral_periodogramMeasure {N : ℕ} (p : FinProb (Fin N → Bool)) (hN : 0 < N)
    (F : FrequencyCircle → ℂ) :
    (∫ θ, F θ ∂(periodogramMeasure p hN : Measure FrequencyCircle)) =
      ∫ θ, (periodogramDensity p θ : ℂ) * F θ ∂frequencyHaar := by
  change (∫ θ, F θ ∂frequencyHaar.withDensity (fun θ ↦ ENNReal.ofReal (periodogramDensity p θ))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_periodogramDensity p).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ ↦ by
    dsimp only
    rw [ENNReal.toReal_ofReal (periodogramDensity_nonneg p θ)]
    rfl

theorem fourier_mul_periodogramDensity {N : ℕ} (p : FinProb (Fin N → Bool))
    (h : ℤ) (θ : FrequencyCircle) :
    fourier h θ * (periodogramDensity p θ : ℂ) =
      (∑ x, (p x : ℂ) *
        (fourier h θ * (Complex.normSq
          (signPolynomial N (fun j ↦ signValue (x j)) θ) : ℂ))) / N := by
  simp only [periodogramDensity, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_natCast]
  rw [← mul_div_assoc, mul_sum]
  apply congrArg (fun z : ℂ ↦ z / N)
  apply sum_congr rfl
  intro x _
  ring

theorem integral_fourier_periodogramMeasure {N : ℕ} (p : FinProb (Fin N → Bool)) (hN : 0 < N)
    (h : ℤ) :
    (∫ θ : FrequencyCircle, fourier h θ ∂(periodogramMeasure p hN : Measure FrequencyCircle)) =
      (∑ x, (p x : ℂ) * ∑ i : Fin N, ∑ j : Fin N,
        if h + (i.val : ℤ) = (j.val : ℤ) then
          ((signValue (x i) * signValue (x j) : ℝ) : ℂ) else 0) / N := by
  rw [integral_periodogramMeasure]
  simp_rw [mul_comm (_ : ℂ) (fourier h _), fourier_mul_periodogramDensity]
  rw [integral_div, integral_finsetSum]
  · apply congrArg (fun z : ℂ ↦ z / N)
    apply sum_congr rfl
    intro x _
    rw [integral_const_mul, integral_fourier_mul_signPolynomial_normSq]
  · intro x _
    exact integrable_frequency_continuous _ (continuous_const.mul
      ((fourier h).continuous.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_normSq.comp (continuous_signPolynomial N (fun j ↦ signValue (x j)))))))

end Erdos67.StationaryModel
