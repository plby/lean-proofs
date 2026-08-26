import ErdosProblems.Erdos67.StationaryPrimeBudget

/-!
# Finite Fourier kernels for the spectral construction

We use the normalized Haar measure on the circle of period one. The
periodogram identities are proved by finite expansion and orthogonality.
-/

open scoped BigOperators ComplexConjugate
open Finset MeasureTheory

namespace Erdos67.StationaryModel

abbrev FrequencyCircle := AddCircle (1 : ℝ)

noncomputable def frequencyHaar : Measure FrequencyCircle := AddCircle.haarAddCircle

instance : IsProbabilityMeasure frequencyHaar := inferInstanceAs
  (IsProbabilityMeasure (AddCircle.haarAddCircle (T := (1 : ℝ))))

theorem integrable_frequency_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : FrequencyCircle → E) (hF : Continuous F) : Integrable F frequencyHaar :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem integral_fourier_frequency (k : ℤ) :
    (∫ θ : FrequencyCircle, fourier k θ ∂frequencyHaar) = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  simpa [fourierCoeff, frequencyHaar, Pi.single_apply, eq_comm] using h

noncomputable def signPolynomial (N : ℕ) (a : Fin N → ℝ) (θ : FrequencyCircle) : ℂ :=
  ∑ j, (a j : ℂ) * fourier (j.val : ℤ) θ

theorem continuous_signPolynomial (N : ℕ) (a : Fin N → ℝ) : Continuous (signPolynomial N a) :=
  continuous_finsetSum _ fun j _ ↦ continuous_const.mul (fourier (j.val : ℤ)).continuous

theorem signPolynomial_normSq_expansion (N : ℕ) (a : Fin N → ℝ) (θ : FrequencyCircle) :
    (Complex.normSq (signPolynomial N a θ) : ℂ) =
      ∑ i : Fin N, ∑ j : Fin N,
        ((a i * a j : ℝ) : ℂ) * fourier ((i.val : ℤ) - (j.val : ℤ)) θ := by
  rw [← Complex.mul_conj]
  simp only [signPolynomial, map_sum, map_mul, Complex.conj_ofReal, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [sub_eq_add_neg, fourier_add, fourier_neg, Complex.ofReal_mul]
  ring

theorem fourier_mul_signPolynomial_normSq (N : ℕ) (a : Fin N → ℝ)
    (h : ℤ) (θ : FrequencyCircle) :
    fourier h θ * (Complex.normSq (signPolynomial N a θ) : ℂ) =
      ∑ i : Fin N, ∑ j : Fin N,
        ((a i * a j : ℝ) : ℂ) * fourier (h + (i.val : ℤ) - (j.val : ℤ)) θ := by
  rw [signPolynomial_normSq_expansion]
  simp only [mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [show h + (i.val : ℤ) - (j.val : ℤ) = h + ((i.val : ℤ) - (j.val : ℤ)) by omega,
    fourier_add]
  ring

theorem integral_fourier_mul_signPolynomial_normSq (N : ℕ) (a : Fin N → ℝ) (h : ℤ) :
    (∫ θ : FrequencyCircle, fourier h θ * (Complex.normSq (signPolynomial N a θ) : ℂ)
      ∂frequencyHaar) =
      ∑ i : Fin N, ∑ j : Fin N,
        if h + (i.val : ℤ) = (j.val : ℤ) then ((a i * a j : ℝ) : ℂ) else 0 := by
  simp_rw [fourier_mul_signPolynomial_normSq]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_fourier_frequency]
      simp only [sub_eq_zero]
      split_ifs <;> simp
    · intro j _
      exact integrable_frequency_continuous _ (continuous_const.mul (fourier _).continuous)
  · intro i _
    exact integrable_frequency_continuous _
      (continuous_finsetSum _ fun j _ ↦ continuous_const.mul (fourier _).continuous)

/-- Parseval for a finite real coefficient block. -/
theorem integral_signPolynomial_normSq (N : ℕ) (a : Fin N → ℝ) :
    (∫ θ : FrequencyCircle, Complex.normSq (signPolynomial N a θ) ∂frequencyHaar) =
      ∑ i, a i ^ 2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have h := integral_fourier_mul_signPolynomial_normSq N a 0
  simpa only [fourier_zero, one_mul, zero_add, Int.natCast_inj, Fin.val_inj,
    Finset.sum_ite_eq, Finset.sum_ite_eq', mem_univ, ite_true, ← pow_two, Complex.ofReal_sum,
    Complex.ofReal_pow] using h

end Erdos67.StationaryModel
