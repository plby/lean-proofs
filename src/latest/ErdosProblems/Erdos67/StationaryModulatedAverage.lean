import ErdosProblems.Erdos67.StationaryAtomKernel

/-!
# Modulated coordinate averages

The spectral quadratic identity identifies the second moment of an average
along a dilation with the mass of the corresponding frequency fiber in the limit.
-/

open scoped BigOperators ComplexConjugate Topology
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem fourier_sub_argument (h : ℤ) (θ η : FrequencyCircle) :
    fourier h (θ - η) = fourier h θ * conj (fourier h η) := by
  change (AddCircle.toCircle (h • (θ - η)) : ℂ) =
    (AddCircle.toCircle (h • θ) : ℂ) * conj (AddCircle.toCircle (h • η) : ℂ)
  rw [zsmul_sub, sub_eq_add_neg, AddCircle.toCircle_add, Circle.coe_mul,
    AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

theorem fourier_nsmul_argument (h d : ℕ) (θ : FrequencyCircle) :
    fourier (h : ℤ) (d • θ) = fourier ((d * h : ℕ) : ℤ) θ := by
  change (AddCircle.toCircle ((h : ℤ) • (d • θ)) : ℂ) =
    (AddCircle.toCircle (((d * h : ℕ) : ℤ) • θ) : ℂ)
  congr 2
  simp only [natCast_zsmul, mul_nsmul]

noncomputable def modulationCoefficients (N : ℕ) (η : FrequencyCircle) (j : Fin (N + 1)) : ℂ :=
  conj (fourier (j.val : ℤ) η) / ((N + 1 : ℕ) : ℂ)

noncomputable def modulatedAverage (N d : ℕ) (η : FrequencyCircle) (ω : Configuration) : ℂ :=
  coordinatePolynomial (fun j : Fin (N + 1) ↦ d * j.val) (modulationCoefficients N η) ω

theorem continuous_modulatedAverage (N d : ℕ) (η : FrequencyCircle) :
    Continuous (modulatedAverage N d η) := continuous_coordinatePolynomial _ _

theorem frequencyPolynomial_modulation (N d : ℕ) (η θ : FrequencyCircle) :
    frequencyPolynomial (fun j : Fin (N + 1) ↦ d * j.val) (modulationCoefficients N η) θ =
      atomKernel N (d • θ - η) := by
  simp only [frequencyPolynomial, modulationCoefficients, atomKernel,
    geometricPolynomial, signPolynomial, Complex.ofReal_one, one_mul, sum_div]
  apply sum_congr rfl
  intro j _
  rw [fourier_sub_argument, fourier_nsmul_argument]
  ring

theorem integral_modulatedAverage_normSq (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (N d : ℕ) (η : FrequencyCircle) :
    (∫ ω, Complex.normSq (modulatedAverage N d η ω) ∂(Q : Measure Configuration)) =
      ∫ θ, Complex.normSq (atomKernel N (d • θ - η)) ∂(σ : Measure FrequencyCircle) := by
  have he := spectral_quadratic_identity Q hQ σ hσ
    (fun j : Fin (N + 1) ↦ d * j.val) (modulationCoefficients N η)
  simpa only [modulatedAverage, frequencyPolynomial_modulation] using he

theorem tendsto_modulatedAverage_second_moment (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (d : ℕ) (η : FrequencyCircle) :
    Tendsto (fun N ↦ ∫ ω, Complex.normSq (modulatedAverage N d η ω)
      ∂(Q : Measure Configuration)) atTop
        (nhds ((σ : Measure FrequencyCircle).real {θ | d • θ = η})) := by
  have ht := tendsto_integral_atomKernel σ (fun θ ↦ d • θ - η)
    ((continuous_id.nsmul d).sub continuous_const)
  simpa only [sub_eq_zero, integral_modulatedAverage_normSq Q hQ σ hσ] using ht

noncomputable def signSequenceAverage (N : ℕ) (η : FrequencyCircle) (x : ℤ → Bool) : ℂ :=
  ∑ j : Fin (N + 1), modulationCoefficients N η j * (signValue (x (j.val : ℤ)) : ℂ)

theorem continuous_signSequenceAverage (N : ℕ) (η : FrequencyCircle) :
    Continuous (signSequenceAverage N η) :=
  continuous_finsetSum _ fun j _ ↦ continuous_const.mul
    (Complex.continuous_ofReal.comp
      ((continuous_of_discreteTopology : Continuous signValue).comp (continuous_apply (j.val : ℤ))))

theorem signSequenceAverage_base (N : ℕ) (η : FrequencyCircle) (ω : Configuration) :
    signSequenceAverage N η ω.1 = modulatedAverage N 1 η ω := by
  simp only [signSequenceAverage, modulatedAverage, coordinatePolynomial, coordinate, one_mul]

theorem signSequenceAverage_dilation (N : ℕ) (η : FrequencyCircle) (d : ℕ+) (ω : Configuration) :
    signSequenceAverage N η (signDilation d ω) = modulatedAverage N d.val η ω := by
  simp only [signSequenceAverage, modulatedAverage, coordinatePolynomial, coordinate,
    signDilation, Nat.cast_mul]

theorem modulatedAverage_conditional_dilation (Q : ProbabilityMeasure Configuration)
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (N : ℕ) (η : FrequencyCircle) (d : ℕ+) :
    (∫ ω, Complex.normSq (modulatedAverage N 1 η ω) ∂(Q : Measure Configuration)) =
      (d.val : ℝ) * ∫ ω, residueZeroIndicator d ω * Complex.normSq (modulatedAverage N d.val η ω)
        ∂(Q : Measure Configuration) := by
  let F : C((ℤ → Bool), ℝ) := ⟨fun x ↦ Complex.normSq (signSequenceAverage N η x),
    Complex.continuous_normSq.comp (continuous_signSequenceAverage N η)⟩
  have he := hCD d F
  simpa only [F, ContinuousMap.coe_mk, conditionalDilationTest,
    signSequenceAverage_base, signSequenceAverage_dilation] using he

end Erdos67.StationaryModel
