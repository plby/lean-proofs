import ErdosProblems.Erdos421.SchwartzWindowMultiplier
import ErdosProblems.Erdos421.PrimePolynomialSupport

/-! # Reflection of window multipliers and Dirichlet frequencies -/

namespace Erdos421

open Complex FourierTransform
open scoped SchwartzMap ComplexConjugate

noncomputable def reflectedSchwartz (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv φ

theorem reflectedSchwartz_apply (φ : 𝓢(ℝ, ℂ)) (x : ℝ) : reflectedSchwartz φ x = φ (-x) := rfl

theorem fourier_reflectedSchwartz (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (reflectedSchwartz φ) ξ = 𝓕 φ (-ξ) := by
  have h := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) (φ : ℝ → ℂ) ξ
  simpa only [SchwartzMap.fourier_coe, reflectedSchwartz,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using! h

theorem windowMultiplier_reflected (φ : 𝓢(ℝ, ℂ)) (δ ρ t : ℝ) :
    windowMultiplier (reflectedSchwartz φ) δ ρ t = windowMultiplier φ δ ρ (-t) := by
  simp only [windowMultiplier, fourier_reflectedSchwartz, neg_div, mul_neg]

theorem oscillatoryPhase_conj (ω t : ℝ) :
    conj (oscillatoryPhase ω t) = oscillatoryPhase ω (-t) := by
  unfold oscillatoryPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

theorem dirichletPolynomial_reflected (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (σ t : ℝ) :
    dirichletPolynomial S a (σ + ((-t : ℝ) : ℂ) * I) =
      conj (dirichletPolynomial S (fun n ↦ conj (a n)) (σ + t * I)) := by
  rw [dirichletPolynomial_eq_exponentialSum S a hS σ (-t),
    dirichletPolynomial_eq_exponentialSum S (fun n ↦ conj (a n)) hS σ t]
  simp only [exponentialSum, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal,
    oscillatoryPhase_conj, neg_neg]

theorem primeDirichletBlock_reflected (M N : ℕ) (σ t : ℝ) :
    primeDirichletBlock M N (σ + ((-t : ℝ) : ℂ) * I) =
      conj (primeDirichletBlock M N (σ + t * I)) := by
  have hp : ∀ n ∈ primeBlockSupport M N, 0 < n := fun _ hn ↦ (Finset.mem_filter.mp hn).2.pos
  rw [primeDirichletBlock_eq_polynomial, primeDirichletBlock_eq_polynomial,
    dirichletPolynomial_reflected _ _ hp]
  simp only [map_one]

end Erdos421
