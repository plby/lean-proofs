import ErdosProblems.Erdos421.WeightedDirichletMeanSquare
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # Exact Fourier and Plancherel identities for smooth Dirichlet windows -/

namespace Erdos421

open Complex MeasureTheory FourierTransform
open scoped SchwartzMap

theorem fourier_schwartz_translate (φ : 𝓢(ℝ, ℂ)) (c ξ : ℝ) :
    𝓕 (φ.compSubConstCLM ℂ c) ξ =
      oscillatoryPhase c (-2 * Real.pi * ξ) * 𝓕 φ ξ := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ ℝ) (φ : ℝ → ℂ) (-c)) ξ
  have hleft : VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
      ((φ : ℝ → ℂ) ∘ fun x ↦ x + -c) ξ = 𝓕 (φ.compSubConstCLM ℂ c) ξ := by rfl
  rw [hleft] at h
  have hphase : (Real.fourierChar ((innerₗ ℝ) (-c) ξ) : ℂ) =
      oscillatoryPhase c (-2 * Real.pi * ξ) := by
    rw [Real.fourierChar_apply]
    simp only [innerₗ_apply_apply, RCLike.inner_apply, RCLike.conj_to_real]
    unfold oscillatoryPhase
    congr 1
    push_cast
    ring
  simpa only [Circle.smul_def, smul_eq_mul, hphase] using! h

noncomputable def schwartzDirichletWindow (S : Finset ℕ) (a : ℕ → ℂ) (σ : ℝ)
    (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  ∑ n ∈ S, (a n * ((n : ℝ) ^ (-σ) : ℝ)) • φ.compSubConstCLM ℂ (Real.log n)

theorem schwartzDirichletWindow_apply (S : Finset ℕ) (a : ℕ → ℂ) (σ : ℝ)
    (φ : 𝓢(ℝ, ℂ)) (y : ℝ) :
    schwartzDirichletWindow S a σ φ y =
      ∑ n ∈ S, (a n * ((n : ℝ) ^ (-σ) : ℝ)) * φ (y - Real.log n) := by
  simp only [schwartzDirichletWindow, sum_apply, smul_apply,
    SchwartzMap.compSubConstCLM_apply, smul_eq_mul]

theorem fourier_schwartzDirichletWindow (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (schwartzDirichletWindow S a σ φ) ξ =
      dirichletPolynomial S a (σ + (2 * Real.pi * ξ : ℝ) * I) * 𝓕 φ ξ := by
  rw [schwartzDirichletWindow, fourier_sum]
  simp only [fourier_smul, sum_apply, smul_apply, smul_eq_mul]
  simp_rw [fourier_schwartz_translate]
  rw [dirichletPolynomial_eq_exponentialSum S a hS σ]
  unfold exponentialSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [show -2 * Real.pi * ξ = -(2 * Real.pi * ξ) by ring]
  ring

theorem schwartzDirichletWindow_plancherel (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    (∫ y : ℝ, ‖schwartzDirichletWindow S a σ φ y‖ ^ 2) =
      ∫ ξ : ℝ, ‖dirichletPolynomial S a (σ + (2 * Real.pi * ξ : ℝ) * I)‖ ^ 2 * ‖𝓕 φ ξ‖ ^ 2 := by
  rw [← SchwartzMap.integral_norm_sq_fourier (schwartzDirichletWindow S a σ φ)]
  simp_rw [fourier_schwartzDirichletWindow S a hS σ φ, norm_mul, mul_pow]

theorem schwartzDirichletWindow_sub (S : Finset ℕ) (a : ℕ → ℂ) (σ : ℝ)
    (φ ψ : 𝓢(ℝ, ℂ)) :
    schwartzDirichletWindow S a σ (φ - ψ) =
      schwartzDirichletWindow S a σ φ - schwartzDirichletWindow S a σ ψ := by
  unfold schwartzDirichletWindow
  simp only [map_sub, smul_sub, Finset.sum_sub_distrib]

theorem schwartzDirichletWindow_difference_plancherel (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (σ : ℝ) (φ ψ : 𝓢(ℝ, ℂ)) :
    (∫ y : ℝ, ‖schwartzDirichletWindow S a σ φ y - schwartzDirichletWindow S a σ ψ y‖ ^ 2) =
      ∫ ξ : ℝ, ‖dirichletPolynomial S a (σ + (2 * Real.pi * ξ : ℝ) * I)‖ ^ 2 *
        ‖𝓕 φ ξ - 𝓕 ψ ξ‖ ^ 2 := by
  have h := schwartzDirichletWindow_plancherel S a hS σ (φ - ψ)
  have hsub : 𝓕 (φ - ψ) = 𝓕 φ - 𝓕 ψ :=
    (fourierCLM ℂ 𝓢(ℝ, ℂ)).map_sub φ ψ
  simpa only [schwartzDirichletWindow_sub, sub_apply, hsub] using h

end Erdos421
