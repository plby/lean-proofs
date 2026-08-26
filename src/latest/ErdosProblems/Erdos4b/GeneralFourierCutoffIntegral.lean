/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierProductLimit

/-!
# Removing the Euler cutoff under an integrable Fourier weight

The bound is uniform over every finite prime set and every Fourier point.
Dominated convergence is applied to the directed filter of finite prime
sets, using the proved absolute majorant and Euler-product convergence.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

theorem continuous_doubledFourierPrimeFactor {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool) (p : ℕ) :
    Continuous (fun s : (ι ⊕ ι) → Bool → ℂ ↦ doubledFourierPrimeFactor edges companion s p) := by
  unfold doubledFourierPrimeFactor doubledFourierLocalPolynomial selbergPairPolynomial
    primeFourierPower
  split_ifs <;> fun_prop

theorem tendsto_integral_doubledFourierPrimeProducts
    {ι X : Type*} [Fintype ι] [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : X → (ι ⊕ ι) → Bool → ℂ) (hS : Continuous S)
    (G : X → ℂ) (hG : Integrable G μ) {σ : ℝ} (hσ : 1 < σ)
    (hRe : ∀ x i b, σ - 1 ≤ (S x i b).re) :
    Tendsto (fun Q : Finset Nat.Primes ↦
      ∫ x, (∏ p ∈ Q, doubledFourierPrimeFactor edges companion (S x) p) * G x ∂μ)
      atTop (𝓝 (∫ x,
        (∏' p : Nat.Primes, doubledFourierPrimeFactor edges companion (S x) p) * G x ∂μ)) := by
  classical
  let C := ‖riemannZeta (σ : ℂ)‖ ^ Fintype.card (NonemptyDoubledPrimeChoice ι)
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ C * ‖G x‖)
  · apply Eventually.of_forall
    intro Q
    have hprod : Continuous (fun x ↦ ∏ p ∈ Q, doubledFourierPrimeFactor edges companion (S x) p) :=
      continuous_finsetProd Q fun p hp ↦
        (continuous_doubledFourierPrimeFactor edges companion p).comp hS
    exact hprod.aestronglyMeasurable.mul hG.aestronglyMeasurable
  · apply Eventually.of_forall
    intro Q
    apply ae_of_all
    intro x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_prod_doubledFourierPrimeFactor_le_zeta edges companion (S x) hσ (hRe x) Q)
      (norm_nonneg _)
  · exact hG.norm.const_mul C
  · apply ae_of_all
    intro x
    have hprod : Tendsto (fun Q : Finset Nat.Primes ↦
        ∏ p ∈ Q, doubledFourierPrimeFactor edges companion (S x) p) atTop
        (𝓝 (∏' p : Nat.Primes, doubledFourierPrimeFactor edges companion (S x) p)) :=
      (multipliable_doubledFourierPrimeFactor edges companion (S x) hσ (hRe x)).hasProd
    exact hprod.mul_const (G x)

def doubledFourierTensor {ι : Type*} [Fintype ι]
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) : ℂ := ∏ ib, f ib (ξ ib)

theorem integrable_doubledFourierTensor {ι : Type*} [Fintype ι]
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) : Integrable (doubledFourierTensor f) := by
  exact Integrable.fintype_prod fun ib ↦ (f ib).integrable

def doubledFourierTensorExponents {ι : Type*}
    (L : (ι ⊕ ι) → Bool → ℝ) (ξ : ((ι ⊕ ι) × Bool) → ℝ) : (ι ⊕ ι) → Bool → ℂ :=
  fun i b ↦ fourierLaplaceParameter (ξ (i, b)) / (L i b : ℂ)

theorem continuous_doubledFourierTensorExponents {ι : Type*}
    (L : (ι ⊕ ι) → Bool → ℝ) : Continuous (doubledFourierTensorExponents L) := by
  unfold doubledFourierTensorExponents fourierLaplaceParameter
  fun_prop

theorem doubledFourierTensorExponents_re {ι : Type*}
    (L : (ι ⊕ ι) → Bool → ℝ) (ξ : ((ι ⊕ ι) × Bool) → ℝ) (i : ι ⊕ ι) (b : Bool) :
    (doubledFourierTensorExponents L ξ i b).re = (L i b)⁻¹ := by
  simp [doubledFourierTensorExponents, Complex.div_ofReal_re, fourierLaplaceParameter]

theorem tendsto_integral_doubledFourierTensorProducts
    {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (L : (ι ⊕ ι) → Bool → ℝ) (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    {σ : ℝ} (hσ : 1 < σ) (hL : ∀ i b, σ - 1 ≤ (L i b)⁻¹) :
    Tendsto (fun Q : Finset Nat.Primes ↦ ∫ ξ,
      (∏ p ∈ Q, doubledFourierPrimeFactor edges companion (doubledFourierTensorExponents L ξ) p) *
        doubledFourierTensor f ξ) atTop
      (𝓝 (∫ ξ, (∏' p : Nat.Primes,
        doubledFourierPrimeFactor edges companion (doubledFourierTensorExponents L ξ) p) *
          doubledFourierTensor f ξ)) := by
  apply tendsto_integral_doubledFourierPrimeProducts volume edges companion
    (doubledFourierTensorExponents L) (continuous_doubledFourierTensorExponents L)
    (doubledFourierTensor f) (integrable_doubledFourierTensor f) hσ
  intro ξ i b
  rw [doubledFourierTensorExponents_re]
  exact hL i b

end

end Erdos4b
