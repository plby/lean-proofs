/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientKernel

/-!
# Dominated convergence for the totient Euler integrals

The finite correction product has the same uniform exponential bound
as its infinite product. It multiplies the existing zeta majorant, so
the prime cutoff may tend to infinity under the Fourier integral.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

theorem norm_prod_roughTotientFourierCorrection_le
    (a : ℕ → ℂ) {w : ℕ} {A : ℝ} (hA : 0 ≤ A) (hw0 : 0 < w) (hw : 2 * A ≤ w)
    (ha : ∀ p : Nat.Primes, w < p → ‖a p‖ ≤ A) (Q : Finset Nat.Primes) :
    ‖∏ p ∈ Q, roughTotientFourierCorrection w a p‖ ≤ Real.exp (8 * A / w) := by
  have hs := sum_norm_roughTotientFourierCorrection_sub_one_le a hA hw0 hw ha Q
  have hp := norm_prod_one_add_error_le Q
    (fun p : Nat.Primes ↦ roughTotientFourierCorrection w a p - 1)
  simp only [add_sub_cancel] at hp
  have he := hp.trans (sub_le_sub_right (Real.exp_le_exp.mpr hs) 1)
  have ht := norm_add_le ((∏ p ∈ Q, roughTotientFourierCorrection w a p) - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at ht
  linarith

theorem norm_prod_roughTotientDoubledFourierPrimeFactor_le_zeta
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {w : ℕ} {σ : ℝ} (hw0 : 0 < w)
    (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) ≤ w)
    (hσ : 1 < σ) (hs : ∀ i b, σ - 1 ≤ (s i b).re) (Q : Finset Nat.Primes) :
    ‖∏ p ∈ Q, roughTotientDoubledFourierPrimeFactor w edges companion s p‖ ≤
      Real.exp (8 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) / w) *
        ‖riemannZeta (σ : ℂ)‖ ^ Fintype.card (NonemptyDoubledPrimeChoice ι) := by
  have hs0 : ∀ i b, 0 ≤ (s i b).re := fun i b ↦ (by linarith : 0 ≤ σ - 1).trans (hs i b)
  simp_rw [roughTotientDoubledFourierPrimeFactor_eq_correction_mul edges companion s hw hs0]
  rw [Finset.prod_mul_distrib, norm_mul]
  exact mul_le_mul (norm_prod_roughTotientFourierCorrection_le
    (doubledFourierPrimeNumerator edges companion s) (Nat.cast_nonneg _) hw0 hw
    (fun p _hp ↦ norm_doubledFourierPrimeNumerator_le edges companion s hs0 p) Q)
    (norm_prod_selectedDoubledFourierPrimeFactor_le_zeta
      (fun p ↦ decide (w < p)) edges companion s hσ hs Q) (norm_nonneg _) (Real.exp_pos _).le

theorem continuous_roughTotientDoubledFourierPrimeFactor
    {ι : Type*} [Fintype ι] (w : ℕ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool) (p : ℕ) :
    Continuous (fun s : (ι ⊕ ι) → Bool → ℂ ↦
      roughTotientDoubledFourierPrimeFactor w edges companion s p) := by
  unfold roughTotientDoubledFourierPrimeFactor totientDoubledFourierPrimeFactor
    doubledFourierPrimeNumerator doubledFourierLocalPolynomial
    selbergPairPolynomial primeFourierPower
  split_ifs <;> fun_prop

theorem tendsto_integral_roughTotientDoubledFourierPrimeProducts
    {ι X : Type*} [Fintype ι] [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (w : ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (S : X → (ι ⊕ ι) → Bool → ℂ) (hS : Continuous S)
    (G : X → ℂ) (hG : Integrable G μ) {σ : ℝ} (hσ : 1 < σ)
    (hw0 : 0 < w) (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) ≤ w)
    (hRe : ∀ x i b, σ - 1 ≤ (S x i b).re) :
    Tendsto (fun Q : Finset Nat.Primes ↦
      ∫ x, (∏ p ∈ Q, roughTotientDoubledFourierPrimeFactor w edges companion (S x) p) * G x ∂μ)
      atTop (𝓝 (∫ x,
        (∏' p : Nat.Primes, roughTotientDoubledFourierPrimeFactor w edges companion (S x) p) *
          G x ∂μ)) := by
  classical
  let C := Real.exp (8 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) / w) *
    ‖riemannZeta (σ : ℂ)‖ ^ Fintype.card (NonemptyDoubledPrimeChoice ι)
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ C * ‖G x‖)
  · apply Eventually.of_forall
    intro Q
    have hprod : Continuous (fun x ↦
        ∏ p ∈ Q, roughTotientDoubledFourierPrimeFactor w edges companion (S x) p) :=
      continuous_finsetProd Q fun p hp ↦
        (continuous_roughTotientDoubledFourierPrimeFactor w edges companion p).comp hS
    exact hprod.aestronglyMeasurable.mul hG.aestronglyMeasurable
  · apply Eventually.of_forall
    intro Q
    apply ae_of_all
    intro x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_prod_roughTotientDoubledFourierPrimeFactor_le_zeta
        edges companion (S x) hw0 hw hσ (hRe x) Q) (norm_nonneg _)
  · exact hG.norm.const_mul C
  · apply ae_of_all
    intro x
    have hprod : Tendsto (fun Q : Finset Nat.Primes ↦
        ∏ p ∈ Q, roughTotientDoubledFourierPrimeFactor w edges companion (S x) p) atTop
        (𝓝 (∏' p : Nat.Primes, roughTotientDoubledFourierPrimeFactor w edges companion (S x) p)) :=
      (hasProd_roughTotientDoubledFourierPrimeFactor
        edges companion (S x) hw hσ (hRe x)).multipliable.hasProd
    exact hprod.mul_const (G x)

end

end Erdos4b
