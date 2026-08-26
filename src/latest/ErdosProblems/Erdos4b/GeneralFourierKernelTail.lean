/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierScaledKernel
import ErdosProblems.Erdos4b.GeneralFourierTensorTail

/-!
# Polynomial majorant and tail bound for the normalized Euler kernel

The uniform lower bound for the singular product and the absolute zeta
majorant give a bound at all frequencies. Schwartz moments absorb this
polynomial bound outside a growing coordinate box.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

theorem norm_tprod_selectedDoubledFourierPrimeFactor_le_zeta
    {ι : Type*} [Fintype ι] (select : ℕ → Bool)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {σ : ℝ} (hσ : 1 < σ)
    (hs : ∀ i b, σ - 1 ≤ (s i b).re) :
    ‖∏' p : Nat.Primes, selectedDoubledFourierPrimeFactor select edges companion s p‖ ≤
      ‖riemannZeta (σ : ℂ)‖ ^ Fintype.card (NonemptyDoubledPrimeChoice ι) := by
  have hprod := (multipliable_selectedDoubledFourierPrimeFactor
    select edges companion s hσ hs).hasProd.norm
  apply le_of_tendsto hprod
  apply Eventually.of_forall
  intro Q
  simpa only [norm_prod] using
    norm_prod_selectedDoubledFourierPrimeFactor_le_zeta select edges companion s hσ hs Q

theorem norm_doubledFourierNormalization_le
    {ι : Type*} [Fintype ι] (w : ℕ) (edges : ℕ → Finset (ι × ι))
    (companion : ℕ → Bool) (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 ≤ L i)
    (hS : (1 : ℝ) / 2 ≤
      ‖∏' p : Nat.Primes, roughDoubledFourierSingularFactor w edges companion p‖) :
    ‖doubledFourierNormalization w edges companion L‖ ≤ 2 * ∏ i, L i := by
  have hprod : ‖∏ i, (L i : ℂ)‖ = ∏ i, L i := by
    rw [norm_prod]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hL i)]
  rw [doubledFourierNormalization, norm_div, norm_mul, hprod]
  calc
    _ ≤ ((∏ i, L i) * 1) / (1 / 2) :=
      div_le_div₀ (mul_nonneg (Finset.prod_nonneg fun i hi ↦ hL i) zero_le_one)
        (mul_le_mul_of_nonneg_left (norm_smallDoubledFourierReferenceProduct_zero_le_one w)
          (Finset.prod_nonneg fun i hi ↦ hL i)) (by norm_num) hS
    _ = _ := by ring

theorem norm_normalizedDoubledFourierKernel_le_zeta
    {ι : Type*} [Fintype ι] (w : ℕ) (edges : ℕ → Finset (ι × ι))
    (companion : ℕ → Bool) (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    (hS : (1 : ℝ) / 2 ≤
      ‖∏' p : Nat.Primes, roughDoubledFourierSingularFactor w edges companion p‖)
    {σ : ℝ} (hσ : 1 < σ) (hscale : ∀ i, σ - 1 ≤ (L i)⁻¹)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
    ‖normalizedDoubledFourierKernel w edges companion L ξ‖ ≤
      (2 * ∏ i, L i) * ‖riemannZeta (σ : ℂ)‖ ^ Fintype.card (NonemptyDoubledPrimeChoice ι) := by
  rw [normalizedDoubledFourierKernel, norm_mul]
  apply mul_le_mul (norm_doubledFourierNormalization_le w edges companion L
    (fun i ↦ (hL i).le) hS) _ (norm_nonneg _)
      (mul_nonneg (by norm_num) (Finset.prod_nonneg fun i hi ↦ (hL i).le))
  apply norm_tprod_selectedDoubledFourierPrimeFactor_le_zeta _ _ _ _ hσ
  intro i b
  rw [doubledFourierTensorExponents_re]
  exact hscale i

theorem norm_normalizedDoubledFourierKernel_le_polynomial
    {ι : Type*} [Fintype ι] (w : ℕ) (edges : ℕ → Finset (ι × ι))
    (companion : ℕ → Bool) (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    (hS : (1 : ℝ) / 2 ≤
      ‖∏' p : Nat.Primes, roughDoubledFourierSingularFactor w edges companion p‖)
    {V : ℝ} (hV : 0 < V) (hscale : ∀ i, L i ≤ V)
    (hzeta : ‖riemannZeta (1 + ((V⁻¹ : ℝ) : ℂ))‖ ≤ 2 * V)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
    ‖normalizedDoubledFourierKernel w edges companion L ξ‖ ≤
      2 * V ^ Fintype.card (ι ⊕ ι) * (2 * V) ^ Fintype.card (NonemptyDoubledPrimeChoice ι) := by
  have hσ : 1 < 1 + V⁻¹ := by linarith [inv_pos.mpr hV]
  have hscale' (i : ι ⊕ ι) : (1 + V⁻¹) - 1 ≤ (L i)⁻¹ := by
    simpa only [add_sub_cancel_left] using
      (inv_le_inv₀ hV (hL i)).mpr (hscale i)
  have h := norm_normalizedDoubledFourierKernel_le_zeta
    w edges companion L hL hS hσ hscale' ξ
  have hprod : (∏ i, L i) ≤ V ^ Fintype.card (ι ⊕ ι) := by
    simpa only [Finset.prod_const, Finset.card_univ] using
      Finset.prod_le_prod (s := Finset.univ) (fun i hi ↦ (hL i).le) (fun i hi ↦ hscale i)
  apply h.trans
  simp only [Complex.ofReal_add, Complex.ofReal_one]
  gcongr

theorem integrable_normalizedDoubledFourierKernel_mul_tensor
    {ι : Type*} [Fintype ι] (w : ℕ) (edges : ℕ → Finset (ι × ι))
    (companion : ℕ → Bool) (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    (hS : (1 : ℝ) / 2 ≤
      ‖∏' p : Nat.Primes, roughDoubledFourierSingularFactor w edges companion p‖)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) :
    Integrable (fun ξ ↦ normalizedDoubledFourierKernel w edges companion L ξ *
      doubledFourierTensor f ξ) := by
  obtain ⟨σ, hσ, hscale⟩ := exists_doubledFourierTensor_halfPlane
    (fun i _ ↦ L i) (fun i _ ↦ hL i)
  exact integrable_mul_schwartzTensor_of_bound f _
    (stronglyMeasurable_normalizedDoubledFourierKernel w edges companion L).aestronglyMeasurable
    (fun ξ ↦ norm_normalizedDoubledFourierKernel_le_zeta
      w edges companion L hL hS hσ (fun i ↦ hscale i false) ξ)

theorem norm_integral_normalizedDoubledFourierKernel_box_compl_le
    {ι : Type*} [Fintype ι] (w : ℕ) (edges : ℕ → Finset (ι × ι))
    (companion : ℕ → Bool) (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    (hS : (1 : ℝ) / 2 ≤
      ‖∏' p : Nat.Primes, roughDoubledFourierSingularFactor w edges companion p‖)
    {V T : ℝ} (hV : 0 < V) (hT : 0 < T) (hscale : ∀ i, L i ≤ V)
    (hzeta : ‖riemannZeta (1 + ((V⁻¹ : ℝ) : ℂ))‖ ≤ 2 * V)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) (A : ℕ) :
    ‖∫ ξ in (fourierCoordinateBox T)ᶜ,
      normalizedDoubledFourierKernel w edges companion L ξ * doubledFourierTensor f ξ‖ ≤
      (2 * V ^ Fintype.card (ι ⊕ ι) * (2 * V) ^ Fintype.card (NonemptyDoubledPrimeChoice ι)) *
        schwartzTensorMoment f A / T ^ A := by
  apply norm_integral_mul_schwartzTensor_box_compl_le f _ A hT (by positivity)
  intro ξ
  exact norm_normalizedDoubledFourierKernel_le_polynomial
    w edges companion L hL hS hV hscale hzeta ξ

end

end Erdos4b
