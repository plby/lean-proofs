/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierIntegralLimit

/-!
# Absolute-integral bounds for the normalized Fourier kernel

These estimates control the integral of the norm. They can therefore
justify uniform multiplicative perturbations of the kernel without
assuming that cancellation also bounds its absolute integral.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

theorem integral_norm_mul_schwartzTensor_box_compl_le
    {ι : Type*} [Fintype ι] (f : ι → SchwartzMap ℝ ℂ)
    (K : (ι → ℝ) → ℂ) (A : ℕ) {T D : ℝ}
    (hT : 0 < T) (hD : 0 ≤ D) (hbound : ∀ ξ, ‖K ξ‖ ≤ D) :
    (∫ ξ in (fourierCoordinateBox T)ᶜ, ‖K ξ * ∏ i, f i (ξ i)‖) ≤
      D * schwartzTensorMoment f A / T ^ A := by
  calc
    _ = ‖∫ ξ in (fourierCoordinateBox T)ᶜ, ‖K ξ * ∏ i, f i (ξ i)‖‖ := by
      rw [Real.norm_of_nonneg (integral_nonneg fun ξ ↦ norm_nonneg _)]
    _ ≤ ∫ ξ in (fourierCoordinateBox T)ᶜ, D * schwartzTensorNorm f ξ := by
      apply norm_integral_le_of_norm_le
        ((integrable_schwartzTensorNorm f).const_mul D).integrableOn
      apply ae_of_all
      intro ξ
      rw [norm_norm, norm_mul, norm_prod]
      exact mul_le_mul_of_nonneg_right (hbound ξ) (schwartzTensorNorm_nonneg f ξ)
    _ = D * ∫ ξ in (fourierCoordinateBox T)ᶜ, schwartzTensorNorm f ξ := integral_const_mul _ _
    _ ≤ D * (schwartzTensorMoment f A / T ^ A) :=
      mul_le_mul_of_nonneg_left (integral_schwartzTensorNorm_box_compl_le f A hT) hD
    _ = _ := by ring

theorem integral_norm_normalizedDoubledFourierKernel_le
    {ι : Type*} [Fintype ι] (w : ℕ) (edges : ℕ → Finset (ι × ι))
    (companion : ℕ → Bool) (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    (hS : (1 : ℝ) / 2 ≤
      ‖∏' p : Nat.Primes, roughDoubledFourierSingularFactor w edges companion p‖)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) (A : ℕ) {T C D : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbox : ∀ ξ ∈ fourierCoordinateBox T,
      ‖normalizedDoubledFourierKernel w edges companion L ξ‖ ≤ C * ‖doubledFourierPairKernel ξ‖)
    (hglobal : ∀ ξ, ‖normalizedDoubledFourierKernel w edges companion L ξ‖ ≤ D) :
    (∫ ξ, ‖normalizedDoubledFourierKernel w edges companion L ξ * doubledFourierTensor f ξ‖) ≤
      C * (∫ ξ, mainFourierTensorMajorant f ξ) + D * schwartzTensorMoment f A / T ^ A := by
  have hint := (integrable_normalizedDoubledFourierKernel_mul_tensor
    w edges companion L hL hS f).norm
  have hb : (∫ ξ in fourierCoordinateBox T,
      ‖normalizedDoubledFourierKernel w edges companion L ξ * doubledFourierTensor f ξ‖) ≤
      C * (∫ ξ, mainFourierTensorMajorant f ξ) := by
    calc
      _ ≤ ∫ ξ in fourierCoordinateBox T, C * mainFourierTensorMajorant f ξ := by
        apply setIntegral_mono_on hint.integrableOn
          ((integrable_mainFourierTensorMajorant f).const_mul C).integrableOn
          (measurableSet_fourierCoordinateBox T)
        intro ξ hξ
        rw [norm_mul]
        calc
          _ ≤ (C * ‖doubledFourierPairKernel ξ‖) * ‖doubledFourierTensor f ξ‖ :=
            mul_le_mul_of_nonneg_right (hbox ξ hξ) (norm_nonneg _)
          _ = C * ‖doubledFourierPairKernel ξ * doubledFourierTensor f ξ‖ := by
            rw [norm_mul, mul_assoc]
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (norm_doubledFourierPairKernel_mul_tensor_le f ξ) hC
      _ ≤ ∫ ξ, C * mainFourierTensorMajorant f ξ :=
        setIntegral_le_integral ((integrable_mainFourierTensorMajorant f).const_mul C)
          (ae_of_all _ fun ξ ↦ mul_nonneg hC (mainFourierTensorMajorant_nonneg f ξ))
      _ = _ := integral_const_mul _ _
  calc
    _ = (∫ ξ in fourierCoordinateBox T,
        ‖normalizedDoubledFourierKernel w edges companion L ξ * doubledFourierTensor f ξ‖) +
        ∫ ξ in (fourierCoordinateBox T)ᶜ,
          ‖normalizedDoubledFourierKernel w edges companion L ξ * doubledFourierTensor f ξ‖ :=
      (integral_add_compl (measurableSet_fourierCoordinateBox T) hint).symm
    _ ≤ _ := add_le_add hb (integral_norm_mul_schwartzTensor_box_compl_le
      f (normalizedDoubledFourierKernel w edges companion L) A hT hD hglobal)

theorem exists_eventually_integral_norm_normalizedDoubledFourierKernel_bound
    {α ι : Type*} [Fintype ι] {l : Filter α}
    (M w : α → ℕ) (edges : α → ℕ → Finset (ι × ι)) (companion : α → ℕ → Bool)
    (L : α → (ι ⊕ ι) → ℝ) (T σ V : α → ℝ)
    (hdata : ∀ᶠ a in l, DoubledFourierBoxConditions (M a) (w a)
      (edges a) (companion a) (L a) (T a) (σ a))
    (hw : Tendsto w l atTop) (hT : Tendsto T l atTop) (hV : Tendsto V l atTop)
    (hσ : Tendsto σ l (𝓝 0))
    (hsmall : Tendsto (fun a ↦ σ a * (w a + 1)) l (𝓝 0))
    (hmass : Tendsto (fun a ↦ σ a * roughPrimeLogDivisorMass (M a) (w a)) l (𝓝 0))
    (hupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a) (A : ℕ)
    (hdecay : Tendsto (fun a ↦
      (2 * V a ^ Fintype.card (ι ⊕ ι) *
        (2 * V a) ^ Fintype.card (NonemptyDoubledPrimeChoice ι)) / T a ^ A) l (𝓝 0))
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ a in l,
      (∫ ξ, ‖normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
        doubledFourierTensor f ξ‖) ≤ B := by
  let C : ℝ := Real.exp (1 + (Fintype.card (ι ⊕ ι) : ℝ))
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hI : 0 ≤ ∫ ξ, mainFourierTensorMajorant f ξ :=
    integral_nonneg (mainFourierTensorMajorant_nonneg f)
  refine ⟨C * (∫ ξ, mainFourierTensorMajorant f ξ) + 1,
    add_nonneg (mul_nonneg hC hI) zero_le_one, ?_⟩
  have hrelative := tendsto_doubledFourierRelativeErrorBound_zero ι M w σ hw hmass
  have hbox := eventually_norm_normalizedDoubledFourierKernel_le_on_box
    M w edges companion L T σ hdata hσ hsmall hrelative
  obtain ⟨W, hW⟩ := exists_uniform_half_le_norm_tprod_roughDoubledFourierSingularFactor ι
  have hS : ∀ᶠ a in l, (1 : ℝ) / 2 ≤
      ‖∏' p : Nat.Primes, roughDoubledFourierSingularFactor (w a) (edges a) (companion a) p‖ := by
    filter_upwards [hdata, hw.eventually_ge_atTop W] with a ha hWa
    exact hW (edges a) (companion a) hWa ha.integer_pos ha.edge_card ha.generic
  obtain ⟨V₀, hV₀, hzeta⟩ := exists_zetaRealNearOne_norm_bound
  have htail : Tendsto (fun a ↦
      (2 * V a ^ Fintype.card (ι ⊕ ι) *
        (2 * V a) ^ Fintype.card (NonemptyDoubledPrimeChoice ι)) *
          schwartzTensorMoment f A / T a ^ A) l (𝓝 0) := by
    simpa only [zero_mul, div_mul_eq_mul_div] using hdecay.mul_const (schwartzTensorMoment f A)
  filter_upwards [hdata, hS, hupper, hbox, hV.eventually_ge_atTop V₀,
    hT.eventually_gt_atTop 0, htail.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with a ha hSa hUa hBa hVa hTa hEa
  have hVpos := hV₀.trans_le hVa
  have hbound := integral_norm_normalizedDoubledFourierKernel_le
    (w a) (edges a) (companion a) (L a) ha.scale_pos hSa f A hTa hC
    (show 0 ≤ 2 * V a ^ Fintype.card (ι ⊕ ι) *
      (2 * V a) ^ Fintype.card (NonemptyDoubledPrimeChoice ι) by positivity) hBa
    (fun ξ ↦ norm_normalizedDoubledFourierKernel_le_polynomial
      (w a) (edges a) (companion a) (L a) ha.scale_pos hSa hVpos hUa (hzeta (V a) hVa) ξ)
  exact hbound.trans (add_le_add le_rfl hEa.le)

end

end Erdos4b
