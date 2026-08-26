/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientIntegralLimit

/-!
# Uniform absolute-integral bounds for the normalized totient kernel

The all-frequency totient correction multiplies the already bounded
absolute integral of the ordinary kernel. No cancellation is used.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

theorem norm_doubledFourierTotientCorrection_le_exp
    {ι : Type*} [Fintype ι] (w : ℕ) (edges : ℕ → Finset (ι × ι))
    (companion : ℕ → Bool) (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    (hw0 : 0 < w) (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) ≤ w)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
    ‖doubledFourierTotientCorrection w edges companion L ξ‖ ≤
      Real.exp (8 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) / w) := by
  have he := norm_doubledFourierTotientCorrection_sub_one_le w edges companion L hL hw0 hw ξ
  have hn := norm_add_le (doubledFourierTotientCorrection w edges companion L ξ - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith

theorem integrable_and_integral_norm_totientKernel_mul_tensor_le
    {ι : Type*} [Fintype ι] (w : ℕ) (edges : ℕ → Finset (ι × ι))
    (companion : ℕ → Bool) (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    (hw0 : 0 < w) (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) ≤ w)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (hint : Integrable (fun ξ ↦ normalizedDoubledFourierKernel w edges companion L ξ *
      doubledFourierTensor f ξ)) :
    Integrable (fun ξ ↦ normalizedTotientDoubledFourierKernel w edges companion L ξ *
      doubledFourierTensor f ξ) ∧
    (∫ ξ, ‖normalizedTotientDoubledFourierKernel w edges companion L ξ *
      doubledFourierTensor f ξ‖) ≤
      Real.exp (8 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) / w) *
        ∫ ξ, ‖normalizedDoubledFourierKernel w edges companion L ξ * doubledFourierTensor f ξ‖ := by
  let C := Real.exp (8 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) / w)
  have hC := norm_doubledFourierTotientCorrection_le_exp w edges companion L hL hw0 hw
  have hid (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
      normalizedTotientDoubledFourierKernel w edges companion L ξ * doubledFourierTensor f ξ =
      doubledFourierTotientCorrection w edges companion L ξ *
        (normalizedDoubledFourierKernel w edges companion L ξ * doubledFourierTensor f ξ) := by
    rw [normalizedTotientDoubledFourierKernel_eq_correction_mul w edges companion L hL hw ξ,
      mul_assoc]
  have hi := hint.bdd_mul
    (stronglyMeasurable_doubledFourierTotientCorrection w edges companion L).aestronglyMeasurable
    (ae_of_all _ hC)
  have htot : Integrable (fun ξ ↦ normalizedTotientDoubledFourierKernel w edges companion L ξ *
      doubledFourierTensor f ξ) := hi.congr (ae_of_all _ fun ξ ↦ (hid ξ).symm)
  refine ⟨htot, ?_⟩
  calc
    _ ≤ ∫ ξ, C * ‖normalizedDoubledFourierKernel w edges companion L ξ *
        doubledFourierTensor f ξ‖ := by
      apply integral_mono htot.norm (hint.norm.const_mul C)
      intro ξ
      dsimp only
      rw [hid ξ, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem exists_eventually_integral_norm_normalizedTotientDoubledFourierKernel_bound
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
      Integrable (fun ξ ↦ normalizedTotientDoubledFourierKernel
        (w a) (edges a) (companion a) (L a) ξ * doubledFourierTensor f ξ) ∧
      (∫ ξ, ‖normalizedTotientDoubledFourierKernel
        (w a) (edges a) (companion a) (L a) ξ * doubledFourierTensor f ξ‖) ≤ B := by
  let D := Fintype.card (NonemptyDoubledPrimeChoice ι)
  obtain ⟨B, hB0, hB⟩ := exists_eventually_integral_norm_normalizedDoubledFourierKernel_bound
    M w edges companion L T σ V hdata hw hT hV hσ hsmall hmass hupper A hdecay f
  obtain ⟨W, hW⟩ := exists_uniform_half_le_norm_tprod_roughDoubledFourierSingularFactor ι
  have hlim := tendsto_totientFourierUniformError_zero D w hw
  refine ⟨2 * B, by positivity, ?_⟩
  filter_upwards [hdata, hB, hw.eventually_ge_atTop W, hw.eventually_ge_atTop 1,
    hw.eventually_ge_atTop (2 * D),
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with a ha hBa hWa hwa0 hwa hca
  have hint := integrable_normalizedDoubledFourierKernel_mul_tensor
    (w a) (edges a) (companion a) (L a) ha.scale_pos
    (hW (edges a) (companion a) hWa ha.integer_pos ha.edge_card ha.generic) f
  have ht := integrable_and_integral_norm_totientKernel_mul_tensor_le
    (w a) (edges a) (companion a) (L a) ha.scale_pos hwa0 (by exact_mod_cast hwa) f hint
  refine ⟨ht.1, ht.2.trans ?_⟩
  apply (mul_le_mul_of_nonneg_left hBa (Real.exp_pos _).le).trans
  apply mul_le_mul_of_nonneg_right _ hB0
  change Real.exp (8 * (D : ℝ) / w a) - 1 < 1 at hca
  linarith

theorem exists_eventually_integral_norm_totientKernel_log_envelope_bound
    {α ι : Type*} [Fintype ι] {l : Filter α}
    (M w : α → ℕ) (edges : α → ℕ → Finset (ι × ι)) (companion : α → ℕ → Bool)
    (L : α → (ι ⊕ ι) → ℝ) (σ V : α → ℝ)
    (hdata : ∀ᶠ a in l, DoubledFourierBoxConditions (M a) (w a)
      (edges a) (companion a) (L a) (Real.sqrt (V a)) (σ a))
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop) (hσ : Tendsto σ l (𝓝 0))
    (hlog : Tendsto (fun a ↦ σ a * Real.log (V a + 1)) l (𝓝 0))
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1))
    {B : ℝ} (hB : 0 ≤ B) (hsize : ∀ᶠ a in l, Real.log (M a) ≤ B * V a)
    (hupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a in l,
      Integrable (fun ξ ↦ normalizedTotientDoubledFourierKernel
        (w a) (edges a) (companion a) (L a) ξ * doubledFourierTensor f ξ) ∧
      (∫ ξ, ‖normalizedTotientDoubledFourierKernel
        (w a) (edges a) (companion a) (L a) ξ * doubledFourierTensor f ξ‖) ≤ C := by
  have hσnonneg := hdata.mono fun a ha ↦ ha.exponent_nonneg
  have hM := hdata.mono fun a ha ↦ ha.integer_pos
  exact exists_eventually_integral_norm_normalizedTotientDoubledFourierKernel_bound
    M w edges companion L (fun a ↦ Real.sqrt (V a)) σ V hdata hw
    (Real.tendsto_sqrt_atTop.comp hV) hV hσ
    (tendsto_exponent_mul_cutoff_of_log_envelope w σ V hσnonneg hcutoff hσ hlog)
    (tendsto_exponent_mul_roughPrimeLogDivisorMass_of_log_envelope
      M w σ V hV hM hσnonneg hB hsize hσ hlog) hupper
    (2 * (Fintype.card (ι ⊕ ι) + Fintype.card (NonemptyDoubledPrimeChoice ι) + 1))
    (tendsto_fourier_polynomial_div_sqrt_pow_zero _ _ V hV) f

end

end Erdos4b
