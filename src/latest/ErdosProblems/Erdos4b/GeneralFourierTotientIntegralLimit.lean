/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientScaledKernel
import ErdosProblems.Erdos4b.GeneralFourierPerturbation
import ErdosProblems.Erdos4b.GeneralFourierSquareRootCutoff
import ErdosProblems.Erdos4b.GeneralFourierLogEnvelope

/-!
# Normalized totient Fourier integral asymptotics

The original normalized kernel has a uniform absolute-integral bound.
The totient correction is measurable and uniformly tends to one at all
frequencies. Their product therefore has the same limiting integral.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

theorem tendsto_integral_normalizedTotientDoubledFourierKernel
    {α ι : Type*} [Fintype ι] {l : Filter α} [l.IsCountablyGenerated]
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
    Tendsto (fun a ↦ ∫ ξ,
      normalizedTotientDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
        doubledFourierTensor f ξ) l
      (𝓝 (∫ ξ, doubledFourierPairKernel ξ * doubledFourierTensor f ξ)) := by
  let D := Fintype.card (NonemptyDoubledPrimeChoice ι)
  let δ (a : α) := Real.exp (8 * (D : ℝ) / w a) - 1
  have hδ (a : α) : 0 ≤ δ a :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))
  have hδlim := tendsto_totientFourierUniformError_zero D w hw
  have hcut : ∀ᶠ a in l, 0 < w a ∧ 2 * (D : ℝ) ≤ w a := by
    filter_upwards [hw.eventually_gt_atTop 0, hw.eventually_ge_atTop (2 * D)] with a h0 h2
    exact ⟨h0, by exact_mod_cast h2⟩
  have hclose : ∀ᶠ a in l, ∀ ξ,
      ‖doubledFourierTotientCorrection (w a) (edges a) (companion a) (L a) ξ - 1‖ ≤ δ a := by
    filter_upwards [hdata, hcut] with a ha hwa
    exact norm_doubledFourierTotientCorrection_sub_one_le
      (w a) (edges a) (companion a) (L a) ha.scale_pos hwa.1 hwa.2
  obtain ⟨W, hW⟩ := exists_uniform_half_le_norm_tprod_roughDoubledFourierSingularFactor ι
  have hint : ∀ᶠ a in l, Integrable (fun ξ ↦
      normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
        doubledFourierTensor f ξ) := by
    filter_upwards [hdata, hw.eventually_ge_atTop W] with a ha hWa
    exact integrable_normalizedDoubledFourierKernel_mul_tensor
      (w a) (edges a) (companion a) (L a) ha.scale_pos
      (hW (edges a) (companion a) hWa ha.integer_pos ha.edge_card ha.generic) f
  obtain ⟨B, _hB0, hB⟩ := exists_eventually_integral_norm_normalizedDoubledFourierKernel_bound
    M w edges companion L T σ V hdata hw hT hV hσ hsmall hmass hupper A hdecay f
  have hlim := tendsto_integral_normalizedDoubledFourierKernel
    M w edges companion L T σ V hdata hw hT hV hσ hsmall hmass hupper A hdecay f
  have hpert := tendsto_integral_mul_of_uniform_correction volume
    (fun a ξ ↦ normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
      doubledFourierTensor f ξ)
    (fun a ↦ doubledFourierTotientCorrection (w a) (edges a) (companion a) (L a)) δ hint
    (Eventually.of_forall fun a ↦ (stronglyMeasurable_doubledFourierTotientCorrection
      (w a) (edges a) (companion a) (L a)).aestronglyMeasurable)
    (Eventually.of_forall hδ) hclose hB hδlim hlim
  apply hpert.congr'
  filter_upwards [hdata, hcut] with a ha hwa
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  dsimp only
  rw [normalizedTotientDoubledFourierKernel_eq_correction_mul
    (w a) (edges a) (companion a) (L a) ha.scale_pos hwa.2 ξ, mul_assoc]

theorem tendsto_integral_normalizedTotientDoubledFourierKernel_sqrt_cutoff
    {α ι : Type*} [Fintype ι] {l : Filter α} [l.IsCountablyGenerated]
    (M w : α → ℕ) (edges : α → ℕ → Finset (ι × ι)) (companion : α → ℕ → Bool)
    (L : α → (ι ⊕ ι) → ℝ) (σ V : α → ℝ)
    (hdata : ∀ᶠ a in l, DoubledFourierBoxConditions (M a) (w a)
      (edges a) (companion a) (L a) (Real.sqrt (V a)) (σ a))
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop) (hσ : Tendsto σ l (𝓝 0))
    (hsmall : Tendsto (fun a ↦ σ a * (w a + 1)) l (𝓝 0))
    (hmass : Tendsto (fun a ↦ σ a * roughPrimeLogDivisorMass (M a) (w a)) l (𝓝 0))
    (hupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) :
    Tendsto (fun a ↦ ∫ ξ,
      normalizedTotientDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
        doubledFourierTensor f ξ) l
      (𝓝 (∫ ξ, doubledFourierPairKernel ξ * doubledFourierTensor f ξ)) :=
  tendsto_integral_normalizedTotientDoubledFourierKernel
    M w edges companion L (fun a ↦ Real.sqrt (V a)) σ V hdata hw
      (Real.tendsto_sqrt_atTop.comp hV) hV hσ hsmall hmass hupper
      (2 * (Fintype.card (ι ⊕ ι) + Fintype.card (NonemptyDoubledPrimeChoice ι) + 1))
      (tendsto_fourier_polynomial_div_sqrt_pow_zero _ _ V hV) f

theorem tendsto_integral_normalizedTotientDoubledFourierKernel_log_envelope
    {α ι : Type*} [Fintype ι] {l : Filter α} [l.IsCountablyGenerated]
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
    Tendsto (fun a ↦ ∫ ξ,
      normalizedTotientDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
        doubledFourierTensor f ξ) l
      (𝓝 (∫ ξ, doubledFourierPairKernel ξ * doubledFourierTensor f ξ)) := by
  have hσnonneg := hdata.mono fun a ha ↦ ha.exponent_nonneg
  have hM := hdata.mono fun a ha ↦ ha.integer_pos
  exact tendsto_integral_normalizedTotientDoubledFourierKernel_sqrt_cutoff
    M w edges companion L σ V hdata hw hV hσ
    (tendsto_exponent_mul_cutoff_of_log_envelope w σ V hσnonneg hcutoff hσ hlog)
    (tendsto_exponent_mul_roughPrimeLogDivisorMass_of_log_envelope
      M w σ V hV hM hσnonneg hB hsize hσ hlog) hupper f

end

end Erdos4b
