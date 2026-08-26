/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSquareRootCutoff

/-!
# Logarithmic envelopes for the uniform Fourier normalization

The exceptional integer may vary arbitrarily subject to a fixed
logarithmic size bound. Its actual prime-divisor mass is eliminated
from the analytic limit hypotheses using the proved uniform estimate.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

theorem roughPrimeLogDivisorMass_nonneg (M w : ℕ) : 0 ≤ roughPrimeLogDivisorMass M w := by
  unfold roughPrimeLogDivisorMass
  apply Finset.sum_nonneg
  intro p hp
  positivity

theorem tendsto_exponent_mul_cutoff_of_log_envelope
    {α : Type*} {l : Filter α} (w : α → ℕ) (σ V : α → ℝ)
    (hσnonneg : ∀ᶠ a in l, 0 ≤ σ a)
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1))
    (hσ : Tendsto σ l (𝓝 0))
    (hlog : Tendsto (fun a ↦ σ a * Real.log (V a + 1)) l (𝓝 0)) :
    Tendsto (fun a ↦ σ a * (w a + 1)) l (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [hσnonneg] with a ha
    exact mul_nonneg ha (by positivity)
  · filter_upwards [hσnonneg, hcutoff] with a ha hw
    calc
      _ ≤ σ a * (Real.log (V a + 1) + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add hw le_rfl) ha
      _ = σ a * Real.log (V a + 1) + σ a := by ring
  · simpa only [add_zero] using hlog.add hσ

theorem tendsto_exponent_mul_roughPrimeLogDivisorMass_of_log_envelope
    {α : Type*} {l : Filter α} (M w : α → ℕ) (σ V : α → ℝ)
    (hV : Tendsto V l atTop) (hM : ∀ᶠ a in l, 0 < M a)
    (hσnonneg : ∀ᶠ a in l, 0 ≤ σ a) {B : ℝ} (hB : 0 ≤ B)
    (hsize : ∀ᶠ a in l, Real.log (M a) ≤ B * V a)
    (hσ : Tendsto σ l (𝓝 0))
    (hlog : Tendsto (fun a ↦ σ a * Real.log (V a + 1)) l (𝓝 0)) :
    Tendsto (fun a ↦ σ a * roughPrimeLogDivisorMass (M a) (w a)) l (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_roughPrimeLogDivisorMass_log_bound
  apply squeeze_zero'
  · filter_upwards [hσnonneg] with a ha
    exact mul_nonneg ha (roughPrimeLogDivisorMass_nonneg _ _)
  · filter_upwards [hM, hσnonneg, hsize, hV.eventually_ge_atTop 1] with a hMa hσa hBa hVa
    calc
      _ ≤ σ a * (Real.log (V a + 1) + C + B) :=
        mul_le_mul_of_nonneg_left (hbound hMa hB hVa hBa (w a)) hσa
      _ = σ a * Real.log (V a + 1) + σ a * (C + B) := by ring
  · simpa only [mul_zero, zero_mul, add_zero] using hlog.add (hσ.mul_const (C + B))

theorem tendsto_integral_normalizedDoubledFourierKernel_log_envelope
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
      normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
        doubledFourierTensor f ξ) l
      (𝓝 (∫ ξ, doubledFourierPairKernel ξ * doubledFourierTensor f ξ)) := by
  have hσnonneg := hdata.mono fun a ha ↦ ha.exponent_nonneg
  have hM := hdata.mono fun a ha ↦ ha.integer_pos
  exact tendsto_integral_normalizedDoubledFourierKernel_sqrt_cutoff
    M w edges companion L σ V hdata hw hV hσ
    (tendsto_exponent_mul_cutoff_of_log_envelope w σ V hσnonneg hcutoff hσ hlog)
    (tendsto_exponent_mul_roughPrimeLogDivisorMass_of_log_envelope
      M w σ V hV hM hσnonneg hB hsize hσ hlog) hupper f

end

end Erdos4b
