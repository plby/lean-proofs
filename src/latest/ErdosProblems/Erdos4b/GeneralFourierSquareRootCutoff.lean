/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierIntegralLimit

/-!
# The square-root Fourier cutoff absorbs every fixed polynomial

The explicit moment order removes the polynomial tail-decay hypothesis
from the normalized integral limit. This is the cutoff used with the
large-prime-gap logarithmic scales.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

theorem fourier_polynomial_div_sqrt_pow (n d : ℕ) {V : ℝ} (hV : 0 < V) :
    (2 * V ^ n * (2 * V) ^ d) / (Real.sqrt V) ^ (2 * (n + d + 1)) =
      (2 : ℝ) ^ (d + 1) / V := by
  have hpow : (Real.sqrt V) ^ (2 * (n + d + 1)) = V ^ n * V ^ d * V := by
    rw [pow_mul, Real.sq_sqrt hV.le, pow_succ, pow_add]
  rw [hpow, mul_pow, pow_succ]
  field_simp

theorem tendsto_fourier_polynomial_div_sqrt_pow_zero
    {α : Type*} {l : Filter α} (n d : ℕ) (V : α → ℝ) (hV : Tendsto V l atTop) :
    Tendsto (fun a ↦ (2 * V a ^ n * (2 * V a) ^ d) /
      (Real.sqrt (V a)) ^ (2 * (n + d + 1))) l (𝓝 0) := by
  have h : Tendsto (fun a ↦ (2 : ℝ) ^ (d + 1) / V a) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hV
  apply h.congr'
  filter_upwards [hV.eventually_gt_atTop 0] with a ha
  exact (fourier_polynomial_div_sqrt_pow n d ha).symm

theorem tendsto_integral_normalizedDoubledFourierKernel_sqrt_cutoff
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
      normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
        doubledFourierTensor f ξ) l
      (𝓝 (∫ ξ, doubledFourierPairKernel ξ * doubledFourierTensor f ξ)) := by
  exact tendsto_integral_normalizedDoubledFourierKernel
    M w edges companion L (fun a ↦ Real.sqrt (V a)) σ V hdata hw
      (Real.tendsto_sqrt_atTop.comp hV) hV hσ hsmall hmass hupper
      (2 * (Fintype.card (ι ⊕ ι) + Fintype.card (NonemptyDoubledPrimeChoice ι) + 1))
      (tendsto_fourier_polynomial_div_sqrt_pow_zero _ _ V hV) f

end

end Erdos4b
