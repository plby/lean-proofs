/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Expectation error for bounded integer statistics which agree off a rare event.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.RareEventMoments

namespace Erdos521

open MeasureTheory

theorem nat_statistics_disagreement_nullMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X Y : Ω → ℕ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    NullMeasurableSet {ω | X ω ≠ Y ω} μ :=
  (hX.prodMk hY).nullMeasurableSet_preimage (measurableSet_diagonal.compl)

theorem integral_nat_comparison_error {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {X Y : Ω → ℕ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (n m : ℕ) (hboundX : ∀ ω, X ω ≤ n) (hboundY : ∀ ω, Y ω ≤ m)
    (hYX : ∀ᵐ ω ∂μ, Y ω ≤ X ω) {R : ℝ} (hR : 0 < R) :
    0 ≤ (∫ ω, (X ω : ℝ) ∂μ) - (∫ ω, (Y ω : ℝ) ∂μ) ∧
      (∫ ω, (X ω : ℝ) ∂μ) - (∫ ω, (Y ω : ℝ) ∂μ) ≤
        R * μ.real {ω | X ω ≠ Y ω} + (∫ ω, (X ω : ℝ) ^ 8 ∂μ) / R ^ 7 := by
  have hiX : Integrable (fun ω ↦ (X ω : ℝ)) μ := by
    simpa only [pow_one] using bounded_nat_pow_integrable μ hX n 1 hboundX
  have hiY : Integrable (fun ω ↦ (Y ω : ℝ)) μ := by
    simpa only [pow_one] using bounded_nat_pow_integrable μ hY m 1 hboundY
  have hS := nat_statistics_disagreement_nullMeasurable μ hX hY
  constructor
  · apply sub_nonneg.mpr
    exact integral_mono_ae hiY hiX (hYX.mono (fun _ h ↦ Nat.cast_le.mpr h))
  · have hpoint : ∀ ω, (X ω : ℝ) - Y ω ≤ {ω | X ω ≠ Y ω}.indicator (fun ω ↦ (X ω : ℝ)) ω := by
      intro ω
      by_cases hω : X ω ≠ Y ω
      · rw [Set.indicator_of_mem (show ω ∈ {ω | X ω ≠ Y ω} from hω)]
        exact sub_le_self _ (Nat.cast_nonneg _)
      · have heq : X ω = Y ω := not_ne_iff.mp hω
        simp [heq]
    have h := integral_mono (hiX.sub hiY) (hiX.indicator₀ hS) hpoint
    dsimp only [Pi.sub_apply] at h
    rw [integral_sub hiX hiY, integral_indicator₀ hS] at h
    exact h.trans (setIntegral_nat_le_eighth_moment μ hS hX n hboundX hR)

end Erdos521
