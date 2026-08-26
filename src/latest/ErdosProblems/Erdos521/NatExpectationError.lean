/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Unordered expectation comparison for bounded natural-valued statistics.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.NatComparisonError

namespace Erdos521

open MeasureTheory

theorem integral_nat_sub_le_error {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {X Y : Ω → ℕ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (n m : ℕ) (hboundX : ∀ ω, X ω ≤ n) (hboundY : ∀ ω, Y ω ≤ m)
    {R : ℝ} (hR : 0 < R) :
    (∫ ω, (X ω : ℝ) ∂μ) - (∫ ω, (Y ω : ℝ) ∂μ) ≤
      R * μ.real {ω | X ω ≠ Y ω} + (∫ ω, (X ω : ℝ) ^ 8 ∂μ) / R ^ 7 := by
  have hiX : Integrable (fun ω ↦ (X ω : ℝ)) μ := by
    simpa only [pow_one] using bounded_nat_pow_integrable μ hX n 1 hboundX
  have hiY : Integrable (fun ω ↦ (Y ω : ℝ)) μ := by
    simpa only [pow_one] using bounded_nat_pow_integrable μ hY m 1 hboundY
  have hS := nat_statistics_disagreement_nullMeasurable μ hX hY
  have hpoint : ∀ ω, (X ω : ℝ) - Y ω ≤ {ω | X ω ≠ Y ω}.indicator (fun ω ↦ (X ω : ℝ)) ω := by
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

theorem abs_integral_nat_sub_le_error {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {X Y : Ω → ℕ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (n m : ℕ) (hboundX : ∀ ω, X ω ≤ n) (hboundY : ∀ ω, Y ω ≤ m)
    {R : ℝ} (hR : 0 < R) :
    |(∫ ω, (X ω : ℝ) ∂μ) - (∫ ω, (Y ω : ℝ) ∂μ)| ≤
      R * μ.real {ω | X ω ≠ Y ω} +
        ((∫ ω, (X ω : ℝ) ^ 8 ∂μ) + (∫ ω, (Y ω : ℝ) ^ 8 ∂μ)) / R ^ 7 := by
  have h₁ := integral_nat_sub_le_error μ hX hY n m hboundX hboundY hR
  have h₂ := integral_nat_sub_le_error μ hY hX m n hboundY hboundX hR
  have heq : {ω | Y ω ≠ X ω} = {ω | X ω ≠ Y ω} := by ext ω; exact ne_comm
  rw [heq] at h₂
  have hX₈ : 0 ≤ (∫ ω, (X ω : ℝ) ^ 8 ∂μ) / R ^ 7 :=
    div_nonneg (integral_nonneg (fun _ ↦ by positivity)) (by positivity)
  have hY₈ : 0 ≤ (∫ ω, (Y ω : ℝ) ^ 8 ∂μ) / R ^ 7 :=
    div_nonneg (integral_nonneg (fun _ ↦ by positivity)) (by positivity)
  rw [add_div]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos521
