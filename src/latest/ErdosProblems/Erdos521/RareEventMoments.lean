/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Elementary truncation bounds expectations on rare events using higher moments.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.NatTailMoments

namespace Erdos521

open MeasureTheory

theorem indicator_le_cutoff_moment {Ω : Type*} (S : Set Ω) (X : Ω → ℝ) (p : ℕ)
    {R : ℝ} (hR : 0 < R) (hX : ∀ ω, 0 ≤ X ω) (ω : Ω) :
    S.indicator X ω ≤ S.indicator (fun _ ↦ R) ω + X ω ^ (p + 1) / R ^ p := by
  classical
  have hXω := hX ω
  by_cases hω : ω ∈ S
  · simp only [Set.indicator_of_mem hω]
    by_cases hxR : X ω ≤ R
    · have hpos : 0 ≤ X ω ^ (p + 1) / R ^ p := by positivity
      linarith
    · have hpow := pow_le_pow_left₀ hR.le (le_of_not_ge hxR) p
      have hmul := mul_le_mul_of_nonneg_left hpow (hX ω)
      have hbound : X ω ≤ X ω ^ (p + 1) / R ^ p := by
        apply (le_div_iff₀ (pow_pos hR _)).mpr
        simpa only [pow_succ, mul_comm] using hmul
      linarith
  · simp only [Set.indicator_of_notMem hω, zero_add]
    exact div_nonneg (pow_nonneg (hX ω) _) (pow_nonneg hR.le _)

theorem setIntegral_le_cutoff_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {S : Set Ω} (hS : NullMeasurableSet S μ) {X : Ω → ℝ}
    (hX : Integrable X μ) (p : ℕ) (hXp : Integrable (fun ω ↦ X ω ^ (p + 1)) μ)
    {R : ℝ} (hR : 0 < R) (hnonneg : ∀ ω, 0 ≤ X ω) :
    (∫ ω in S, X ω ∂μ) ≤ R * μ.real S + (∫ ω, X ω ^ (p + 1) ∂μ) / R ^ p := by
  have hi := (integrable_const R).indicator₀ hS
  have hp : Integrable (fun ω ↦ X ω ^ (p + 1) / R ^ p) μ := hXp.div_const _
  have h := integral_mono (hX.indicator₀ hS) (hi.add hp)
    (indicator_le_cutoff_moment S X p hR hnonneg)
  dsimp only [Pi.add_apply] at h
  rw [integral_indicator₀ hS, integral_add hi hp, integral_indicator₀ hS,
    setIntegral_const, smul_eq_mul, integral_div] at h
  simpa only [mul_comm (μ.real S) R] using h

theorem setIntegral_nat_le_eighth_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {S : Set Ω} (hS : NullMeasurableSet S μ) {X : Ω → ℕ}
    (hX : AEMeasurable X μ) (n : ℕ) (hbound : ∀ ω, X ω ≤ n) {R : ℝ} (hR : 0 < R) :
    (∫ ω in S, (X ω : ℝ) ∂μ) ≤ R * μ.real S +
      (∫ ω, (X ω : ℝ) ^ 8 ∂μ) / R ^ 7 := by
  have hX₁ : Integrable (fun ω ↦ (X ω : ℝ)) μ := by
    simpa only [pow_one] using bounded_nat_pow_integrable μ hX n 1 hbound
  exact setIntegral_le_cutoff_moment μ hS hX₁ 7 (bounded_nat_pow_integrable μ hX n 8 hbound)
    hR (fun ω ↦ Nat.cast_nonneg (X ω))

end Erdos521
