/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Counts with fourth moment of order j squared are negligible compared with j almost surely.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SummableDeviations
import ErdosProblems.Erdos521.LocalRootBounds

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem fourth_moment_normalized_deviation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℕ)
    (hX : Integrable (fun ω ↦ (X ω : ℝ) ^ 4) μ) {j : ℕ} (hj : 1 ≤ j)
    {C η : ℝ} (hη : 0 < η) (hmom : (∫ ω, (X ω : ℝ) ^ 4 ∂μ) ≤ C * (j : ℝ) ^ 2) :
    μ.real {ω | η ≤ |(X ω : ℝ) / j|} ≤ (C / η ^ 4) * (j : ℝ) ^ (-2 : ℝ) := by
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hthreshold : 0 < (η * (j : ℝ)) ^ 4 := pow_pos (mul_pos hη hj₀) 4
  have h := measureReal_le_integral_div_of_ae μ hX
    (Eventually.of_forall (fun ω ↦ pow_nonneg (Nat.cast_nonneg (X ω)) 4)) hthreshold
    (Eventually.of_forall (fun ω hω ↦ by
      change η ≤ |(X ω : ℝ) / j| at hω
      rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hj₀.le)] at hω
      exact pow_le_pow_left₀ (mul_nonneg hη.le hj₀.le) ((le_div_iff₀ hj₀).mp hω) 4))
  apply h.trans
  calc
    _ ≤ (C * (j : ℝ) ^ 2) / (η * j) ^ 4 := div_le_div_of_nonneg_right hmom hthreshold.le
    _ = _ := by
      rw [Real.rpow_neg hj₀.le, Real.rpow_two]
      field_simp

theorem ae_nat_div_tendsto_zero_of_fourth_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℕ)
    (hX : ∀ j, Integrable (fun ω ↦ (X j ω : ℝ) ^ 4) μ)
    (hmom : ∃ C : ℝ, ∀ᶠ j : ℕ in atTop, (∫ ω, (X j ω : ℝ) ^ 4 ∂μ) ≤ C * (j : ℝ) ^ 2) :
    ∀ᵐ ω ∂μ, Tendsto (fun j ↦ (X j ω : ℝ) / j) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hmom
  apply ae_tendsto_zero_of_deviation_power_bound μ (fun j ω ↦ (X j ω : ℝ) / j) (p := 2) (by norm_num)
  intro η hη
  refine ⟨C / η ^ 4, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with j hj hj₁
  exact fourth_moment_normalized_deviation μ (X j) (hX j) hj₁ hη hj

end Erdos521
