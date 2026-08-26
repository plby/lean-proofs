/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Almost-sure limits from summable deviation probabilities.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.EndpointAlmostSure

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem ae_tendsto_zero_of_summable_deviations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (h : ∀ η : ℝ, 0 < η → Summable (fun j ↦ μ.real {ω | η ≤ |X j ω|})) :
    ∀ᵐ ω ∂μ, Tendsto (fun j ↦ X j ω) atTop (𝓝 0) := by
  have hcountable : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ᶠ j : ℕ in atTop, |X j ω| < 1 / (k + 1 : ℝ) := by
    apply ae_all_iff.mpr
    intro k
    have hbc := ae_eventually_notMem_of_summable_real μ
      (fun j ↦ {ω | 1 / (k + 1 : ℝ) ≤ |X j ω|}) (h _ (by positivity))
    simpa only [Set.mem_ofPred_eq, not_le] using hbc
  filter_upwards [hcountable] with ω hω
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
  filter_upwards [hω k] with j hj
  simpa only [Real.dist_eq, sub_zero] using hj.trans hk

theorem ae_tendsto_zero_of_deviation_power_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) {p : ℝ} (hp : 1 < p)
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ᶠ j : ℕ in atTop,
      μ.real {ω | η ≤ |X j ω|} ≤ C * (j : ℝ) ^ (-p)) :
    ∀ᵐ ω ∂μ, Tendsto (fun j ↦ X j ω) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_summable_deviations μ X
  intro η hη
  obtain ⟨C, hC⟩ := h η hη
  have hs : Summable (fun j : ℕ ↦ (j : ℝ) ^ (-p)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply (hs.mul_left C).of_norm_bounded_eventually_nat
  filter_upwards [hC] with j hj
  simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using hj

end Erdos521
