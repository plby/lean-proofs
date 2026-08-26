/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The strong law for the central dyadic interval, with every probabilistic input proved.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CentralExpectationTransfer
import ErdosProblems.Erdos521.WindowAlmostSureConcentration

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem ae_centralCappedCount_div_index_limit :
    ∀ᵐ ε ∂sequenceLaw, Tendsto (fun j : ℕ ↦ (centralCappedCount ε j : ℝ) / j)
      atTop (𝓝 (Real.log 2 / (2 * Real.pi))) := by
  have hc := ae_cappedCentralSum_centered_div_index_tendsto_zero dyadicFineGrid
    (fun j _ ↦ fineGridLength j)
  filter_upwards [hc] with ε hε
  have hcenter : Tendsto (fun j : ℕ ↦ ((centralCappedCount ε j : ℝ) -
      ∫ ζ, (centralCappedCount ζ j : ℝ) ∂sequenceLaw) / j) atTop (𝓝 0) := by
    simpa only [centralCappedCount, cappedCentralNatSum_cast] using hε
  have h := hcenter.add centralCappedCount_mean_div_index_limit
  simp only [zero_add] at h
  convert h using 1
  funext j
  ring

theorem ae_centralRootCount_div_index_limit :
    ∀ᵐ ε ∂sequenceLaw, Tendsto (fun j : ℕ ↦ (centralRootCount ε j : ℝ) / j)
      atTop (𝓝 (Real.log 2 / (2 * Real.pi))) := by
  filter_upwards [ae_centralCappedCount_div_index_limit, ae_eventually_centralRootCount_eq_capped]
    with ε hε heq
  apply hε.congr'
  filter_upwards [heq] with j hj
  rw [hj]

theorem tendsto_div_log_two_pow_of_div_index {f : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun j : ℕ ↦ f j / j) atTop (𝓝 L)) :
    Tendsto (fun j : ℕ ↦ f j / Real.log ((2 ^ j : ℕ) : ℝ)) atTop (𝓝 (L / Real.log 2)) := by
  convert h.div_const (Real.log 2) using 1
  funext j
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, div_div]

theorem ae_centralRootCount_div_log_limit :
    ∀ᵐ ε ∂sequenceLaw, Tendsto (fun j : ℕ ↦ (centralRootCount ε j : ℝ) /
      Real.log ((2 ^ j : ℕ) : ℝ)) atTop (𝓝 (1 / (2 * Real.pi))) := by
  filter_upwards [ae_centralRootCount_div_index_limit] with ε hε
  have h := tendsto_div_log_two_pow_of_div_index hε
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have heq : (Real.log 2 / (2 * Real.pi)) / Real.log 2 = 1 / (2 * Real.pi) := by field_simp
  rwa [heq] at h

end Erdos521
