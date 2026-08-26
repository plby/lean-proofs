/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Every fixed moment of a local root count is uniformly bounded in the bulk.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LocalMomentBound
import ErdosProblems.Erdos521.MomentCutoff

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

noncomputable def localMomentBulkConstant (p : ℕ) : ℝ := 32 * (localMomentSlope p + 1)

noncomputable def localMomentBoundConstant (p : ℕ) : ℝ :=
  16 ^ p + localMomentSeries p + localTailConstant

theorem localMomentBulkConstant_pos (p : ℕ) : 0 < localMomentBulkConstant p := by
  have := localMomentSlope_pos p
  unfold localMomentBulkConstant
  positivity

theorem localMomentBoundConstant_pos (p : ℕ) : 0 < localMomentBoundConstant p := by
  have := localTailConstant_pos
  have := localMomentSeries_nonneg p
  unfold localMomentBoundConstant
  positivity

theorem eventually_integral_localRootCount_pow_le (p : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, 9 / 10 ≤ x → x < 1 →
      localMomentBulkConstant p * Real.log n ≤ n * (1 - x) →
      (∫ ε, (localRootCount ε n x ((1 - x) / 8) : ℝ) ^ p ∂sequenceLaw) ≤
        localMomentBoundConstant p := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_localMomentCutoff_large p, hlog.eventually_ge_atTop 1,
    eventually_ge_atTop 1] with n hJ hnlog hn
  intro x hx hx₁ hxgap
  have hgap : 32 * (localMomentCutoff p n : ℝ) ≤ n * (1 - x) :=
    (localMomentCutoff_gap p n hnlog).trans hxgap
  have h := integral_localRootCount_pow_le n p (localMomentCutoff p n) hJ hx hx₁ hgap
  have hrem := mul_le_mul_of_nonneg_left (localMomentCutoff_remainder p n hn) localTailConstant_pos.le
  unfold localMomentBoundConstant
  nlinarith

theorem eventually_bulk_local_moments (p : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ Set.Icc (9 / 10 : ℝ) (endpointCenter (localMomentBulkConstant p) n),
      (∫ ε, (localRootCount ε n x ((1 - x) / 8) : ℝ) ^ p ∂sequenceLaw) ≤
        localMomentBoundConstant p := by
  filter_upwards [eventually_integral_localRootCount_pow_le p, eventually_ge_atTop 2] with n hn hn₂
  intro x hx
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn₁ : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog := Real.log_pos hn₁
  have hC := localMomentBulkConstant_pos p
  have hxupper := hx.2
  change x ≤ 1 - localMomentBulkConstant p * Real.log n / n at hxupper
  have hx₁ : x < 1 := by
    have hdiv := div_pos (mul_pos hC hlog) hn₀
    linarith
  apply hn x hx.1 hx₁
  have h := (div_le_iff₀ hn₀).mp (show localMomentBulkConstant p * Real.log n / n ≤ 1 - x by linarith)
  nlinarith

end Erdos521
