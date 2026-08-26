/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform moments for intervals whose width is at most their endpoint distance.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LogarithmicMoments
import ErdosProblems.Erdos521.UniformLogarithmicMean
import ErdosProblems.Erdos521.EndpointLimit

namespace Erdos521

open MeasureTheory Filter

theorem logarithmic_interval_from_endpoint {b : ℝ} (hb : b < 1) :
    logGrid (1 / (1 - b)) 2 (Real.log 2) 0 = 2 * b - 1 ∧
      logGrid (1 / (1 - b)) 2 (Real.log 2) 1 = b := by
  have hd : 1 - b ≠ 0 := (sub_pos.mpr hb).ne'
  constructor
  · rw [logGrid_zero]
    field_simp
    ring
  · have h := normalized_logGrid_one (1 / (1 - b)) (Real.log 2)
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
    rw [h]
    field_simp
    ring

theorem eventually_relative_interval_moments (p : ℕ) (hp : 1 ≤ p) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop, ∀ a b : ℝ,
      19 / 20 ≤ b → b ≤ endpointCenter (localMomentBulkConstant p) n →
      b - a ≤ 1 - b →
      (∫ ε, (intervalRootCount ε n a b : ℝ) ^ p ∂sequenceLaw) ≤ B := by
  obtain ⟨B, hB, hmom⟩ := eventually_logarithmic_moments p hp
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨B, hB, ?_⟩
  filter_upwards [hmom, eventually_endpointCenter_bounds (localMomentBulkConstant_pos p)] with n hn hcenter
  intro a b hb hbulk hwidth
  have hb₁ : b < 1 := hbulk.trans_lt hcenter.2
  obtain ⟨hg₀, hg₁⟩ := logarithmic_interval_from_endpoint hb₁
  have h := hn (1 / (1 - b)) 2 (by positivity) (by norm_num)
    (by rw [hg₀]; linarith) (by rw [hg₁]; exact hbulk)
  rw [hg₀, hg₁] at h
  apply le_trans _ h
  apply integral_mono (intervalRootCount_pow_integrable n p a b) (intervalRootCount_pow_integrable n p _ _)
  intro ε
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr
    (intervalRootCount_mono ε n (by linarith : 2 * b - 1 ≤ a) le_rfl)) p

end Erdos521
