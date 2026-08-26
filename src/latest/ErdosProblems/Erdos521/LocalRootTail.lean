/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform local root-count tails from Jensen, smoothing, and lacunary signs.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LocalTailFrequency
import ErdosProblems.Erdos521.LocalSmallVariance

namespace Erdos521

noncomputable def localTailBound (j : ℕ) : ℝ :=
  let c : ℝ := 1 / (4 * Real.pi ^ 2)
  Real.exp (1 / 2) * ((1 / 2 : ℝ) ^ j * Real.sqrt (Real.pi / c) +
    Real.exp (-c * j) + 2 * Real.exp (-(j : ℝ) / 2)) +
      (1 / 4 : ℝ) ^ (j / 12) + 24 * (1 / 4 : ℝ) ^ j

theorem localTailBound_nonneg (j : ℕ) : 0 ≤ localTailBound j := by
  unfold localTailBound
  positivity

theorem localRootCount_tail (n j : ℕ) (hj : 8 ≤ j) {x : ℝ}
    (hx : 9 / 10 ≤ x) (hx₁ : x < 1) (hgap : 32 * (j : ℝ) ≤ n * (1 - x)) :
    sequenceLaw.real {ε | 2 * j ≤ localRootCount ε n x ((1 - x) / 8)} ≤ localTailBound j := by
  have hx₀ : 0 < x := by linarith
  have hj₁ : 1 ≤ j := by omega
  have htail := local_tail_variance_condition n j hj₁ hx₀.le hx₁.le hgap
  by_cases hV : geometricVariance x (n + 1) ≤ j
  · have h := localRootCount_normalized_probability_split n (2 * j) hx₀.le hx₁
      (by positivity : 0 < (1 / 2 : ℝ) ^ j) htail
    rw [dyadic_local_jensen_term] at h
    apply (h.trans (add_le_add (local_small_variance_smallBall n j hj hx hx₁ hgap hV) le_rfl)).trans
    dsimp only [localTailBound]
    have hnonneg : 0 ≤ Real.exp (1 / 2) * ((1 / 2 : ℝ) ^ j *
        Real.sqrt (Real.pi / (1 / (4 * Real.pi ^ 2))) +
        Real.exp (-(1 / (4 * Real.pi ^ 2)) * j) + 2 * Real.exp (-(j : ℝ) / 2)) := by positivity
    linarith
  · have h := localRootCount_normalized_probability n (2 * j) (n / 2) (by omega)
      (by linarith : 1 / 2 ≤ x) hx₁ (by positivity : 0 < (1 / 2 : ℝ) ^ j) htail
    dsimp only at h
    rw [dyadic_local_jensen_term] at h
    have hvar : Real.exp (-(1 / (4 * Real.pi ^ 2)) * geometricVariance x (n + 1)) ≤
        Real.exp (-(1 / (4 * Real.pi ^ 2)) * j) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (le_of_not_ge hV) (neg_nonpos.mpr (by positivity))
    have hfreq := local_tail_frequency_error n j hj₁ hx₀ hx₁.le hgap
    apply h.trans
    dsimp only [localTailBound]
    have hexp : 0 ≤ Real.exp (1 / 2) := (Real.exp_pos _).le
    have hvarmul := mul_le_mul_of_nonneg_left hvar hexp
    have hfreqmul := mul_le_mul_of_nonneg_left hfreq hexp
    have hrest : 0 ≤ (1 / 4 : ℝ) ^ (j / 12) := by positivity
    nlinarith

end Erdos521
