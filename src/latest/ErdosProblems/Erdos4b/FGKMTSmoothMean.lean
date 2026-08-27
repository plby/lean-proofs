/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTUniformMean
import ErdosProblems.Erdos4b.FGKMTRealAbelMean
import ErdosProblems.Erdos4b.FGKMTSmoothAbel

/-!
# The uniform one-dimensional smooth sieve sum

The absolute constant is chosen before every arithmetic parameter and
test function. The bound retains the cubic modulus loss and a first
derivative bound on the unit interval, exactly as needed for iterating
the smooth coordinate sums.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem exists_roughSieveWeight_real_cumulative_error_logScale :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M : ℕ}, 0 < k → 0 < M →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) → ∀ g : ℕ → ℝ,
      (∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → g p ≤ p - 1) →
      ∀ t : ℝ, 1 ≤ t →
      |BoundedGaps.Maynard.abelCumulative (roughSieveWeight M g) t -
        sieveMainConstant M g * Real.log t| ≤
          C * sieveMainConstant M g * modulusLogScale M ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := exists_roughSieveWeight_cumulative_error_logScale
  refine ⟨C + 1, by linarith, ?_⟩
  intro k M hk hM hsmall g hg hclose hupper t ht
  have hc := sieveMainConstant_pos hk hM hsmall g hg hclose hupper
  have h := abelCumulative_error_of_integer_bounds
    (c := roughSieveWeight M g) (by simp) hc.le
    (fun N hN => hbound hk hM hN hsmall g hg hclose hupper) ht
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hscalePow : 1 ≤ modulusLogScale M ^ 3 := one_le_pow₀ (one_le_modulusLogScale M)
  have hcost : sieveMainConstant M g * Real.log 2 ≤
      sieveMainConstant M g * modulusLogScale M ^ 3 :=
    mul_le_mul_of_nonneg_left (hlog2.trans hscalePow) hc.le
  nlinarith

theorem exists_roughSieveWeight_smooth_error_logScale :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R : ℕ}, 0 < k → 0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) → ∀ g : ℕ → ℝ,
      (∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → g p ≤ p - 1) →
      ∀ {G : ℝ → ℝ}, ContDiff ℝ 1 G → ∀ {V : ℝ},
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv G x| ≤ V) →
      |(∑ n ∈ Finset.Icc 0 R,
          G (Real.log n / Real.log R) * roughSieveWeight M g n) -
        sieveMainConstant M g * Real.log R * (∫ x in (0 : ℝ)..1, G x)| ≤
          C * sieveMainConstant M g * modulusLogScale M ^ 3 * (|G 1| + V) := by
  obtain ⟨C, hC, hbound⟩ := exists_roughSieveWeight_real_cumulative_error_logScale
  refine ⟨C, hC, ?_⟩
  intro k M R hk hM hR hsmall g hg hclose hupper G hG V hV
  have hc := sieveMainConstant_pos hk hM hsmall g hg hclose hupper
  have hscale0 := zero_le_one.trans (one_le_modulusLogScale M)
  apply abs_smoothWeightedSum_sub_logIntegral_le hR (by simp)
    (by positivity) hG _ hV
  intro t ht
  exact hbound hk hM hsmall g hg hclose hupper t ht.1

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_roughSieveWeight_smooth_error_logScale
