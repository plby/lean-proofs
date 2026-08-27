/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSmoothMean
import ErdosProblems.Erdos4b.FGKMTProfileRescale

/-! # The uniform smooth harmonic sum on the entire doubled interval -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem twice_log_ratio_sq (R n : ℕ) :
    2 * (Real.log n / Real.log (R ^ 2 : ℕ)) = Real.log n / Real.log R := by
  rw [log_nat_sq, div_mul_eq_div_div]
  ring

theorem exists_roughSieveWeight_double_smooth_error_logScale :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R : ℕ}, 0 < k → 0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) → ∀ g : ℕ → ℝ,
      (∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → g p ≤ p - 1) →
      ∀ {G : ℝ → ℝ}, ContDiff ℝ 1 G → ∀ {V : ℝ},
      (∀ x ∈ Set.Icc (0 : ℝ) 2, |deriv G x| ≤ V) →
      |(∑ n ∈ Finset.Icc 0 (R ^ 2),
          G (Real.log n / Real.log R) * roughSieveWeight M g n) -
        sieveMainConstant M g * Real.log R * (∫ x in (0 : ℝ)..2, G x)| ≤
          C * sieveMainConstant M g * modulusLogScale M ^ 3 * (|G 2| + 2 * V) := by
  obtain ⟨C, hC, hmean⟩ := exists_roughSieveWeight_smooth_error_logScale
  refine ⟨C, hC, ?_⟩
  intro k M R hk hM hR hsmall g hg hclose hupper G hG V hV
  let H := fun x : ℝ => G (2 * x)
  have hH : ContDiff ℝ 1 H := hG.comp (contDiff_const.mul contDiff_id)
  have hHD (x : ℝ) : deriv H x = deriv G (2 * x) * 2 := by
    have h := ((hG.differentiable_one (2 * x)).hasDerivAt).comp x
      ((hasDerivAt_id x).const_mul 2)
    simpa only [H, Function.comp_apply, mul_one] using! h.deriv
  have hV' (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : |deriv H x| ≤ 2 * V := by
    rw [hHD, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := mul_le_mul_of_nonneg_right (hV (2 * x) ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [mul_comm] using h
  have h := hmean hk hM (by nlinarith : 1 < R ^ 2) hsmall g hg hclose hupper hH hV'
  have hsum : (∑ n ∈ Finset.Icc 0 (R ^ 2),
      H (Real.log n / Real.log (R ^ 2 : ℕ)) * roughSieveWeight M g n) =
        ∑ n ∈ Finset.Icc 0 (R ^ 2), G (Real.log n / Real.log R) * roughSieveWeight M g n := by
    simp only [H, twice_log_ratio_sq]
  have hint : sieveMainConstant M g * Real.log (R ^ 2 : ℕ) *
      (∫ x in (0 : ℝ)..1, H x) =
        sieveMainConstant M g * Real.log R * (∫ x in (0 : ℝ)..2, G x) := by
    rw [show (∫ x in (0 : ℝ)..1, H x) =
        (1 / 2) * (∫ x in (0 : ℝ)..2, G x) from integral_double_arg G, log_nat_sq]
    ring
  rw [hsum, hint] at h
  simpa only [H, mul_one] using h

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_roughSieveWeight_double_smooth_error_logScale
