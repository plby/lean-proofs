/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTLongTensorSum
import ErdosProblems.Erdos4b.FGKMTMixedTensorMean

/-!
# The full-support long-factor mean for every admissible denominator chain

The profile hypotheses are all discharged at the intended scales.
The main term uses the original `log R`, the full long mass, and the
short masses. Rescaling changes neither that main term nor the sum.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem exists_generalLongTensorSieveSum_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R → j + 1 ≤ k →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) → ∀ g : ℕ → ℝ,
      (∀ s : ℕ, s < j + 1 → ∀ p : ℕ, p.Prime → ¬p ∣ M →
        (p : ℝ) / 2 ≤ g p + s ∧ |g p + s - p| ≤ 2 * (k : ℝ) ∧ g p + s ≤ p - 1) →
      (j + 1 : ℕ) *
        (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) ≤ 1 →
      |longTensorSieveSum k M g R j -
          multivariateSieveConstant M g (j + 1) *
            (Real.log R * dimensionLongMass k) * (Real.log R * dimensionProfileMass k) ^ j| /
        (multivariateSieveConstant M g (j + 1) *
          (Real.log R * dimensionLongMass k) * (Real.log R * dimensionProfileMass k) ^ j) ≤
        (j + 1 : ℕ) *
          (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) := by
  obtain ⟨K, hK, hψ⟩ := exists_sieveCutoff_bounded
  obtain ⟨C₀, hC₀, hbound⟩ := exists_mixedTensorSieveSum_relative_error
  let C : ℝ := 8 * C₀ * (4 * K + 6)
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro k M R j hk hlog hM hR hj hsmall g hchain htotal
  have hk0 : 0 < k := by omega
  have hb := profile_scales_bounds hk0 hlog
  have hT2 : 1 ≤ 2 * sieveProfileScale k := by linarith [hb.1]
  have hU2 : 0 < sieveProfileWidth k / 2 := div_pos hb.2.1 (by norm_num)
  have hU21 : sieveProfileWidth k / 2 ≤ 1 := by linarith [hb.2.2.1]
  have hTU2 : 2 ≤ (2 * sieveProfileScale k) * (sieveProfileWidth k / 2) := by
    nlinarith [hb.2.2.2]
  have hTL : 2 ≤ (2 * sieveProfileScale k) * 1 := by linarith [hb.1]
  have hR2 : 1 < R ^ 2 := by nlinarith
  let Ω : ℝ := (4 * K + 6) * (2 * sieveProfileScale k) ^ 2
  let Λ := modulusLogScale (M * R ^ (2 * k))
  let ε₀ : ℝ := C₀ * Ω * Λ ^ 3 / Real.log (R ^ 2 : ℕ)
  let ε : ℝ := C * sieveProfileScale k ^ 2 * Λ ^ 3 / Real.log R
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_modulusLogScale _)
  have hlogR2 : 0 < Real.log (R ^ 2 : ℕ) := Real.log_pos (by exact_mod_cast hR2)
  have hΩ : 0 ≤ Ω := by dsimp only [Ω]; positivity
  have hε₀ : 0 ≤ ε₀ := by dsimp only [ε₀]; positivity
  have heq : ε = 4 * ε₀ := by
    dsimp only [ε, ε₀, Ω, C]
    rw [log_nat_sq]
    ring
  have htotal₀ : (j + 1 : ℕ) * ε₀ ≤ 1 := by
    change (j + 1 : ℕ) * ε ≤ 1 at htotal
    rw [heq] at htotal
    have hj0 : (0 : ℝ) ≤ (j + 1 : ℕ) := Nat.cast_nonneg _
    nlinarith
  have h := hbound hk0 hM hR2 (J := k) hj hsmall g hchain
    ((sieveFactor_contDiff (2 * sieveProfileScale k) 1 (n := 1)).pow 2)
    ((sieveFactor_contDiff (2 * sieveProfileScale k) (sieveProfileWidth k / 2) (n := 1)).pow 2)
    (fun t _ht => sq_nonneg (sieveFactor (2 * sieveProfileScale k) (sieveProfileWidth k / 2) t))
    (sieveFactor_sq_unit_mass_pos (zero_le_one.trans hT2) zero_lt_one (le_refl 1))
    (sieveFactor_sq_unit_mass_pos (zero_le_one.trans hT2) hU2 hU21) hΩ
    (fun t ht => sieveFactor_sq_deriv_bound (zero_le_one.trans hT2) zero_lt_one ht.1 hψ)
    (fun t ht => sieveFactor_sq_deriv_bound (zero_le_one.trans hT2) hU2 ht.1 hψ)
    (sieveFactor_sq_cost hT2 zero_lt_one (le_refl 1) hTL hψ)
    (sieveFactor_sq_cost hT2 hU2 hU21 hTU2 hψ)
    (by simpa only [← pow_mul] using htotal₀)
  rw [← longTensorSieveSum_eq_mixed, rescaled_long_log_mass, rescaled_short_log_mass hk0 hlog] at h
  calc
    _ ≤ 4 * (j + 1 : ℕ) * ε₀ := by simpa only [← pow_mul] using h
    _ = _ := by
      change 4 * (j + 1 : ℕ) * ε₀ = (j + 1 : ℕ) * ε
      rw [heq]
      ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_generalLongTensorSieveSum_relative_error
