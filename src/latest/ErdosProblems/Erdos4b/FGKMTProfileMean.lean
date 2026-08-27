/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTProfileCost
import ErdosProblems.Erdos4b.FGKMTCutoffDenominators

/-!
# Uniform summation for the actual squared sieve profile

All regularity and cost hypotheses of the coupled-cutoff estimate are
now discharged. The final constant is absolute, chosen before all
dimensions, arithmetic parameters, and profile scales. The error is
still normalized by the positive tensor mass; the separate coupled
energy lower bound is needed to change that normalization.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem exists_sieveProfile_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j : ℕ}, 2 ≤ k → 0 < M → 1 < R → j ≤ k →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) → ∀ pinned : Bool,
      ∀ {T U : ℝ}, 1 ≤ T → 0 < U → U ≤ 1 → 2 ≤ T * U →
      (j : ℝ) * (C * T ^ 2 * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) ≤ 1 →
      |cutoffSieveSum M (actualSieveDenominator pinned k) R j
          (fun t => sieveFactor T U t ^ 2) (fun t => sieveCutoff t ^ 2) 0 -
        multivariateSieveConstant M (actualSieveDenominator pinned k) j * Real.log R ^ j *
          cutoffCubeIntegral (fun t => sieveFactor T U t ^ 2) (fun t => sieveCutoff t ^ 2) j 0| /
        (multivariateSieveConstant M (actualSieveDenominator pinned k) j *
          (Real.log R * (∫ t in (0 : ℝ)..1, sieveFactor T U t ^ 2)) ^ j) ≤
        (j : ℝ) * (C * T ^ 2 * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) := by
  obtain ⟨K, hK, hψ⟩ := exists_sieveCutoff_bounded
  obtain ⟨C₀, hC₀, hbound⟩ := exists_actualCutoffSieveSum_relative_error
  let C : ℝ := 4 * K * C₀ * (4 * K + 6)
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro k M R j hk hM hR hj hsmall pinned T U hT hU hU1 hTU htotal
  let Ω : ℝ := (4 * K + 6) * T ^ 2
  let ε₀ : ℝ := C₀ * Ω * modulusLogScale (M * R ^ k) ^ 3 / Real.log R
  let ε : ℝ := C * T ^ 2 * modulusLogScale (M * R ^ k) ^ 3 / Real.log R
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hlog : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hscale : 0 ≤ modulusLogScale (M * R ^ k) :=
    zero_le_one.trans (one_le_modulusLogScale _)
  have hΩ : 0 ≤ Ω := by dsimp only [Ω]; positivity
  have hε₀ : 0 ≤ ε₀ := by dsimp only [ε₀]; positivity
  have heq : ε = (4 * K) * ε₀ := by dsimp only [ε, ε₀, Ω, C]; ring
  have hεle : ε₀ ≤ ε := by rw [heq]; nlinarith
  have htotal₀ : (j : ℝ) * ε₀ ≤ 1 :=
    (mul_le_mul_of_nonneg_left hεle (Nat.cast_nonneg j)).trans htotal
  have h := hbound hk hM hR hj hsmall pinned
    ((sieveFactor_contDiff T U (n := 1)).pow 2)
    (fun t _ht => sq_nonneg (sieveFactor T U t))
    (sieveFactor_sq_unit_mass_pos hT0 hU hU1) hΩ
    (fun t ht => sieveFactor_sq_deriv_bound hT0 hU ht.1 hψ)
    (sieveFactor_sq_cost hT hU hU1 hTU hψ) htotal₀
    (fun t => sieveCutoff t ^ 2) (2 * K) (sieveCutoff_sq_bounded hK hψ) 0
  calc
    _ ≤ 2 * (2 * K) * (j : ℝ) * ε₀ := h
    _ = (j : ℝ) * ε := by rw [heq]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_sieveProfile_relative_error
