/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMixedTensorMean
import ErdosProblems.Erdos4b.FGKMTTensorDenominators

/-! # The mixed tensor mean for both actual sieve denominator families -/

namespace Erdos4b.FGKMT

noncomputable section

theorem exists_actualMixedTensorSieveSum_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j : ℕ}, 2 ≤ k → 0 < M → 1 < R → j + 1 ≤ k →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) → ∀ pinned : Bool,
      ∀ {H G : ℝ → ℝ}, ContDiff ℝ 1 H → ContDiff ℝ 1 G →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G x) →
      0 < (∫ x in (0 : ℝ)..1, H x) → 0 < (∫ x in (0 : ℝ)..1, G x) →
      ∀ {VH VG Ω : ℝ}, 0 ≤ Ω →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv H x| ≤ VH) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv G x| ≤ VG) →
      |H 1| + VH ≤ Ω * (∫ x in (0 : ℝ)..1, H x) →
      |G 1| + VG ≤ Ω * (∫ x in (0 : ℝ)..1, G x) →
      (j + 1 : ℕ) * (C * Ω * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) ≤ 1 →
      |mixedTensorSieveSum M (actualSieveDenominator pinned k) R j H G -
          multivariateSieveConstant M (actualSieveDenominator pinned k) (j + 1) *
            (Real.log R * (∫ x in (0 : ℝ)..1, H x)) *
              (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j| /
        (multivariateSieveConstant M (actualSieveDenominator pinned k) (j + 1) *
          (Real.log R * (∫ x in (0 : ℝ)..1, H x)) *
            (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j) ≤
        4 * (j + 1 : ℕ) * (C * Ω * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) := by
  obtain ⟨C, hC, hbound⟩ := exists_mixedTensorSieveSum_relative_error
  refine ⟨C, hC, ?_⟩
  intro k M R j hk hM hR hj hsmall pinned H G hH hG hG0 hHmass hGmass VH VG Ω
    hΩ hVH hVG hHcost hGcost htotal
  exact hbound (by omega : 0 < k) hM hR hj
    (fun p hp hpk => hsmall p hp (by omega)) _
    (actualSieveDenominator_chain hk hj hsmall pinned) hH hG hG0 hHmass hGmass
    hΩ hVH hVG hHcost hGcost htotal

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_actualMixedTensorSieveSum_relative_error
