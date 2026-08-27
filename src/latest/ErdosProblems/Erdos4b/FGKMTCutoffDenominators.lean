/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCutoffRelative
import ErdosProblems.Erdos4b.FGKMTTensorDenominators

/-!
# Coupled cutoff means for the actual sieve denominators

All arithmetic hypotheses are verified for both the unpinned and pinned
families, with the dimension allowed to vary. The remaining assumptions
are the explicit size and regularity conditions on the test profile.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem exists_actualCutoffSieveSum_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j : ℕ}, 2 ≤ k → 0 < M → 1 < R → j ≤ k →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) → ∀ pinned : Bool,
      ∀ {G : ℝ → ℝ}, ContDiff ℝ 1 G →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G x) →
      0 < (∫ x in (0 : ℝ)..1, G x) → ∀ {V Ω : ℝ}, 0 ≤ Ω →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv G x| ≤ V) →
      |G 1| + V ≤ Ω * (∫ x in (0 : ℝ)..1, G x) →
      (j : ℝ) * (C * Ω * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) ≤ 1 →
      ∀ (Φ : ℝ → ℝ) (K : ℝ), BoundedCutoff Φ K → ∀ u : ℝ,
      |cutoffSieveSum M (actualSieveDenominator pinned k) R j G Φ u -
          multivariateSieveConstant M (actualSieveDenominator pinned k) j *
            Real.log R ^ j * cutoffCubeIntegral G Φ j u| /
        (multivariateSieveConstant M (actualSieveDenominator pinned k) j *
          (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j) ≤
          2 * K * (j : ℝ) * (C * Ω * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) := by
  obtain ⟨C, hC, hbound⟩ := exists_cutoffSieveSum_relative_error
  refine ⟨C, hC, ?_⟩
  intro k M R j hk hM hR hj hsmall pinned G hG hG0 hmass V Ω hΩ hV hcost htotal Φ K hΦ u
  exact hbound (by omega : 0 < k) hM hR hj
    (fun p hp hpk => hsmall p hp (by omega)) _
    (actualSieveDenominator_chain hk hj hsmall pinned) hG hG0 hmass hΩ hV hcost htotal Φ K hΦ u

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_actualCutoffSieveSum_relative_error
