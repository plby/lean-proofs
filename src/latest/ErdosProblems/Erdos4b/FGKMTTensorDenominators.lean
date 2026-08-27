/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTensorRelative

/-!
# The actual unpinned and pinned tensor means

Both denominator families satisfy every shifted hypothesis of the
multivariate estimate. The boolean selects only the two literal local
denominators computed in the sieve; no analytic hypothesis is added.
-/

namespace Erdos4b.FGKMT

noncomputable section

def actualSieveDenominator (pinned : Bool) (k p : ℕ) : ℝ :=
  if pinned then pinnedLocalDenominator k p else (p : ℝ) - k

theorem actualSieveDenominator_chain {k M j : ℕ} (hk : 2 ≤ k) (hj : j ≤ k)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) (pinned : Bool) :
    ∀ s : ℕ, s < j → ∀ p : ℕ, p.Prime → ¬p ∣ M →
      (p : ℝ) / 2 ≤ actualSieveDenominator pinned k p + s ∧
        |actualSieveDenominator pinned k p + s - p| ≤ 2 * (k : ℝ) ∧
        actualSieveDenominator pinned k p + s ≤ p - 1 := by
  intro s hs p hp hpM
  have hrough : 2 * (k : ℝ) ^ 2 < p := by
    have hn : 2 * k ^ 2 < p := by
      by_contra hnot
      exact hpM (hsmall p hp (by omega))
    exact_mod_cast hn
  cases pinned with
  | false => exact shiftedDenominator_bounds hk (hs.trans_le hj) hrough
  | true => exact pinnedShiftedDenominator_bounds hk (hs.trans_le hj) hrough

theorem exists_actualTensorSieveSum_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j : ℕ}, 2 ≤ k → 0 < M → 1 < R → j ≤ k →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) → ∀ pinned : Bool,
      ∀ {G : ℝ → ℝ}, ContDiff ℝ 1 G →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G x) →
      0 < (∫ x in (0 : ℝ)..1, G x) → ∀ {V Ω : ℝ}, 0 ≤ Ω →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv G x| ≤ V) →
      |G 1| + V ≤ Ω * (∫ x in (0 : ℝ)..1, G x) →
      (j : ℝ) * (C * Ω * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) ≤ 1 →
      |tensorSieveSum M (actualSieveDenominator pinned k) R j G -
          multivariateSieveConstant M (actualSieveDenominator pinned k) j *
            (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j| /
        (multivariateSieveConstant M (actualSieveDenominator pinned k) j *
          (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j) ≤
          2 * (j : ℝ) * (C * Ω * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) := by
  obtain ⟨C, hC, hbound⟩ := exists_tensorSieveSum_relative_error
  refine ⟨C, hC, ?_⟩
  intro k M R j hk hM hR hj hsmall pinned G hG hG0 hmass V Ω hΩ hV hcost htotal
  exact hbound (by omega : 0 < k) hM hR hj
    (fun p hp hpk => hsmall p hp (by omega)) _
    (actualSieveDenominator_chain hk hj hsmall pinned) hG hG0 hmass hΩ hV hcost htotal

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_actualTensorSieveSum_relative_error
