/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCutoffMean

/-!
# The dimension-uniform cutoff error on the tensor scale

The normalization uses the positive tensor mass, so the theorem also
applies to signed cutoffs or to a cutoff with zero integral. For the
actual sieve profile, a separate lower bound compares its energy to
this tensor mass.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem exists_cutoffSieveSum_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j J : ℕ}, 0 < k → 0 < M → 1 < R → j ≤ J →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) → ∀ g : ℕ → ℝ,
      (∀ s : ℕ, s < j → ∀ p : ℕ, p.Prime → ¬p ∣ M →
        (p : ℝ) / 2 ≤ g p + s ∧ |g p + s - p| ≤ 2 * (k : ℝ) ∧ g p + s ≤ p - 1) →
      ∀ {G : ℝ → ℝ}, ContDiff ℝ 1 G →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G x) →
      0 < (∫ x in (0 : ℝ)..1, G x) → ∀ {V Ω : ℝ}, 0 ≤ Ω →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv G x| ≤ V) →
      |G 1| + V ≤ Ω * (∫ x in (0 : ℝ)..1, G x) →
      (j : ℝ) * (C * Ω * modulusLogScale (M * R ^ J) ^ 3 / Real.log R) ≤ 1 →
      ∀ (Φ : ℝ → ℝ) (K : ℝ), BoundedCutoff Φ K → ∀ u : ℝ,
      |cutoffSieveSum M g R j G Φ u -
          multivariateSieveConstant M g j * Real.log R ^ j * cutoffCubeIntegral G Φ j u| /
        (multivariateSieveConstant M g j * (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j) ≤
          2 * K * (j : ℝ) * (C * Ω * modulusLogScale (M * R ^ J) ^ 3 / Real.log R) := by
  obtain ⟨C, hC, hbound⟩ := exists_cutoffSieveSum_geometric_error
  refine ⟨C, hC, ?_⟩
  intro k M R j J hk hM hR hj hsmall g hchain G hG hG0 hmass V Ω hΩ hV hcost htotal Φ K hΦ u
  let A : ℝ := Real.log R * (∫ x in (0 : ℝ)..1, G x)
  let B : ℝ := C * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V)
  let ε : ℝ := C * Ω * modulusLogScale (M * R ^ J) ^ 3 / Real.log R
  have hlog : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hA : 0 < A := mul_pos hlog hmass
  have hK := hΦ.constant_nonneg
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0 ⟨le_rfl, zero_le_one⟩)
  have hscale : 0 ≤ modulusLogScale (M * R ^ J) :=
    zero_le_one.trans (one_le_modulusLogScale _)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hBA : B ≤ A * ε := by
    calc
      _ ≤ (C * modulusLogScale (M * R ^ J) ^ 3) *
          (Ω * (∫ x in (0 : ℝ)..1, G x)) :=
        mul_le_mul_of_nonneg_left hcost (by positivity)
      _ = _ := by dsimp only [A, ε]; field_simp
  have hPi := multivariateSieveConstant_pos hk hM hsmall g hchain
  have hmain : 0 < multivariateSieveConstant M g j * A ^ j := mul_pos hPi (pow_pos hA j)
  apply (div_le_iff₀ hmain).mpr
  have h := hbound hk hM hR hsmall hG hG0 hV j hj g hchain Φ K hΦ u
  change |cutoffSieveSum M g R j G Φ u -
      multivariateSieveConstant M g j * Real.log R ^ j * cutoffCubeIntegral G Φ j u| ≤
    K * multivariateSieveConstant M g j * ((A + B) ^ j - A ^ j) at h
  calc
    _ ≤ K * multivariateSieveConstant M g j * ((A + B) ^ j - A ^ j) := h
    _ ≤ K * multivariateSieveConstant M g j * (A ^ j * (2 * (j : ℝ) * ε)) :=
      mul_le_mul_of_nonneg_left (geometric_error_le_linear hA.le hB hε hBA j htotal)
        (mul_nonneg hK hPi.le)
    _ = _ := by dsimp only [ε]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_cutoffSieveSum_relative_error
