/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTensorMean

/-!
# The relative, dimension-uniform tensor error

If the endpoint and derivative cost is at most `Ω` times the profile
mass, the relative error is at most twice the total coordinate error
`j * C * Ω * L^3 / log R`, whenever that total is at most one.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem multivariateSieveConstant_pos {k M j : ℕ} (hk : 0 < k) (hM : 0 < M)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) (g : ℕ → ℝ)
    (hchain : ∀ s : ℕ, s < j → ∀ p : ℕ, p.Prime → ¬p ∣ M →
      (p : ℝ) / 2 ≤ g p + s ∧ |g p + s - p| ≤ 2 * (k : ℝ) ∧ g p + s ≤ p - 1) :
    0 < multivariateSieveConstant M g j := by
  apply Finset.prod_pos
  intro s hs
  have hb := hchain s (Finset.mem_range.mp hs)
  exact sieveMainConstant_pos hk hM hsmall _
    (fun p hp hpM => (hb p hp hpM).1)
    (fun p hp hpM => (hb p hp hpM).2.1)
    (fun p hp hpM => (hb p hp hpM).2.2)

theorem exists_tensorSieveSum_relative_error :
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
      |tensorSieveSum M g R j G -
          multivariateSieveConstant M g j * (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j| /
        (multivariateSieveConstant M g j * (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j) ≤
          2 * (j : ℝ) * (C * Ω * modulusLogScale (M * R ^ J) ^ 3 / Real.log R) := by
  obtain ⟨C, hC, hbound⟩ := exists_tensorSieveSum_geometric_error
  refine ⟨C, hC, ?_⟩
  intro k M R j J hk hM hR hj hsmall g hchain G hG hG0 hmass V Ω hΩ hV hcost htotal
  let A : ℝ := Real.log R * (∫ x in (0 : ℝ)..1, G x)
  let B : ℝ := C * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V)
  let ε : ℝ := C * Ω * modulusLogScale (M * R ^ J) ^ 3 / Real.log R
  have hlog : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hA : 0 < A := mul_pos hlog hmass
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
  have h := hbound hk hM hR hj hsmall g hchain hG hG0 hV
  change |tensorSieveSum M g R j G - multivariateSieveConstant M g j * A ^ j| ≤
    multivariateSieveConstant M g j * ((A + B) ^ j - A ^ j) at h
  calc
    _ ≤ multivariateSieveConstant M g j * ((A + B) ^ j - A ^ j) := h
    _ ≤ multivariateSieveConstant M g j * (A ^ j * (2 * (j : ℝ) * ε)) :=
      mul_le_mul_of_nonneg_left (geometric_error_le_linear hA.le hB hε hBA j htotal) hPi.le
    _ = _ := by dsimp only [ε]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_tensorSieveSum_relative_error
