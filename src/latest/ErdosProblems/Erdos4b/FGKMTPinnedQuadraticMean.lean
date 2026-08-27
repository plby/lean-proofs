/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedOffDiagonalRelative
import ErdosProblems.Erdos4b.FGKMTPinnedDiagonalMean

/-! # Uniform mean of the full original pinned quadratic form -/

namespace Erdos4b.FGKMT

noncomputable section

theorem exists_commonPinnedQuadratic_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      C * sieveQuadraticErrorScale (m + 1) M R ≤ 1 → ∀ j : Fin (m + 1),
        |commonPinnedQuadratic m M R j - commonPinnedMainTerm m M R| /
          commonPinnedMainTerm m M R ≤ C * sieveQuadraticErrorScale (m + 1) M R := by
  obtain ⟨Co, hCo, hoff⟩ := exists_commonPinnedQuadratic_offDiagonal_relative_error
  obtain ⟨Cd, hCd, hdiag⟩ := exists_commonPinnedDiagonal_relative_error
  let C := Co + Cd
  have hC : 0 < C := add_pos hCo hCd
  have hoC : Co ≤ C := le_add_of_nonneg_right hCd.le
  have hdC : Cd ≤ C := le_add_of_nonneg_left hCo.le
  refine ⟨C, hC, ?_⟩
  intro m M R hm hlog hM hR hsmall htotal j
  let Q := sieveQuadraticErrorScale (m + 1) M R
  let P := (m + 1 : ℕ) * (sieveProfileScale (m + 1) ^ 2 *
    modulusLogScale (M * R ^ (2 * (m + 1))) ^ 3 / Real.log R)
  have hQ : 0 ≤ Q := sieveQuadraticErrorScale_nonneg _ _ _
  have hT : 0 ≤ sieveProfileScale (m + 1) :=
    zero_le_one.trans (profile_scales_bounds (Nat.succ_pos m) hlog).1
  have hΛ : 0 ≤ modulusLogScale (M * R ^ (2 * (m + 1))) :=
    zero_le_one.trans (one_le_modulusLogScale _)
  have hL : 0 ≤ Real.log R := Real.log_natCast_nonneg R
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hPQ : P ≤ Q := le_add_of_nonneg_right (by
    change 0 ≤ (m + 1 : ℕ) ^ 3 * sieveProfileScale (m + 1) / Real.log R
    positivity)
  have hsmallo : Co * Q ≤ 1 := (mul_le_mul_of_nonneg_right hoC hQ).trans htotal
  have hsmalld : (m + 1 : ℕ) * (Cd * sieveProfileScale (m + 1) ^ 2 *
      modulusLogScale (M * R ^ (2 * (m + 1))) ^ 3 / Real.log R) ≤ 1 := by
    calc
      _ = Cd * P := by dsimp only [P]; ring
      _ ≤ C * Q := mul_le_mul hdC hPQ hP hC.le
      _ ≤ 1 := htotal
  have ho := hoff hm hlog hM hR hsmall hsmallo j
  have hd : |commonPinnedDiagonal m M R j - commonPinnedMainTerm m M R| /
      commonPinnedMainTerm m M R ≤ Cd * Q := by
    have h := hdiag hm hlog hM hR hsmall hsmalld j
    calc
      _ ≤ Cd * P := by
        convert h using 1
        all_goals first | rfl | (dsimp only [P]; ring)
      _ ≤ Cd * Q := mul_le_mul_of_nonneg_left hPQ hCd.le
  have hmain := commonPinnedMainTerm_pos hm hlog hM hR hsmall
  calc
    _ ≤ |commonPinnedQuadratic m M R j - commonPinnedDiagonal m M R j| /
        commonPinnedMainTerm m M R +
        |commonPinnedDiagonal m M R j - commonPinnedMainTerm m M R| /
          commonPinnedMainTerm m M R := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (abs_sub_le _ _ _) hmain.le
    _ ≤ Co * Q + Cd * Q := add_le_add ho hd
    _ = C * Q := by dsimp only [C]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPinnedQuadratic_relative_error
