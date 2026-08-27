/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCommonOffDiagonalRelative

/-!
# The full common-coefficient quadratic mean

The diagonal mean and the complete off-diagonal estimate are now on
one positive main-term scale. One uniform error coefficient controls
both required smallness conditions and their summed relative error.
-/

namespace Erdos4b.FGKMT

noncomputable section

def sieveQuadraticErrorScale (k M R : ℕ) : ℝ :=
  (k : ℝ) * (sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) +
    (k : ℝ) ^ 3 * sieveProfileScale k / Real.log R

theorem sieveQuadraticErrorScale_nonneg (k M R : ℕ) : 0 ≤ sieveQuadraticErrorScale k M R := by
  have hT : 0 ≤ sieveProfileScale k := mul_nonneg (Nat.cast_nonneg k) (Real.log_natCast_nonneg k)
  have hΛ : 0 ≤ modulusLogScale (M * R ^ (2 * k)) :=
    zero_le_one.trans (one_le_modulusLogScale _)
  have hL := Real.log_natCast_nonneg R
  unfold sieveQuadraticErrorScale
  positivity

theorem modulusLogScale_power_double {M R k : ℕ} (hM : 0 < M) (hR : 1 < R) :
    modulusLogScale (M * R ^ k) ≤ modulusLogScale (M * R ^ (2 * k)) :=
  modulusLogScale_mono (Nat.mul_pos hM (pow_pos (by omega : 0 < R) k))
    (Nat.mul_le_mul_left M (Nat.pow_le_pow_right (by omega : 1 ≤ R) (by omega : k ≤ 2 * k)))

theorem exists_commonSieveQuadratic_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) →
      C * sieveQuadraticErrorScale k M R ≤ 1 →
      |commonSieveQuadratic k M R - commonSieveMainTerm k M R| / commonSieveMainTerm k M R ≤
        C * sieveQuadraticErrorScale k M R := by
  obtain ⟨Co, hCo, hoff⟩ := exists_commonSieveQuadratic_offDiagonal_relative_error
  obtain ⟨Cd, hCd, hdiag⟩ := exists_commonSieveDiagonal_relative_error
  let C := Co + Cd
  have hC : 0 < C := add_pos hCo hCd
  have hoC : Co ≤ C := le_add_of_nonneg_right hCd.le
  have hdC : Cd ≤ C := le_add_of_nonneg_left hCo.le
  refine ⟨C, hC, ?_⟩
  intro k M R hk hlog hM hR hsmall htotal
  let A := (k : ℝ) *
    (sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R)
  let B := (k : ℝ) ^ 3 * sieveProfileScale k / Real.log R
  have hT : 0 ≤ sieveProfileScale k :=
    zero_le_one.trans (profile_scales_bounds (by omega : 0 < k) hlog).1
  have hΛ : 0 ≤ modulusLogScale (M * R ^ (2 * k)) :=
    zero_le_one.trans (one_le_modulusLogScale _)
  have hΛ' : 0 ≤ modulusLogScale (M * R ^ k) := zero_le_one.trans (one_le_modulusLogScale _)
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hAB : A ≤ A + B := le_add_of_nonneg_right hB
  have hscale : sieveQuadraticErrorScale k M R = A + B := rfl
  have hD : (k : ℝ) *
      (Cd * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) ≤ Cd * A := by
    calc
      _ ≤ (k : ℝ) *
          (Cd * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) := by
        gcongr
        exact modulusLogScale_power_double hM hR
      _ = _ := by dsimp only [A]; ring
  have hsmallo : (k : ℝ) *
      (Co * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) ≤ 1 := by
    calc
      _ = Co * A := by dsimp only [A]; ring
      _ ≤ C * (A + B) := mul_le_mul hoC hAB hA hC.le
      _ ≤ 1 := by simpa only [hscale] using htotal
  have hsmalld : (k : ℝ) *
      (Cd * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) ≤ 1 :=
    hD.trans ((mul_le_mul hdC hAB hA hC.le).trans (by simpa only [hscale] using htotal))
  have ho : |commonSieveQuadratic k M R - commonSieveDiagonal k M R| /
      commonSieveMainTerm k M R ≤ Co * B := by
    convert hoff hk hlog hM hR hsmall hsmallo using 1
    dsimp only [B]
    ring
  have hd : |commonSieveDiagonal k M R - commonSieveMainTerm k M R| /
      commonSieveMainTerm k M R ≤ Cd * A := (hdiag hk hlog hM hR hsmall hsmalld).trans hD
  have hmain := commonSieveMainTerm_pos hk hlog hM hR hsmall
  calc
    _ ≤ |commonSieveQuadratic k M R - commonSieveDiagonal k M R| / commonSieveMainTerm k M R +
        |commonSieveDiagonal k M R - commonSieveMainTerm k M R| / commonSieveMainTerm k M R := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (abs_sub_le _ _ _) hmain.le
    _ ≤ Co * B + Cd * A := add_le_add ho hd
    _ ≤ C * (A + B) := by
      dsimp only [C]
      nlinarith [mul_nonneg hCo.le hA, mul_nonneg hCd.le hB]
    _ = _ := by rw [hscale]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonSieveQuadratic_relative_error
