/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedMainTerm

/-!
# Uniform relative mean for the actual pinned diagonal

The exact finite normalization is retained. The error constant is chosen
before all sieve parameters, and both the profile replacement and face
summation errors are controlled by one uniform smallness hypothesis.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem pinned_diagonal_relative_of_bounds {D F A J H ε η m : ℝ}
    (hA : 0 < A) (hJ : 0 < J) (hε : 0 ≤ ε)
    (hD : |D - A ^ 2 * F| ≤ 3 * ε * A ^ 2 * H)
    (hH : H ≤ 1200 * m ^ 2 * J) (hF : |F - J| / J ≤ η) :
    |D - A ^ 2 * J| / (A ^ 2 * J) ≤ 3600 * m ^ 2 * ε + η := by
  have hF' := (div_le_iff₀ hJ).mp hF
  apply (div_le_iff₀ (mul_pos (pow_pos hA 2) hJ)).mpr
  calc
    _ ≤ |D - A ^ 2 * F| + |A ^ 2 * F - A ^ 2 * J| := abs_sub_le _ _ _
    _ = |D - A ^ 2 * F| + A ^ 2 * |F - J| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg A)]
    _ ≤ (3 * ε * A ^ 2) * (1200 * m ^ 2 * J) + A ^ 2 * (η * J) :=
      add_le_add (hD.trans (mul_le_mul_of_nonneg_left hH (by positivity)))
        (mul_le_mul_of_nonneg_left hF' (sq_nonneg A))
    _ = _ := by ring

theorem exists_commonPinnedDiagonal_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      (m + 1 : ℕ) * (C * sieveProfileScale (m + 1) ^ 2 *
        modulusLogScale (M * R ^ (2 * (m + 1))) ^ 3 / Real.log R) ≤ 1 →
      ∀ j : Fin (m + 1),
        |commonPinnedDiagonal m M R j - commonPinnedMainTerm m M R| /
          commonPinnedMainTerm m M R ≤
          (m + 1 : ℕ) * (C * sieveProfileScale (m + 1) ^ 2 *
            modulusLogScale (M * R ^ (2 * (m + 1))) ^ 3 / Real.log R) := by
  obtain ⟨Ce, hCe, herror⟩ := exists_commonPinnedDiagonal_replacement_error
  obtain ⟨Cm, hCm, hmajor⟩ := exists_commonPinnedFaceMajorantSum_bound
  obtain ⟨Cf, hCf, hface⟩ := exists_commonFaceDiagonal_relative_error
  let C := Cm + Cf + 3600 * Ce
  have hC : 0 < C := by dsimp only [C]; positivity
  have heC : Ce ≤ C := by dsimp only [C]; linarith
  have hmC : Cm ≤ C := by dsimp only [C]; linarith
  have hfC : Cf ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro m M R hm hlog hM hR hsmall htotal j
  let k := m + 1
  let T := sieveProfileScale k
  let Λ := modulusLogScale (M * R ^ (2 * k))
  let Q := (k : ℝ) * (T ^ 2 * Λ ^ 3 / Real.log R)
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hmk : (m : ℝ) ≤ k := by exact_mod_cast (Nat.le_succ m)
  have hkT : (k : ℝ) ≤ T :=
    le_mul_of_one_le_right (Nat.cast_nonneg k) (by linarith : 1 ≤ Real.log k)
  have hT1 : 1 ≤ T := hkR.trans hkT
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  have hTT : T ≤ T ^ 2 := by nlinarith
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_modulusLogScale _)
  have hD : 0 ≤ modulusLogScale (M * R) := zero_le_one.trans (one_le_modulusLogScale _)
  have hD' : 0 ≤ modulusLogScale (M * R ^ k) := zero_le_one.trans (one_le_modulusLogScale _)
  have hDΛ : modulusLogScale (M * R) ≤ Λ :=
    modulusLogScale_mono (Nat.mul_pos hM (by omega))
      (Nat.mul_le_mul_left M (by
        simpa only [pow_one] using
          Nat.pow_le_pow_right (by omega : 1 ≤ R) (by omega : 1 ≤ 2 * k)))
  have hD'Λ : modulusLogScale (M * R ^ k) ≤ Λ :=
    modulusLogScale_mono (Nat.mul_pos hM (pow_pos (by omega : 0 < R) k))
      (Nat.mul_le_mul_left M
        (Nat.pow_le_pow_right (by omega : 1 ≤ R) (by omega : k ≤ 2 * k)))
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have htotal' : C * Q ≤ 1 := by
    convert htotal using 1
    dsimp only [Q, k, T, Λ]
    ring
  have hprofile : Ce * (m + 1 : ℕ) * sieveProfileScale (m + 1) *
      modulusLogScale (M * R) ^ 3 ≤ Real.log R := by
    have he : Ce * (k : ℝ) * T * modulusLogScale (M * R) ^ 3 / Real.log R ≤ C * Q := by
      calc
        _ ≤ C * (k : ℝ) * T ^ 2 * Λ ^ 3 / Real.log R := by gcongr
        _ = _ := by dsimp only [Q]; ring
    have h := (div_le_iff₀ hL).mp (he.trans htotal')
    simpa only [one_mul] using h
  have hmajorCost : (m : ℝ) * (Cm * sieveProfileScale (m + 1) ^ 2 *
      modulusLogScale (M * R ^ (2 * (m + 1))) ^ 3 / Real.log R) ≤ 1 := by
    apply le_trans _ htotal
    gcongr
  have hfaceCost : (m : ℝ) * (Cf * sieveProfileScale (m + 1) ^ 2 *
      modulusLogScale (M * R ^ (m + 1)) ^ 3 / Real.log R) ≤ 1 := by
    apply le_trans _ htotal
    gcongr
  let p : commonPrimeUniverse M R → ℕ := fun q => q.val
  let A := pinnedGlobalNormalization m M p * Real.log R
  have hA : 0 < A := mul_pos
    (pinnedGlobalNormalization_pos (seven_le_of_profile_log hlog) hM hsmall
      commonPrimeUniverse_prime Subtype.val_injective commonPrimeUniverse_not_dvd) hL
  have hJ := commonFaceMainTerm_pos hm hlog hM hR hsmall
  have h := pinned_diagonal_relative_of_bounds hA hJ
    (show 0 ≤ Ce * T * modulusLogScale (M * R) ^ 3 / Real.log R by positivity)
    (herror hm hlog hM hR hsmall hprofile j) (hmajor hm hlog hM hR hsmall hmajorCost)
    (hface hm hlog hM hR hsmall hfaceCost)
  have hmkT : (m : ℝ) ^ 2 ≤ (k : ℝ) * T := by
    calc
      _ ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg m) hmk 2
      _ ≤ (k : ℝ) * T := by nlinarith
  have heQ : 3600 * (m : ℝ) ^ 2 *
      (Ce * T * modulusLogScale (M * R) ^ 3 / Real.log R) ≤ (3600 * Ce) * Q := by
    calc
      _ = (3600 * Ce) * ((m : ℝ) ^ 2 * T * modulusLogScale (M * R) ^ 3 / Real.log R) := by
        ring
      _ ≤ (3600 * Ce) * (((k : ℝ) * T) * T * Λ ^ 3 / Real.log R) := by gcongr
      _ = _ := by dsimp only [Q]; ring
  have hfQ : (m : ℝ) * (Cf * sieveProfileScale (m + 1) ^ 2 *
      modulusLogScale (M * R ^ (m + 1)) ^ 3 / Real.log R) ≤ Cf * Q := by
    calc
      _ ≤ (k : ℝ) * (Cf * T ^ 2 * Λ ^ 3 / Real.log R) := by gcongr
      _ = _ := by dsimp only [Q]; ring
  calc
    _ ≤ 3600 * (m : ℝ) ^ 2 * (Ce * T * modulusLogScale (M * R) ^ 3 / Real.log R) +
        (m : ℝ) * (Cf * sieveProfileScale (m + 1) ^ 2 *
          modulusLogScale (M * R ^ (m + 1)) ^ 3 / Real.log R) := h
    _ ≤ (3600 * Ce) * Q + Cf * Q := add_le_add heQ hfQ
    _ ≤ C * Q := by dsimp only [C]; nlinarith [mul_nonneg hCm.le hQ]
    _ = _ := by dsimp only [Q, T, k, Λ]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPinnedDiagonal_relative_error
