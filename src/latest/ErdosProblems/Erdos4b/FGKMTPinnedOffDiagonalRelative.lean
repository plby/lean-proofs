/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedOffDiagonal
import ErdosProblems.Erdos4b.FGKMTCommonQuadraticMean

/-! # The full pinned off-diagonal error on the positive finite main-term scale -/

namespace Erdos4b.FGKMT

noncomputable section

theorem pinned_offDiagonal_relative_of_bounds {E A H J C m k T D W L : ℝ}
    (hA : 0 < A) (hJ : 0 < J) (hC : 0 ≤ C) (hm : 0 ≤ m) (hmk : m ≤ k)
    (hk : 0 ≤ k) (hkT : k ≤ T) (hD : 0 ≤ D) (hDW : D ≤ W) (hL : 0 < L)
    (hH : H ≤ 1200 * Real.exp 4 * m ^ 2 * J)
    (hE : E ≤ (2 * A ^ 2) * H *
      (Real.exp 4 * ((C * T / L) * (16 * k) + 2 * (C * T * D / L)))) :
    E / (A ^ 2 * J) ≤ 38400 * Real.exp 8 * C *
      (k ^ 3 * T / L + k * (T ^ 2 * W / L)) := by
  have hT := hk.trans hkT
  have hW := hD.trans hDW
  have hm2 : m ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ hm hmk 2
  have hmkT : m ^ 2 ≤ k * T := hm2.trans (by nlinarith)
  have hfirst : m ^ 2 * k * T / L ≤ k ^ 3 * T / L := by
    calc
      _ ≤ k ^ 2 * k * T / L := by gcongr
      _ = _ := by ring
  have hsecond : m ^ 2 * T * D / L ≤ k * (T ^ 2 * W / L) := by
    calc
      _ ≤ (k * T) * T * W / L := by gcongr
      _ = _ := by ring
  have hpoly : 16 * (m ^ 2 * k * T / L) + 2 * (m ^ 2 * T * D / L) ≤
      16 * (k ^ 3 * T / L + k * (T ^ 2 * W / L)) := by
    have hnon : 0 ≤ k * (T ^ 2 * W / L) := by positivity
    linarith
  have hexp : Real.exp 4 * Real.exp 4 = Real.exp 8 := by rw [← Real.exp_add]; norm_num
  apply (div_le_iff₀ (mul_pos (pow_pos hA 2) hJ)).mpr
  calc
    E ≤ (2 * A ^ 2) * H *
        (Real.exp 4 * ((C * T / L) * (16 * k) + 2 * (C * T * D / L))) := hE
    _ ≤ (2 * A ^ 2) * (1200 * Real.exp 4 * m ^ 2 * J) *
        (Real.exp 4 * ((C * T / L) * (16 * k) + 2 * (C * T * D / L))) := by gcongr
    _ = (2400 * Real.exp 8 * C) *
        (16 * (m ^ 2 * k * T / L) + 2 * (m ^ 2 * T * D / L)) * (A ^ 2 * J) := by
      rw [← hexp]
      ring
    _ ≤ (2400 * Real.exp 8 * C) *
        (16 * (k ^ 3 * T / L + k * (T ^ 2 * W / L))) * (A ^ 2 * J) := by gcongr
    _ = _ := by ring

theorem exists_commonPinnedQuadratic_offDiagonal_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {m M R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      C * sieveQuadraticErrorScale (m + 1) M R ≤ 1 → ∀ j : Fin (m + 1),
      |commonPinnedQuadratic m M R j - commonPinnedDiagonal m M R j| /
        commonPinnedMainTerm m M R ≤ C * sieveQuadraticErrorScale (m + 1) M R := by
  obtain ⟨Ce, hCe, herror⟩ := exists_commonPinnedQuadratic_offDiagonal_bound
  obtain ⟨Cm, hCm, hmajor⟩ := exists_absolutePinnedFaceMajorantSum_energy_bound
  let K := 38400 * Real.exp 8 * Ce
  let C := Cm + Ce + K
  have hK : 0 < K := by dsimp only [K]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have heC : Ce ≤ C := by dsimp only [C]; linarith
  have hmC : Cm ≤ C := by dsimp only [C]; linarith
  have hKC : K ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro m M R hm hlog hM hR hsmall htotal j
  let k := m + 1
  let T := sieveProfileScale k
  let Λ := modulusLogScale (M * R ^ (2 * k))
  let Q := sieveQuadraticErrorScale k M R
  let P := (k : ℝ) * (T ^ 2 * Λ ^ 3 / Real.log R)
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hmk : (m : ℝ) ≤ k := by exact_mod_cast (Nat.le_succ m)
  have hkT : (k : ℝ) ≤ T :=
    le_mul_of_one_le_right (Nat.cast_nonneg k) (by linarith : 1 ≤ Real.log k)
  have hT1 : 1 ≤ T := hkR.trans hkT
  have hT : 0 ≤ T := zero_le_one.trans hT1
  have hTT : T ≤ T ^ 2 := by nlinarith
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_modulusLogScale _)
  have hD : 0 ≤ modulusLogScale (M * R) := zero_le_one.trans (one_le_modulusLogScale _)
  have hDΛ : modulusLogScale (M * R) ≤ Λ :=
    modulusLogScale_mono (Nat.mul_pos hM (by omega))
      (Nat.mul_le_mul_left M (by
        simpa only [pow_one] using
          Nat.pow_le_pow_right (by omega : 1 ≤ R) (by omega : 1 ≤ 2 * k)))
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hQ : 0 ≤ Q := sieveQuadraticErrorScale_nonneg _ _ _
  have hPQ : P ≤ Q := le_add_of_nonneg_right (by
    change 0 ≤ (k : ℝ) ^ 3 * T / Real.log R
    positivity)
  have hprofile : Ce * (m + 1 : ℕ) * sieveProfileScale (m + 1) *
      modulusLogScale (M * R) ^ 3 ≤ Real.log R := by
    have he : Ce * (k : ℝ) * T * modulusLogScale (M * R) ^ 3 / Real.log R ≤ Ce * P := by
      calc
        _ ≤ Ce * (k : ℝ) * T ^ 2 * Λ ^ 3 / Real.log R := by gcongr
        _ = _ := by dsimp only [P]; ring
    have h := (div_le_iff₀ hL).mp
      (he.trans ((mul_le_mul heC hPQ hP hC.le).trans htotal))
    simpa only [one_mul] using h
  have hmajorCost : (m : ℝ) * (Cm * sieveProfileScale (m + 1) ^ 2 *
      modulusLogScale (M * R ^ (2 * (m + 1))) ^ 3 / Real.log R) ≤ 1 := by
    have hmP : (m : ℝ) * (Cm * T ^ 2 * Λ ^ 3 / Real.log R) ≤ Cm * P := by
      calc
        _ ≤ (k : ℝ) * (Cm * T ^ 2 * Λ ^ 3 / Real.log R) := by gcongr
        _ = _ := by dsimp only [P]; ring
    exact hmP.trans ((mul_le_mul hmC hPQ hP hC.le).trans htotal)
  let p : commonPrimeUniverse M R → ℕ := fun q => q.val
  let A := pinnedGlobalNormalization m M p * Real.log R
  have hA : 0 < A := mul_pos
    (pinnedGlobalNormalization_pos (seven_le_of_profile_log hlog) hM hsmall
      commonPrimeUniverse_prime Subtype.val_injective commonPrimeUniverse_not_dvd) hL
  have hJ := commonFaceMainTerm_pos hm hlog hM hR hsmall
  have hraw := herror hm hlog hM hR hsmall hprofile j
  have hmajorant := hmajor (commonPrimeUniverse M R) hm hlog hM hR hsmall hmajorCost p
    commonPrimeUniverse_prime Subtype.val_injective commonPrimeUniverse_not_dvd
  have h := pinned_offDiagonal_relative_of_bounds hA hJ hCe.le (Nat.cast_nonneg m) hmk
    (Nat.cast_nonneg k) hkT (pow_nonneg hD 3) (pow_le_pow_left₀ hD hDΛ 3) hL hmajorant hraw
  calc
    _ ≤ K * Q := by
      convert h using 1
      all_goals first | rfl | (dsimp only [K, Q, sieveQuadraticErrorScale, k, T, Λ]; ring)
    _ ≤ C * Q := mul_le_mul_of_nonneg_right hKC hQ

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPinnedQuadratic_offDiagonal_relative_error
