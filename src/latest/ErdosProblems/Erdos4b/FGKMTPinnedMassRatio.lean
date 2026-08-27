/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTLastCoordinateConstant
import ErdosProblems.Erdos4b.FGKMTPinnedQuadraticMean

/-!
# Exact finite pinned-to-total normalization and its logarithmic gain

The finite pinned Euler factor is kept in the common scalar. Its bounds
are uniform, so a sharper Euler-tail approximation is not needed for
the weight interface. Neither the coefficients nor the weight change.
-/

namespace Erdos4b.FGKMT

noncomputable section

def commonPinnedDensityRatio (m M R : ℕ) : ℝ :=
  pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M R => q.val) /
    ((M.totient : ℝ) / M)

def commonPinnedVariationalGain (m M R : ℕ) : ℝ :=
  commonPinnedDensityRatio m M R ^ 2 *
    ((m + 1 : ℕ) * dimensionFaceEnergy (m + 1) m /
      dimensionProfileEnergy (m + 1) (m + 1))

theorem commonPinnedDensityRatio_bounds {m M R : ℕ} (hm : 7 ≤ m) (hM : 0 < M)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) :
    (1 / 2 : ℝ) ≤ commonPinnedDensityRatio m M R ∧
      commonPinnedDensityRatio m M R ≤ Real.exp 12 := by
  have hb : (0 : ℝ) < (M.totient : ℝ) / M :=
    div_pos (by exact_mod_cast Nat.totient_pos.mpr hM) (by exact_mod_cast hM)
  have h := pinnedGlobalNormalization_bounds hm hM hsmall
    (p := fun q : commonPrimeUniverse M R => q.val)
    commonPrimeUniverse_prime Subtype.val_injective commonPrimeUniverse_not_dvd
  constructor
  · apply (le_div_iff₀ hb).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using h.1
  · exact (div_le_iff₀ hb).mpr h.2

theorem commonPinnedDensityRatio_sq_bounds {m M R : ℕ} (hm : 7 ≤ m) (hM : 0 < M)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) :
    (1 / 4 : ℝ) ≤ commonPinnedDensityRatio m M R ^ 2 ∧
      commonPinnedDensityRatio m M R ^ 2 ≤ Real.exp 24 := by
  have h := commonPinnedDensityRatio_bounds (R := R) hm hM hsmall
  have hnon : 0 ≤ commonPinnedDensityRatio m M R := by linarith
  constructor
  · nlinarith
  · have he : Real.exp 12 ^ 2 = Real.exp 24 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    exact (pow_le_pow_left₀ hnon h.2 2).trans_eq he

theorem commonPinnedMainTerm_div_total {m M R : ℕ} (hm : 1 ≤ m)
    (hlog : 10000 ≤ Real.log (m + 1 : ℕ)) (hM : 0 < M) (hR : 1 < R)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) :
    commonPinnedMainTerm m M R / commonSieveMainTerm (m + 1) M R =
      ((M.totient : ℝ) / M) * commonPinnedDensityRatio m M R ^ 2 * Real.log R *
        (dimensionFaceEnergy (m + 1) m / dimensionProfileEnergy (m + 1) (m + 1)) := by
  have hb : (0 : ℝ) < (M.totient : ℝ) / M :=
    div_pos (by exact_mod_cast Nat.totient_pos.mpr hM) (by exact_mod_cast hM)
  have hP := multivariateSieveConstant_pos (k := m + 1) (by omega) hM
    (fun p hp hpk => hsmall p hp (by omega)) _
    (actualSieveDenominator_chain (by omega) (by omega : m ≤ m + 1) hsmall false)
  have hI := dimensionProfileEnergy_pos (Nat.succ_pos m) hlog (le_refl (m + 1))
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  unfold commonPinnedMainTerm commonSieveMainTerm commonFaceMainTerm commonPinnedDensityRatio
  rw [actual_multivariateSieveConstant_last_coordinate m hM, pow_succ]
  field_simp [hb.ne', hP.ne', hI.ne', hL.ne']
  ring

theorem commonPinnedVariationalGain_bounds {m M R : ℕ} (hm : 1 ≤ m)
    (hlog : 10000 ≤ Real.log (m + 1 : ℕ)) (hM : 0 < M)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) :
    Real.log (m + 1 : ℕ) / 64 ≤ commonPinnedVariationalGain m M R ∧
      commonPinnedVariationalGain m M R ≤ 6 * Real.exp 24 * Real.log (m + 1 : ℕ) := by
  have hk : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have htheta := commonPinnedDensityRatio_sq_bounds (R := R)
    (seven_le_of_profile_log hlog) hM hsmall
  have hratio := dimensionProfile_variational_ratio_bounds (Nat.succ_pos m) hlog
  have hdim : m + 1 - 1 = m := by omega
  simp only [Nat.succ_eq_add_one, hdim] at hratio
  let V := (m + 1 : ℕ) * dimensionFaceEnergy (m + 1) m /
    dimensionProfileEnergy (m + 1) (m + 1)
  have hVlo : Real.log (m + 1 : ℕ) / 16 ≤ V := by
    simpa only [V, Nat.succ_eq_add_one, hdim] using
      dimensionProfile_variational_gain (Nat.succ_pos m) hlog
  have hVhi : V ≤ 6 * Real.log (m + 1 : ℕ) := by
    calc
      _ = (m + 1 : ℕ) * (dimensionFaceEnergy (m + 1) m /
          dimensionProfileEnergy (m + 1) (m + 1)) := by dsimp only [V]; ring
      _ ≤ (m + 1 : ℕ) * (6 * Real.log (m + 1 : ℕ) / (m + 1 : ℕ)) :=
        mul_le_mul_of_nonneg_left hratio.2 hk.le
      _ = _ := by field_simp
  have hlog0 : 0 ≤ Real.log (m + 1 : ℕ) := by linarith
  have hV0 : 0 ≤ V := (div_nonneg hlog0 (by norm_num)).trans hVlo
  constructor
  · calc
      _ = (1 / 4 : ℝ) * (Real.log (m + 1 : ℕ) / 16) := by ring
      _ ≤ commonPinnedDensityRatio m M R ^ 2 * V :=
        mul_le_mul htheta.1 hVlo (by positivity) (sq_nonneg _)
      _ = _ := rfl
  · calc
      _ ≤ Real.exp 24 * (6 * Real.log (m + 1 : ℕ)) :=
        mul_le_mul htheta.2 hVhi hV0 (Real.exp_pos _).le
      _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedMainTerm_div_total
#print axioms Erdos4b.FGKMT.commonPinnedVariationalGain_bounds
