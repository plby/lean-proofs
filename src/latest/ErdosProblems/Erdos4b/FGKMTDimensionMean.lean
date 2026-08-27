/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTDimensionEnergy
import ErdosProblems.Erdos4b.FGKMTProfileMean

/-!
# Relative summation error on the true profile energy

The denominator is the genuine positive coupled energy, rather than
its tensor majorant. The scale and moment hypotheses are proved for
the chosen dimension-dependent profile.
-/

namespace Erdos4b.FGKMT

noncomputable section

private theorem relative_error_on_energy {N P L A I ε : ℝ} {j : ℕ}
    (hP : 0 < P) (hL : 0 < L) (hA : 0 < A) (hI : A ^ j / 3 ≤ I) (hε : 0 ≤ ε)
    (herror : |N - P * L ^ j * I| / (P * (L * A) ^ j) ≤ ε) :
    |N - P * L ^ j * I| / (P * L ^ j * I) ≤ 3 * ε := by
  have hI0 : 0 < I := lt_of_lt_of_le (by positivity) hI
  have hmain : 0 < P * L ^ j * I := by positivity
  have htensor : 0 < P * (L * A) ^ j := by positivity
  have hcomp : P * (L * A) ^ j ≤ 3 * (P * L ^ j * I) := by
    have hi : A ^ j ≤ I * 3 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mp hI
    calc
      _ = (P * L ^ j) * A ^ j := by rw [mul_pow]; ring
      _ ≤ (P * L ^ j) * (I * 3) := mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by ring
  apply (div_le_iff₀ hmain).mpr
  calc
    _ ≤ ε * (P * (L * A) ^ j) := (div_le_iff₀ htensor).mp herror
    _ ≤ ε * (3 * (P * L ^ j * I)) := mul_le_mul_of_nonneg_left hcomp hε
    _ = _ := by ring

theorem exists_dimensionProfile_energy_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R → j ≤ k →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) → ∀ pinned : Bool,
      (j : ℝ) *
        (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) ≤ 1 →
      |cutoffSieveSum M (actualSieveDenominator pinned k) R j
          (fun t => dimensionProfileFactor k t ^ 2) (fun t => sieveCutoff t ^ 2) 0 -
        multivariateSieveConstant M (actualSieveDenominator pinned k) j * Real.log R ^ j *
          dimensionProfileEnergy k j| /
        (multivariateSieveConstant M (actualSieveDenominator pinned k) j * Real.log R ^ j *
          dimensionProfileEnergy k j) ≤
        (j : ℝ) *
          (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ k) ^ 3 / Real.log R) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_sieveProfile_relative_error
  refine ⟨3 * C₀, by positivity, ?_⟩
  intro k M R j hk hlog hM hR hj hsmall pinned htotal
  have hk0 : 0 < k := by omega
  have hb := profile_scales_bounds hk0 hlog
  let P := multivariateSieveConstant M (actualSieveDenominator pinned k) j
  let L := Real.log R
  let ε₀ : ℝ := C₀ * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ k) ^ 3 / L
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hR)
  have hscale : 0 ≤ modulusLogScale (M * R ^ k) :=
    zero_le_one.trans (one_le_modulusLogScale _)
  have hε₀ : 0 ≤ ε₀ := by dsimp only [ε₀]; positivity
  have htotal₀ : (j : ℝ) * ε₀ ≤ 1 := by
    have heq : 3 * C₀ * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ k) ^ 3 /
        Real.log R = 3 * ε₀ := by dsimp only [ε₀, L]; ring
    rw [heq] at htotal
    nlinarith
  have hP : 0 < P := multivariateSieveConstant_pos hk0 hM
    (fun p hp hpk => hsmall p hp (by omega)) _
    (actualSieveDenominator_chain hk hj hsmall pinned)
  have h := hbound hk hM hR hj hsmall pinned hb.1 hb.2.1
    (by linarith [hb.2.2.1]) (by linarith [hb.2.2.2]) htotal₀
  have hrelative := relative_error_on_energy hP hL (dimensionProfileMass_pos hk0 hlog)
    (dimensionProfileEnergy_bounds hk0 hlog hj).1
    (mul_nonneg (Nat.cast_nonneg j) hε₀) h
  dsimp only [ε₀, L, P, dimensionProfileFactor] at hrelative ⊢
  convert hrelative using 1 <;> ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_dimensionProfile_energy_relative_error
