/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedMassRatio
import ErdosProblems.Erdos4b.FGKMTPrimePreSieveNormalization
import ErdosProblems.Erdos4b.FGKMTPreSieveAdmissible

/-!
# Finite lower bounds for the actual pinned main term

The signed main constants retain at least one totient density per
coordinate. No asymptotic replacement of the common normalization is used.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem totientDensity_pow_le_actual_multivariate {k M j : ℕ}
    (hk : 2 ≤ k) (hM : 0 < M) (hj : j ≤ k)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) :
    ((M.totient : ℝ) / M) ^ j ≤
      multivariateSieveConstant M (actualSieveDenominator false k) j := by
  calc
    _ = ∏ _s ∈ Finset.range j, ((M.totient : ℝ) / M) := by simp [div_pow]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro s _
        positivity
      · intro s hs
        simpa only [actualSieveDenominator, Bool.false_eq_true, if_false] using
          (shiftedDenominator_mainConstant_bounds hk hM
            ((Finset.mem_range.mp hs).trans_le hj) hsmall).1

theorem dimensionFaceEnergy_explicit_lower {k j : ℕ}
    (hk : 0 < k) (hlog : 10000 ≤ Real.log k) (hj : j ≤ k) :
    (1 / (2 * (k : ℝ))) ^ 2 * (1 / (2 * sieveProfileScale k)) ^ j / 4 ≤
      dimensionFaceEnergy k j := by
  have hT : 0 < sieveProfileScale k := zero_lt_one.trans_le (profile_scales_bounds hk hlog).1
  have hfirst := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (2 * (k : ℝ)))
    (dimensionProfileFirstMass_bounds hk hlog).1 2
  have hmass := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (2 * sieveProfileScale k))
    (dimensionProfileMass_ge_half_inv hk hlog) j
  exact (div_le_div_of_nonneg_right (mul_le_mul hfirst hmass (by positivity) (sq_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 4)).trans (dimensionFaceEnergy_bounds hk hlog hj).1

theorem commonPinnedMainTerm_explicit_lower {m M R : ℕ}
    (hm : 1 ≤ m) (hlog : 10000 ≤ Real.log (m + 1 : ℕ)) (hM : 0 < M)
    (hR : 1 ≤ Real.log (R : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) :
    (((M.totient : ℝ) / M) / 2) ^ 2 * ((M.totient : ℝ) / M) ^ m *
        ((1 / (2 * (m + 1 : ℕ))) ^ 2 * (1 / (2 * sieveProfileScale (m + 1))) ^ m / 4) ≤
      commonPinnedMainTerm m M R := by
  let b : ℝ := (M.totient : ℝ) / M
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hnorm := (pinnedGlobalNormalization_bounds (seven_le_of_profile_log hlog) hM hsmall
    (p := fun q : commonPrimeUniverse M R => q.val)
    commonPrimeUniverse_prime Subtype.val_injective commonPrimeUniverse_not_dvd).1
  have hnorm0 : 0 ≤ pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M R => q.val) :=
    (div_nonneg hb (by norm_num)).trans hnorm
  have hnormL : b / 2 ≤
      pinnedGlobalNormalization m M (fun q : commonPrimeUniverse M R => q.val) * Real.log R := by
    exact hnorm.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hR hnorm0)
  have hnormSq := pow_le_pow_left₀ (div_nonneg hb (by norm_num)) hnormL 2
  have hP := totientDensity_pow_le_actual_multivariate (by omega : 2 ≤ m + 1) hM
    (by omega : m ≤ m + 1) hsmall
  have hP0 : 0 ≤ multivariateSieveConstant M (actualSieveDenominator false (m + 1)) m :=
    (pow_nonneg hb m).trans hP
  have hLpow : 1 ≤ Real.log (R : ℝ) ^ m := one_le_pow₀ hR
  have hPL : b ^ m ≤
      multivariateSieveConstant M (actualSieveDenominator false (m + 1)) m * Real.log R ^ m :=
    hP.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hLpow hP0)
  have hJ := dimensionFaceEnergy_explicit_lower (Nat.succ_pos m) hlog (by omega : m ≤ m + 1)
  have hJ0 : 0 ≤ (1 / (2 * (m + 1 : ℕ))) ^ 2 *
      (1 / (2 * sieveProfileScale (m + 1))) ^ m / 4 := by
    have hT := (profile_scales_bounds (Nat.succ_pos m) hlog).1
    positivity
  have hface0 : 0 ≤ commonFaceMainTerm m M R := by
    dsimp [commonFaceMainTerm]
    exact mul_nonneg (mul_nonneg hP0 (pow_nonneg (by linarith) _))
      (hJ0.trans hJ)
  have hface := mul_le_mul hPL hJ hJ0 (mul_nonneg hP0 (pow_nonneg (by linarith) _))
  calc
    _ = (b / 2) ^ 2 * (b ^ m *
        ((1 / (2 * (m + 1 : ℕ))) ^ 2 * (1 / (2 * sieveProfileScale (m + 1))) ^ m / 4)) := by
      dsimp [b]
      ring
    _ ≤ _ := mul_le_mul hnormSq hface (mul_nonneg (pow_nonneg hb _) hJ0) (sq_nonneg _)

theorem primePreSieveDensity_ge_inv_of_witness {ι : Type*} [Fintype ι]
    {W Q : ℕ} (hW : 0 < W) (hQ : Q.Coprime W) (a : ι → ℤ) (j : ι)
    {n : ℤ} (hn : preSieveCondition W a n) :
    1 / (W : ℝ) ≤ primePreSieveDensity W Q a j := by
  have hphi0 : (0 : ℝ) < W.totient := by exact_mod_cast Nat.totient_pos.mpr hW
  have hphiW : (W.totient : ℝ) ≤ W := by exact_mod_cast Nat.totient_le W
  have hratio : 1 ≤ (W : ℝ) / W.totient := (one_le_div hphi0).mpr hphiW
  rw [primePreSieveDensity_eq hW hQ a j]
  calc
    _ = 1 * (1 / (W : ℝ)) := by ring
    _ ≤ _ := mul_le_mul hratio (preSieveDensity_ge_inv_of_witness hW a hn)
      (by positivity) (by positivity)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedMainTerm_explicit_lower
#print axioms Erdos4b.FGKMT.primePreSieveDensity_ge_inv_of_witness
