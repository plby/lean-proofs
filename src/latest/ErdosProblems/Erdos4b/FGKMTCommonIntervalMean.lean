/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCommonIntervalMass
import ErdosProblems.Erdos4b.FGKMTCommonQuadraticMean

/-!
# Uniform physical interval mean with explicit arithmetic and endpoint errors

The actual presieved integer sum is now compared with the profile energy.
The two errors remain separate: the relative arithmetic error and the
absolute endpoint envelope. No prime-distribution hypothesis is added.
-/

namespace Erdos4b.FGKMT

noncomputable section

def preSieveIntervalDensity {ι : Type*} [Fintype ι] (W : ℕ) (a : ι → ℤ)
    (A B : ℤ) : ℝ := ((preSieveResidues W a).card : ℝ) * ((B : ℝ) - A) / W

theorem preSieveIntervalDensity_nonneg {ι : Type*} [Fintype ι] (W : ℕ) (a : ι → ℤ)
    {A B : ℤ} (hAB : A ≤ B) : 0 ≤ preSieveIntervalDensity W a A B := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hAB)))
    (Nat.cast_nonneg W)

theorem exists_commonPrimePreSieveIntervalMass_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k W M R P : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R → 0 < W → W ∣ M →
      (∀ q : ℕ, q.Prime → q ≤ 2 * k ^ 2 → q ∣ M) →
      P.Prime → R < P → ∀ h : Fin k → ℕ, Function.Injective h →
      (∀ i, h i < 2 * k ^ 2) → ∀ A B : ℤ, A ≤ B →
      C * sieveQuadraticErrorScale k M R ≤ 1 →
      |commonPreSieveIntervalMass k W R (fun q : commonPrimeUniverse M R => q.val)
          (fun i => (h i : ℤ) * P) A B -
        preSieveIntervalDensity W (fun i => (h i : ℤ) * P) A B * commonSieveMainTerm k M R| ≤
      (W : ℝ) * ((R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k)) +
        (preSieveIntervalDensity W (fun i => (h i : ℤ) * P) A B * commonSieveMainTerm k M R) *
          (C * sieveQuadraticErrorScale k M R) := by
  obtain ⟨C, hC, hquad⟩ := exists_commonSieveQuadratic_relative_error
  refine ⟨C, hC, ?_⟩
  intro k W M R P hk hlog hM hR hW hWM hsmall hP hRP h hinj hshift A B hAB hsize
  let D := preSieveIntervalDensity W (fun i => (h i : ℤ) * P) A B
  have hD : 0 ≤ D := preSieveIntervalDensity_nonneg W _ hAB
  have hmain := commonSieveMainTerm_pos hk hlog hM hR hsmall
  have hq := (div_le_iff₀ hmain).mp (hquad hk hlog hM hR hsmall hsize)
  have hendpoint := commonPrimePreSieveIntervalMass_quadratic_error
    hk hR hW hWM hsmall hP hRP h hinj hshift A B hAB
  change |commonPreSieveIntervalMass k W R _ _ A B - D * commonSieveQuadratic k M R| ≤ _
    at hendpoint
  change |commonPreSieveIntervalMass k W R _ _ A B - D * commonSieveMainTerm k M R| ≤
    _ + (D * commonSieveMainTerm k M R) * (C * sieveQuadraticErrorScale k M R)
  calc
    _ ≤ |commonPreSieveIntervalMass k W R _ _ A B - D * commonSieveQuadratic k M R| +
        |D * commonSieveQuadratic k M R - D * commonSieveMainTerm k M R| := abs_sub_le _ _ _
    _ ≤ (W : ℝ) * ((R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k)) +
        D * ((C * sieveQuadraticErrorScale k M R) * commonSieveMainTerm k M R) := by
      apply add_le_add hendpoint
      rw [← mul_sub, abs_mul, abs_of_nonneg hD]
      exact mul_le_mul_of_nonneg_left hq hD
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPrimePreSieveIntervalMass_error
