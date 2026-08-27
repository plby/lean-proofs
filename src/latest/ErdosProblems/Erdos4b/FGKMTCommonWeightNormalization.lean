/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPreSieveNormalization
import ErdosProblems.Erdos4b.FGKMTCommonWeightInterval

/-!
# A common total-mass scale independent of the label prime

The presieve permutation and the rounding estimate replace the integer
window length by `2*y`. Arithmetic and endpoint errors stay explicit.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem preSieveIntervalDensity_eq {ι : Type*} [Fintype ι] (W : ℕ) (a : ι → ℤ)
    (A B : ℤ) : preSieveIntervalDensity W a A B = preSieveDensity W a * ((B : ℝ) - A) := by
  unfold preSieveIntervalDensity preSieveDensity
  ring

def commonWeightMassScale (k W M R : ℕ) (h : Fin k → ℕ) : ℝ :=
  preSieveDensity W (fun i => (h i : ℤ)) * commonSieveMainTerm k M R

theorem commonWeightMassScale_nonneg {k W M R : ℕ} (hk : 2 ≤ k)
    (hlog : 10000 ≤ Real.log k) (hM : 0 < M) (hR : 1 < R)
    (hsmall : ∀ q : ℕ, q.Prime → q ≤ 2 * k ^ 2 → q ∣ M) (h : Fin k → ℕ) :
    0 ≤ commonWeightMassScale k W M R h :=
  mul_nonneg (preSieveDensity_nonneg W _) (commonSieveMainTerm_pos hk hlog hM hR hsmall).le

theorem exists_commonPrimeSieveWeight_centered_totalMass_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k W M R P : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R → 0 < W → W ∣ M →
      (∀ q : ℕ, q.Prime → q ≤ 2 * k ^ 2 → q ∣ M) →
      P.Prime → R < P → P.Coprime W → ∀ h : Fin k → ℕ, Function.Injective h →
      (∀ i, h i < 2 * k ^ 2) → ∀ y : ℝ, 0 ≤ y →
      C * sieveQuadraticErrorScale k M R ≤ 1 →
      |(∑' n : ℤ, commonPrimeSieveWeight k W M R y h P n) -
        2 * y * commonWeightMassScale k W M R h| ≤
      (W : ℝ) * ((R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k)) +
        ((2 * y + 1) * (C * sieveQuadraticErrorScale k M R) + 1) *
          commonWeightMassScale k W M R h := by
  obtain ⟨C, hC, htotal⟩ := exists_commonPrimeSieveWeight_totalMass_error
  refine ⟨C, hC, ?_⟩
  intro k W M R P hk hlog hM hR hW hWM hsmall hP hRP hPW h hinj hshift y hy hsize
  let L : ℝ := ((⌊y⌋ + 1 : ℤ) : ℝ) - (⌈-y⌉ : ℝ)
  let S := commonWeightMassScale k W M R h
  let δ := C * sieveQuadraticErrorScale k M R
  have hS : 0 ≤ S := commonWeightMassScale_nonneg hk hlog hM hR hsmall h
  have hδ : 0 ≤ δ := mul_nonneg hC.le (sieveQuadraticErrorScale_nonneg k M R)
  have hL : |L - 2 * y| ≤ 1 := integerWeightWindow_length_error y
  have hLupper : L ≤ 2 * y + 1 := by linarith [(abs_le.mp hL).2]
  have hnorm :
      preSieveIntervalDensity W (fun i => (h i : ℤ) * P) ⌈-y⌉ (⌊y⌋ + 1) *
          commonSieveMainTerm k M R = L * S := by
    rw [preSieveIntervalDensity_eq, preSieveDensity_mul hW hPW]
    dsimp only [L, S, commonWeightMassScale]
    ring
  have hm := htotal hk hlog hM hR hW hWM hsmall hP hRP h hinj hshift y hy hsize
  rw [hnorm] at hm
  change |(∑' n : ℤ, commonPrimeSieveWeight k W M R y h P n) - 2 * y * S| ≤
    _ + ((2 * y + 1) * δ + 1) * S
  calc
    _ ≤ |(∑' n : ℤ, commonPrimeSieveWeight k W M R y h P n) - L * S| +
        |L * S - 2 * y * S| := abs_sub_le _ _ _
    _ ≤ ((W : ℝ) * ((R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k)) + L * S * δ) + S := by
      apply add_le_add hm
      rw [← sub_mul, abs_mul, abs_of_nonneg hS]
      exact (mul_le_mul_of_nonneg_right hL hS).trans_eq (one_mul S)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hLupper (mul_nonneg hS hδ)
      nlinarith

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPrimeSieveWeight_centered_totalMass_error
