import ErdosProblems.Erdos964.ScalarRadical
import ErdosProblems.Erdos964.AffineNormalization

/-!
# Totient-density cancellation for normalized affine leading coefficients
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem coprimeHarmonicDensity_mul_of_dvd (a M : ℕ) (ha : 0 < a) (hM : 0 < M)
    (haM : a ∣ M) : coprimeHarmonicDensity (a * M) = coprimeHarmonicDensity M := by
  unfold coprimeHarmonicDensity
  rw [totient_density_eq_prime_product _ (Nat.mul_pos ha hM),
    totient_density_eq_prime_product M hM, Nat.primeFactors_mul ha.ne' hM.ne',
    Finset.union_eq_right.mpr (Nat.primeFactors_mono haM hM.ne')]

theorem normalized_totient_density_cancel (a M : ℕ) (ha : 0 < a) (hM : 0 < M)
    (haM : a ∣ M) :
    ((a * M : ℕ) : ℝ) / (a * M).totient * coprimeHarmonicDensity M = 1 := by
  rw [← coprimeHarmonicDensity_mul_of_dvd a M ha hM haM]
  unfold coprimeHarmonicDensity
  have hm : ((a * M : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos ha hM).ne'
  have hφ : ((a * M).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos ha hM)).ne'
  field_simp

theorem normalized_affine_totient_density_cancel (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i) (i : Fin 3) :
    ((A i * affineNormalizationModulus A B : ℕ) : ℝ) /
      (A i * affineNormalizationModulus A B).totient *
        coprimeHarmonicDensity (affineNormalizationModulus A B) = 1 :=
  normalized_totient_density_cancel _ _ (hA i) (affineNormalizationModulus_pos A B hA hne)
    (affine_leading_dvd_normalization A B i)

end Erdos964
