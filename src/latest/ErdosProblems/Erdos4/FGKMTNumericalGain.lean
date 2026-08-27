import ErdosProblems.Erdos4.FGKMTProfileGain
import ErdosProblems.Erdos4.FGKMTFaceRadius
import ErdosProblems.Erdos4.FGKMTPrimeLabels

/-! A concrete gain proportional to the logarithm of the sieve dimension. -/

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

theorem coprimeHarmonicDensity_pos {W : ℕ} (hW : 0 < W) : 0 < coprimeHarmonicDensity W := by
  unfold coprimeHarmonicDensity
  exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) (by exact_mod_cast hW)

theorem profile_mass_ratio_lower {ρ b u v M A : ℝ}
    (hρ : 0 < ρ) (hb : 0 < b) (hu : 0 ≤ u) (hv : 0 ≤ v) (hM : 0 < M)
    (hA : ρ * u / (4 * b) ≤ A) (hMup : M ≤ 3 * ρ / (2 * b)) :
    v * ρ * u ^ 2 / (48 * b) ≤ v * A ^ 2 / (2 * M) := by
  have hsmall : 0 ≤ ρ * u / (4 * b) := by positivity
  have hsq := pow_le_pow_left₀ hsmall hA 2
  have hden : 2 * M ≤ 3 * ρ / b := by
    calc
      _ ≤ 2 * (3 * ρ / (2 * b)) := mul_le_mul_of_nonneg_left hMup (by norm_num)
      _ = _ := by ring
  calc
    _ = v * (ρ * u / (4 * b)) ^ 2 / (3 * ρ / b) := by field_simp; ring
    _ ≤ v * (ρ * u / (4 * b)) ^ 2 / (2 * M) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hv) (by positivity)

theorem rationalMass_sieve_ratio_lower {W R j : ℕ} (hW : 0 < W) (hSq : Squarefree W)
    (hR : 16 ≤ R) (hj : 16 ≤ j)
    (hE : harmonicTransferError W ≤ coprimeHarmonicDensity W * Real.log (R : ℝ) /
      (2 * (1 + sieveProfileScale j))) :
    coprimeHarmonicDensity W * Real.log (R : ℝ) * (j : ℝ) / 6144 ≤
      (sieveDimension j : ℝ) * rationalMass W (sieveSlope j R) (sieveFaceRadius R) ^ 2 /
        (2 * rationalSquareMass W (sieveSlope j R) R) := by
  have hR2 : 2 ≤ R := by omega
  have hb := sieveSlope_pos (by omega : 1 ≤ j) hR2
  have hρ := coprimeHarmonicDensity_pos hW
  have hL : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR2)
  have hE' : harmonicTransferError W ≤ coprimeHarmonicDensity W / (2 * sieveSlope j R) := by
    apply harmonic_error_le_density_over_slope hρ.le hb hL.le
    simpa only [sieveSlope_mul_log hR2] using hE
  have hT : 1 ≤ sieveFaceRadius R := (by norm_num : 1 ≤ 4).trans (sieveFaceRadius_ge_four hR)
  have hA := rationalMass_face_lower hW hSq hR2 hT (by omega : 2 ≤ j)
    (sieveFaceRadius_log_lower hR) hE'
  have hMup := rationalSquareMass_slope_upper hW hSq (by omega : 1 ≤ R) hb hE'
  have hM := zero_lt_one.trans_le (one_le_rationalSquareMass W (sieveSlope j R) (by omega : 1 ≤ R))
  have hh := profile_mass_ratio_lower hρ hb (Nat.cast_nonneg j)
    (Nat.cast_nonneg (sieveDimension j)) hM hA hMup
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hk0 : (sieveDimension j : ℝ) ≠ 0 := by exact_mod_cast (sieveDimension_pos j).ne'
  have heq : (sieveDimension j : ℝ) * coprimeHarmonicDensity W * (j : ℝ) ^ 2 /
      (48 * sieveSlope j R) = coprimeHarmonicDensity W * Real.log (R : ℝ) * (j : ℝ) / 6144 := by
    unfold sieveSlope sieveProfileScale
    field_simp
    ring
  rwa [heq] at hh

theorem rationalSieve_dimension_gain {W R K j : ℕ}
    (hW : 0 < W) (hSq : Squarefree W) (hR : 16 ≤ R) (hj : 16 ≤ j) (hK : 2 ≤ K)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W)
    (hcollision : 4 * (sieveDimension j + 1) ^ 2 ≤ K - 1)
    (hE : harmonicTransferError W ≤ coprimeHarmonicDensity W * Real.log (R : ℝ) /
      (2 * (1 + sieveProfileScale j))) :
    (sieveWindowDensity (sievePrimeValue W R) * coprimeHarmonicDensity W *
      Real.log (R : ℝ) * (j : ℝ) / 6144) *
        RestrictedProductNorm.energy
          (rationalCoefficient (k := sieveDimension j) (sieveSlope j R) R (sievePrimeValue W R)) ≤
      ∑ i : Fin (sieveDimension j), rationalIdealForm (sieveSlope j R) R (sievePrimeValue W R) i := by
  have hR2 : 2 ≤ R := by omega
  have hb := sieveSlope_pos (by omega : 1 ≤ j) hR2
  have hT : 1 ≤ sieveFaceRadius R := (by norm_num : 1 ≤ 4).trans (sieveFaceRadius_ge_four hR)
  have hmean : (sieveDimension j : ℝ) * rationalMass W (sieveSlope j R) R ≤
      (1 / 4) * (sieveSlope j R * rationalSquareMass W (sieveSlope j R) R * (Real.log (R : ℝ) / 2)) := by
    apply rationalMass_moment_budget hW hSq hR2 hb
    · rw [sieveSlope_mul_log hR2]
      exact sieveProfileScale_ge_one (by omega)
    · simpa only [sieveSlope_mul_log hR2] using hE
    · simpa only [sieveSlope_mul_log hR2] using sieveProfileScale_moment_budget hj
  have hsum := rationalSieve_sum_ideal_gain hb hR2 hT (sieveFaceRadius_sq_le R) hK hpre hmean hcollision
  have hratio := rationalMass_sieve_ratio_lower hW hSq hR hj hE
  have hδ := sieveWindowDensity_nonneg (sievePrimeValue W R) (fun p => (sievePrimeValue_prime W R p).one_le)
  have henergy := RestrictedProductNorm.energy_nonneg
    (rationalCoefficient (k := sieveDimension j) (sieveSlope j R) R (sievePrimeValue W R))
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hδ) henergy
  have hleft : sieveWindowDensity (sievePrimeValue W R) *
      (coprimeHarmonicDensity W * Real.log (R : ℝ) * (j : ℝ) / 6144) =
      sieveWindowDensity (sievePrimeValue W R) * coprimeHarmonicDensity W *
        Real.log (R : ℝ) * (j : ℝ) / 6144 := by ring
  have hright : sieveWindowDensity (sievePrimeValue W R) *
      ((sieveDimension j : ℝ) * rationalMass W (sieveSlope j R) (sieveFaceRadius R) ^ 2 /
        (2 * rationalSquareMass W (sieveSlope j R) R)) =
      (sieveDimension j : ℝ) * (sieveWindowDensity (sievePrimeValue W R) *
        rationalMass W (sieveSlope j R) (sieveFaceRadius R) ^ 2 /
          (2 * rationalSquareMass W (sieveSlope j R) R)) := by ring
  rw [hleft, hright] at hh
  exact hh.trans hsum

end Erdos4.FGKMT
