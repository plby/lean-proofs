import ErdosProblems.Erdos248.FinalReduction
import ErdosProblems.Erdos248.TransformedEnergy

/-!
# Erdős Problem 248: a common reference mass for centered correlations

Centered prime moments need a single model mass, independent of the chosen
set of at most four primes.  The sharp diagonal energy of the original
Selberg `Y`-variable provides that model.  It is nonnegative and is at most
four times the actual sieve mass, by the quantitative normalization lower
bound.
-/

noncomputable section

namespace Erdos248

/-- The common main term used when centering prime-divisibility events. -/
def sieveReferenceMass (K : ℕ) : ℝ :=
  (intervalStart K : ℝ) / preSieveModulus K *
    varyingYEnergy K (sieveY K)

theorem sieveReferenceMass_nonneg (K : ℕ) :
    0 ≤ sieveReferenceMass K := by
  unfold sieveReferenceMass
  positivity

theorem sieveReferenceMass_le_scaledProductEnergy (K : ℕ) :
    sieveReferenceMass K ≤
      (intervalStart K : ℝ) / preSieveModulus K *
        productCoordinateEnergy K := by
  unfold sieveReferenceMass
  exact mul_le_mul_of_nonneg_left (varyingYEnergy_sieveY_le K) (by positivity)

theorem sieveReferenceMass_lt_four_sieveMass
    {A : ℝ} (hA : HasUniformWirsingBound A)
    {K : ℕ} (hreg : NormalizationRegular A K) :
    sieveReferenceMass K < 4 * sieveMass K := by
  have hlower := quarter_scaled_energy_lt_sieveMass hA hreg
  have href := sieveReferenceMass_le_scaledProductEnergy K
  calc
    sieveReferenceMass K ≤
        (intervalStart K : ℝ) / preSieveModulus K *
          productCoordinateEnergy K := href
    _ < 4 * sieveMass K := by nlinarith

end Erdos248
