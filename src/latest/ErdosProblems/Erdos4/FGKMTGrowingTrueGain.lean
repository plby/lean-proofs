import ErdosProblems.Erdos4.FGKMTGrowingIdealGain
import ErdosProblems.Erdos4.FGKMTGrowingWindow
import ErdosProblems.Erdos4.FGKMTWindowDensity
import ErdosProblems.Erdos4.FGKMTProjectionTail

/-! The true principal projection retains the growing-dimensional sieve gain. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter BoundedGaps.Maynard RestrictedProductNorm

theorem eventually_growing_true_gain :
    ∀ᶠ x : ℕ in atTop, ∀ a : ℝ, a ≤ 1 / 4 → ∀ B : ℕ,
      (B = 1 ∨ B.Prime) → B ≤ exponentialConductorCutoff a x →
      let j := growingIndex x
      let R := growingRadius x
      let W := harmonicModulus (growingPrecutoff x) B
      (sieveWindowDensity (sievePrimeValue W R) * coprimeHarmonicDensity W *
        Real.log (R : ℝ) * (j : ℝ) / 12288) *
          energy (rationalCoefficient (k := sieveDimension j) (sieveSlope j R) R (sievePrimeValue W R)) ≤
        ∑ i : Fin (sieveDimension j), rationalTrueForm (sieveSlope j R) R (sievePrimeValue W R) i := by
  obtain ⟨c, hc, hdensity⟩ := exists_window_density_uniform_lower
  have hdim : Tendsto (fun x => (sieveDimension (growingIndex x) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp growingDimension_tendsto
  filter_upwards [eventually_growing_ideal_gain, eventually_growing_pre_le_radius,
    eventually_growingPrecutoff_bounds, eventually_growingRadius_bounds,
    growingIndex_tendsto.eventually (eventually_ge_atTop 16),
    hdim.eventually (eventually_ge_atTop (12288 / c))]
      with x hideal hDR hD hR hj hlarge
  intro a ha B hB hBx
  let j := growingIndex x
  let R := growingRadius x
  let W := harmonicModulus (growingPrecutoff x) B
  let E := energy (rationalCoefficient (k := sieveDimension j) (sieveSlope j R) R (sievePrimeValue W R))
  let A := sieveWindowDensity (sievePrimeValue W R) * coprimeHarmonicDensity W * Real.log (R : ℝ)
  let I := ∑ i : Fin (sieveDimension j), rationalIdealForm (sieveSlope j R) R (sievePrimeValue W R) i
  let T := ∑ i : Fin (sieveDimension j), rationalTrueForm (sieveSlope j R) R (sievePrimeValue W R) i
  let e := 10 * (sieveDimension j : ℝ) ^ 3 / growingPrecutoff x
  change (A * (j : ℝ) / 12288) * E ≤ T
  have hE : 0 ≤ E := energy_nonneg _
  have hb := sieveSlope_pos (by omega : 1 ≤ j) hR.1
  have hK : 0 < growingPrecutoff x := by omega
  have hk : sieveDimension j + 1 ≤ growingPrecutoff x := by
    have hsmall : sieveDimension j + 1 ≤ 4 * (sieveDimension j + 1) ^ 2 := by nlinarith
    exact hsmall.trans (hD.2.1.trans (Nat.sub_le _ _))
  have hpre : ∀ p : ℕ, p.Prime → p ≤ growingPrecutoff x → p ∣ W :=
    fun p hp hpD => small_prime_dvd_harmonicModulus (growingPrecutoff x) B hp hpD
  have htrue : I - E * e ≤ T := rational_ideal_sum_sub_tail_le_true (R := R) hb.le hK hk hpre
  have hi : (A * (j : ℝ) / 6144) * E ≤ I := hideal a ha B hB hBx
  have hA : c ≤ A := hdensity (growingPrecutoff x) R B hDR hR.1 hB
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
  have hAj : c ≤ A * (j : ℝ) :=
    hA.trans (le_mul_of_one_le_right (hc.le.trans hA) hj1)
  have hdim0 : (0 : ℝ) < sieveDimension j := by exact_mod_cast sieveDimension_pos j
  have hrecip : 1 / (sieveDimension j : ℝ) ≤ c / 12288 := by
    have hh := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 12288 / c) hlarge
    have heq : 1 / (12288 / c) = c / 12288 := by field_simp
    rwa [heq] at hh
  have herr : e ≤ A * (j : ℝ) / 12288 :=
    (growing_projection_loss_le x).trans
      (hrecip.trans (div_le_div_of_nonneg_right hAj (by norm_num)))
  have hmul := mul_le_mul_of_nonneg_left herr hE
  calc
    _ = (A * (j : ℝ) / 6144) * E - E * (A * (j : ℝ) / 12288) := by ring
    _ ≤ I - E * e := sub_le_sub hi hmul
    _ ≤ T := htrue

end Erdos4.FGKMT
