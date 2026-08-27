import ErdosProblems.Erdos4.FGKMTNumericalGain
import ErdosProblems.Erdos4.FGKMTGrowingDivisorLaw

/-!
The growing-dimensional ideal gain is proved for every sufficiently large
natural endpoint, uniformly in the excised prime. No unproved sieve-profile
or prime-factor-coverage hypotheses remain.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter BoundedGaps.Maynard

theorem eventually_growing_ideal_gain :
    ∀ᶠ x : ℕ in atTop, ∀ a : ℝ, a ≤ 1 / 4 → ∀ B : ℕ,
      (B = 1 ∨ B.Prime) → B ≤ exponentialConductorCutoff a x →
      let j := growingIndex x
      let R := growingRadius x
      let W := harmonicModulus (growingPrecutoff x) B
      (sieveWindowDensity (sievePrimeValue W R) * coprimeHarmonicDensity W *
        Real.log (R : ℝ) * (j : ℝ) / 6144) *
          RestrictedProductNorm.energy
            (rationalCoefficient (k := sieveDimension j) (sieveSlope j R) R (sievePrimeValue W R)) ≤
        ∑ i : Fin (sieveDimension j), rationalIdealForm (sieveSlope j R) R (sievePrimeValue W R) i := by
  have hlogTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpow : Tendsto (fun x : ℕ => (x : ℝ) ^ (1 / 50 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 50)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_sieve_harmonic_error, eventually_growingRadius_bounds,
    eventually_growingPrecutoff_bounds, eventually_growingDimension_bounds,
    growingIndex_tendsto.eventually (eventually_ge_atTop 16),
    hlogTop.eventually (eventually_ge_atTop 1), hpow.eventually (eventually_ge_atTop 16)]
      with x herror hR hD hk hj hlog hlarge
  have hR16 : 16 ≤ growingRadius x := Nat.le_floor hlarge
  intro a ha B hB hBx
  have hkupper : (sieveDimension (growingIndex x) : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 16 : ℝ) :=
    hk.2.trans (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num))
  have he := herror (growingIndex x) (growingRadius x) (growingPrecutoff x) B a
    hj hR.1 hD.1 ha hkupper hD.2.2 hR.2 hB hBx
  exact rationalSieve_dimension_gain (harmonicModulus_pos (growingPrecutoff x) hB)
    (harmonicModulus_squarefree (growingPrecutoff x) hB) hR16 hj hD.1
    (fun p hp hpD => small_prime_dvd_harmonicModulus (growingPrecutoff x) B hp hpD) hD.2.1 he

end Erdos4.FGKMT
