import ErdosProblems.Erdos248.LargeRangeMoment

/-!
# Erdős Problem 248: the uniform large-prime tail

The fourth-moment estimates for the near and far large-prime ranges have the
same absolute constant.  We choose one centered distance and then one natural
raw threshold beyond both that distance and the uniform reciprocal-prime
mean.  Markov's inequality then supplies the summable `1 / (16 k²)` tail in
both ranges.
-/

noncomputable section

open scoped BigOperators

namespace Erdos248

/-- A single natural threshold controls the large-prime exceptional mass for
every admissible sieve scale and every shift up to `intervalExponent K`. -/
theorem exists_uniform_largePrimeBadMass_tail :
    ∃ T : ℕ, ∀ {A : ℝ}, HasUniformWirsingBound A →
      ∀ {K : ℕ}, NormalizationRegular A K →
        ∀ k, 1 ≤ k → k ≤ intervalExponent K →
          largePrimeBadMass K T k ≤
            sieveMass K * (1 / (16 * (k : ℝ) ^ 2)) := by
  obtain ⟨D, hDnat, -, hDfour⟩ :=
    exists_natural_moment_threshold largePrimeFourthMomentConstant
      largePrimeFourthMomentConstant_pos
  obtain ⟨T : ℕ, hT⟩ := exists_nat_gt
    (largePrimeUniformReciprocalConstant + (D : ℝ))
  refine ⟨T, ?_⟩
  intro A hA K hreg k hk1 hkmax
  have hD : (0 : ℝ) < D := by exact_mod_cast hDnat
  have hBT : largePrimeUniformReciprocalConstant + (D : ℝ) ≤ (T : ℝ) :=
    hT.le
  have hmass : 0 ≤ sieveMass K := (sieveMass_pos hA hreg).le
  by_cases hkK : k ≤ K
  · apply largePrimeBadMass_le_sixteenth_of_centeredMoment
      (I := largePrimes K k) hk1 hD hBT
    · exact (sum_largePrimes_inv_le hk1 hkK).trans (by
        exact mul_le_mul_of_nonneg_right
          largePrimeReciprocalConstant_le_uniform (by positivity))
    · intro n hn
      exact largePrimeCount_cast_eq_largeIndicatorSum hkK (by omega)
    · exact hmass
    · exact hDfour
    · exact nearLargePrimeCenteredFourthMoment_le hA hreg hk1 hkK
  · have hKk : K < k := lt_of_not_ge hkK
    apply largePrimeBadMass_le_sixteenth_of_centeredMoment
      (I := farPrimes K k) hk1 hD hBT
    · exact (sum_farPrimes_inv_le hreg.1 hKk.le).trans (by
        exact mul_le_mul_of_nonneg_right
          farPrimeReciprocalConstant_le_uniform (by positivity))
    · intro n hn
      exact largePrimeCount_cast_eq_farIndicatorSum hKk (by omega)
    · exact hmass
    · exact hDfour
    · exact farLargePrimeCenteredFourthMoment_le hA hreg hKk

end Erdos248
