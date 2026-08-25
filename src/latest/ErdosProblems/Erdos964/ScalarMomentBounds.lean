import ErdosProblems.Erdos964.ScalarWeightedMoments

/-!
# Positivity and growth bounds for the scalar moments

These bounds control errors in the transformed kernel and the exclusion
of divisors containing the distinguished prime.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem scalarMomentAF_nonneg (M k n : ℕ) (h2M : 2 ∣ M) (h3M : 3 ∣ M) :
    0 ≤ scalarMomentAF M k n := by
  rw [scalarMomentAF_apply]
  split_ifs with hn
  · apply Finset.prod_nonneg
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpc := hn.2.of_dvd_left (Nat.dvd_of_mem_primeFactors hp)
    have hpM := hprime.coprime_iff_not_dvd.mp hpc
    have hp2 : p ≠ 2 := fun h => hpM (h ▸ h2M)
    have hp3 : p ≠ 3 := fun h => hpM (h ▸ h3M)
    have hp4 : (4 : ℝ) ≤ p := by
      exact_mod_cast (show 4 ≤ p by have := hprime.two_le; omega)
    exact div_nonneg (Nat.cast_nonneg k) (by linarith)
  · exact le_rfl

theorem scalarMomentAF_two_prime_le (M : ℕ) (h2M : 2 ∣ M) (h3M : 3 ∣ M)
    {p : ℕ} (hp : p.Prime) : scalarMomentAF M 2 p ≤ 8 / (p : ℝ) := by
  rw [scalarMomentAF_prime M 2 hp]
  split_ifs with hpM
  · positivity
  · have hp2 : p ≠ 2 := fun h => hpM (h ▸ h2M)
    have hp3 : p ≠ 3 := fun h => hpM (h ▸ h3M)
    have hp4 : (4 : ℝ) ≤ p := by
      exact_mod_cast (show 4 ≤ p by have := hp.two_le; omega)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    norm_num only [Nat.cast_ofNat]
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < p - 3) hp0]
    linarith

theorem scalarMomentAF_prime_mul_le (M k n : ℕ) (h2M : 2 ∣ M) (h3M : 3 ∣ M)
    {p : ℕ} (hp : p.Prime) :
    scalarMomentAF M k (p * n) ≤ scalarMomentAF M k p * scalarMomentAF M k n := by
  by_cases hpn : p ∣ n
  · have hns : ¬Squarefree (p * n) := by
      intro hsq
      exact hp.not_isUnit (hsq p (Nat.mul_dvd_mul_left p hpn))
    rw [scalarMomentAF_apply, if_neg (fun h => hns h.1)]
    exact mul_nonneg (scalarMomentAF_nonneg M k p h2M h3M)
      (scalarMomentAF_nonneg M k n h2M h3M)
  · exact le_of_eq ((scalarMomentAF_multiplicative M k).map_mul_of_coprime
      (hp.coprime_iff_not_dvd.mpr hpn))

theorem exists_scalarMoment_two_cumulative_growth (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 1 ≤ x →
      abelCumulative (scalarMomentAF M 2) x ≤ D * (1 + Real.log x) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_scalarMoment_two_uniform_error M hM h2M h3M 1 (by norm_num)
  let c := scalarSieveEulerConstant M * (coprimeHarmonicDensity M ^ 2 / 2)
  have hc : 0 ≤ c := mul_nonneg
    (zero_le_one.trans (scalarSieveEulerConstant_ge_one M h2M h3M)) (by positivity)
  refine ⟨1 + c + C, by positivity, ?_⟩
  intro x hx
  have hlog := Real.log_nonneg hx
  have h := (le_abs_self _).trans (hbound x hx)
  have hbase : abelCumulative (scalarMomentAF M 2) x ≤ (1 + c) * (Real.log x) ^ 2 + C := by
    change abelCumulative (scalarMomentAF M 2) x - c * (Real.log x) ^ 2 ≤
      1 * (Real.log x) ^ 2 + C at h
    linarith
  have hpow : (Real.log x) ^ 2 ≤ (1 + Real.log x) ^ 2 :=
    pow_le_pow_left₀ hlog (by linarith) 2
  have hone : 1 ≤ (1 + Real.log x) ^ 2 := one_le_pow₀ (by linarith : 1 ≤ 1 + Real.log x)
  refine hbase.trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ 1 + c by positivity),
    mul_le_mul_of_nonneg_left hone hC]

end Erdos964
