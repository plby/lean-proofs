import ErdosProblems.Erdos421.SievePrimeProducts

/-! # Exact telescoping for the rough-number Euler product -/

namespace Erdos421

noncomputable def roughEulerProduct (z : ℕ) : ℝ :=
  ∏ p ∈ sievePrimes 0 z, (1 - (p : ℝ)⁻¹)

theorem primeFactors_primeProductBelow (z : ℕ) :
    (primeProductBelow z).primeFactors = sievePrimes 0 z := by
  ext p
  simp only [Nat.mem_primeFactors, sievePrimes, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨hp, hpd, _⟩
    exact ⟨⟨Nat.zero_le _, (prime_dvd_primeProductBelow_iff hp).mp hpd⟩, hp⟩
  · rintro ⟨⟨_, hpz⟩, hp⟩
    exact ⟨hp, (prime_dvd_primeProductBelow_iff hp).mpr hpz,
      (primeProductBelow_squarefree z).ne_zero⟩

theorem roughEulerProduct_pos (z : ℕ) : 0 < roughEulerProduct z := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
  exact sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr hp1)

theorem roughEulerProduct_zero : roughEulerProduct 0 = 1 := by
  simp [roughEulerProduct, sievePrimes]

theorem roughEulerProduct_succ (z : ℕ) :
    roughEulerProduct (z + 1) = roughEulerProduct z -
      (if z.Prime then roughEulerProduct z / (z : ℝ) else 0) := by
  have hz : z ∉ (Finset.range z).filter Nat.Prime := by simp
  by_cases hp : z.Prime
  · simp only [roughEulerProduct, sievePrimes, Nat.Ico_zero_eq_range,
      Finset.range_add_one, Finset.filter_insert, if_pos hp, Finset.prod_insert hz]
    ring
  · simp [roughEulerProduct, sievePrimes, Nat.Ico_zero_eq_range,
      Finset.range_add_one, Finset.filter_insert, hp]

theorem roughEulerProduct_prefix (z : ℕ) :
    (∑ p ∈ sievePrimes 0 z, roughEulerProduct p / (p : ℝ)) = 1 - roughEulerProduct z := by
  induction z with
  | zero => simp [sievePrimes, roughEulerProduct_zero]
  | succ z ih =>
    simp only [sievePrimes, Nat.Ico_zero_eq_range] at ih
    have hz : z ∉ (Finset.range z).filter Nat.Prime := by simp
    by_cases hp : z.Prime
    · simp only [sievePrimes, Nat.Ico_zero_eq_range,
        Finset.range_add_one, Finset.filter_insert, if_pos hp, Finset.sum_insert hz]
      rw [ih, roughEulerProduct_succ, if_pos hp]
      ring
    · simp only [sievePrimes, Nat.Ico_zero_eq_range,
        Finset.range_add_one, Finset.filter_insert, if_neg hp]
      rw [ih, roughEulerProduct_succ, if_neg hp, sub_zero]

theorem roughEulerProduct_interval {w z : ℕ} (hwz : w ≤ z) :
    (∑ p ∈ sievePrimes w z, roughEulerProduct p / (p : ℝ)) =
      roughEulerProduct w - roughEulerProduct z := by
  have hs (x : ℕ) : (∑ p ∈ Finset.range x,
      if p.Prime then roughEulerProduct p / (p : ℝ) else 0) = 1 - roughEulerProduct x := by
    simpa only [sievePrimes, Nat.Ico_zero_eq_range, Finset.sum_filter] using
      roughEulerProduct_prefix x
  rw [sievePrimes, Finset.sum_filter, Finset.sum_Ico_eq_sub _ hwz, hs z, hs w]
  ring

theorem roughEulerProduct_antitone : Antitone roughEulerProduct := by
  intro w z hwz
  have hs : 0 ≤ ∑ p ∈ sievePrimes w z, roughEulerProduct p / (p : ℝ) :=
    Finset.sum_nonneg (fun p _ ↦ div_nonneg (roughEulerProduct_pos p).le (Nat.cast_nonneg p))
  rw [roughEulerProduct_interval hwz] at hs
  linarith

end Erdos421
