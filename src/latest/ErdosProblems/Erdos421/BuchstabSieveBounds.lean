import ErdosProblems.Erdos421.SievePrimeProducts
import ErdosProblems.Erdos421.WeightedBuchstab

/-! # A pointwise lower sieve constructed from upper sieves -/

namespace Erdos421

theorem roughIndicator_buchstab (n z : ℕ) :
    (1 : ℝ) = roughIndicator n z +
      ∑ p ∈ sievePrimes 0 z, if p ∣ n then roughIndicator (n / p) p else 0 := by
  classical
  have h := weighted_buchstab_identity {n} (fun _ ↦ (1 : ℝ)) (Nat.zero_le z)
  have hzero : RoughAt n 0 := fun p _ hp ↦ (Nat.not_lt_zero p hp).elim
  have hs (w : ℕ) : (∑ m ∈ sifted {n} w, (1 : ℝ)) = roughIndicator n w := by
    by_cases hr : RoughAt n w <;> simp [sifted, roughIndicator, Finset.filter_singleton, hr]
  rw [hs 0, hs z] at h
  have hc (p : ℕ) :
      (∑ _d ∈ sifted (sieveCofactors {n} p) p, (1 : ℝ)) =
        if p ∣ n then roughIndicator (n / p) p else 0 := by
    by_cases hpn : p ∣ n
    · by_cases hr : RoughAt (n / p) p <;>
        simp [sieveCofactors, sifted, roughIndicator, Finset.filter_singleton, hpn, hr]
    · simp [sieveCofactors, sifted, Finset.filter_singleton, hpn]
  simp only [hc, roughIndicator, if_pos hzero] at h
  exact h

noncomputable def sieveDivisorSum (z : ℕ) (ρ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ (primeProductBelow z).divisors, if d ∣ n then ρ d else 0

noncomputable def buchstabLowerValue (z : ℕ) (ρ : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - ∑ p ∈ sievePrimes 0 z, if p ∣ n then sieveDivisorSum p (ρ p) (n / p) else 0

theorem buchstabLowerValue_le_roughIndicator (z : ℕ) (ρ : ℕ → ℕ → ℝ)
    (hρ : ∀ p ∈ sievePrimes 0 z, BoundingSieve.IsUpperMoebius (ρ p)) (n : ℕ) :
    buchstabLowerValue z ρ n ≤ roughIndicator n z := by
  have hb : (∑ p ∈ sievePrimes 0 z, if p ∣ n then roughIndicator (n / p) p else 0) ≤
      ∑ p ∈ sievePrimes 0 z, if p ∣ n then sieveDivisorSum p (ρ p) (n / p) else 0 := by
    apply Finset.sum_le_sum
    intro p hp
    split_ifs
    · exact upper_sieve_pointwise (ρ p) (hρ p hp) (n / p) p
    · exact le_rfl
  have hi := roughIndicator_buchstab n z
  unfold buchstabLowerValue
  linarith

end Erdos421
