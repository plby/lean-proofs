import ErdosProblems.Erdos248.LargeMoment
import ErdosProblems.Erdos248.PrimeRangeFacts

/-!
# Erdős Problem 248: concrete large-range fourth moments

This file specializes the abstract correlation-to-fourth-moment theorem from
`LargeMoment.lean` to the actual near and far prime ranges.  All elementary
membership and separation facts are supplied by `PrimeRangeFacts.lean`.
-/

noncomputable section

open scoped BigOperators

namespace Erdos248

private theorem primesBetween_card_le_upper (lo hi : ℕ) :
    (primesBetween lo hi).card ≤ hi := by
  have hsub : primesBetween lo hi ⊆ Finset.Icc 1 hi := by
    intro p hp
    have hp' := mem_primesBetween.mp hp
    exact Finset.mem_Icc.mpr ⟨hp'.2.2.pos, hp'.2.1⟩
  calc
    (primesBetween lo hi).card ≤ (Finset.Icc 1 hi).card :=
      Finset.card_le_card hsub
    _ ≤ hi := by simp

theorem largePrimes_card_le_largestRadius (K k : ℕ) :
    (largePrimes K k).card ≤ shiftRadius K 1 := by
  exact primesBetween_card_le_upper _ _

theorem farPrimes_card_le_largestRadius (K k : ℕ) :
    (farPrimes K k).card ≤ shiftRadius K 1 := by
  exact primesBetween_card_le_upper _ _

theorem farPrimes_subset_base {K k : ℕ} (hKk : K ≤ k) :
    farPrimes K k ⊆ farPrimes K K := by
  intro p hp
  unfold farPrimes at hp ⊢
  have hp' := mem_primesBetween.mp hp
  rw [mem_primesBetween]
  exact ⟨(max_le_max_left (tinyCutoff K) hKk |>.trans_lt hp'.1),
    hp'.2⟩

/-- The far-range reciprocal sum is also bounded at scale `K`; this is the
bound used to cancel the `K⁻⁴` correlation error. -/
theorem sum_farPrimes_inv_le_uniform_scale {K k : ℕ}
    (hK : 0 < K) (hKk : K ≤ k) :
    (∑ p ∈ farPrimes K k, (1 : ℝ) / p) ≤
      largePrimeUniformReciprocalConstant * (K : ℝ) := by
  have hsub := farPrimes_subset_base hKk
  have hsumsub :
      (∑ p ∈ farPrimes K k, (1 : ℝ) / p) ≤
        ∑ p ∈ farPrimes K K, (1 : ℝ) / p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp hpnot
    positivity
  calc
    (∑ p ∈ farPrimes K k, (1 : ℝ) / p) ≤
        ∑ p ∈ farPrimes K K, (1 : ℝ) / p := hsumsub
    _ ≤ farPrimeReciprocalConstant * (K : ℝ) :=
      sum_farPrimes_inv_le hK le_rfl
    _ ≤ largePrimeUniformReciprocalConstant * (K : ℝ) := by
      gcongr
      exact farPrimeReciprocalConstant_le_uniform

/-- Concrete centered fourth-moment bound for the near-coordinate large
prime range. -/
theorem nearLargePrimeCenteredFourthMoment_le
    {A : ℝ} (hA : HasUniformWirsingBound A)
    {K k : ℕ} (hreg : NormalizationRegular A K)
    (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    largePrimeCenteredFourthMoment K k (largePrimes K k) ≤
      largePrimeFourthMomentConstant * (k : ℝ) ^ 2 * sieveMass K := by
  apply largePrimeCenteredFourthMoment_le_of_correlations hA hreg hk1
  · exact largePrimes_card_le_largestRadius K k
  · intro p hp
    exact prime_of_mem_largePrimes hp
  · calc
      (∑ p ∈ largePrimes K k, (1 : ℝ) / p) ≤
          largePrimeReciprocalConstant * (k : ℝ) :=
        sum_largePrimes_inv_le hk1 hkK
      _ ≤ largePrimeUniformReciprocalConstant * (K : ℝ) := by
        calc
          largePrimeReciprocalConstant * (k : ℝ) ≤
              largePrimeUniformReciprocalConstant * (k : ℝ) := by
            gcongr
            exact largePrimeReciprocalConstant_le_uniform
          _ ≤ largePrimeUniformReciprocalConstant * (K : ℝ) := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hkK)
              largePrimeUniformReciprocalConstant_pos.le
  · exact (sum_largePrimes_inv_le hk1 hkK).trans (by
      gcongr
      exact largePrimeReciprocalConstant_le_uniform)
  · intro J hJI hJcard
    have hJprime : ∀ p ∈ J, p.Prime := fun p hp ↦
      prime_of_mem_largePrimes (hJI hp)
    have hJcut : ∀ p ∈ J, tinyCutoff K < p := fun p hp ↦
      tinyCutoff_lt_of_mem_largePrimes hk1 hkK (hJI hp)
    let m : nearShifts K := ⟨k, mem_nearShifts.mpr ⟨hk1, hkK⟩⟩
    have hraw := nearLargePrimeProductEventMass_centered_le
      hA m hreg hJcard hJprime hJcut
      (fun p hp ↦ shiftRadius_le_of_mem_largePrimes (hJI hp))
      (fun p hp h hne ↦ largePrime_separated hk1 hkK (hJI hp) h)
    have hrel := primeProductEventError_le_largeRelative hreg.1
      hJcard hJprime hJcut
    simpa [m] using hraw.trans hrel

/-- Concrete centered fourth-moment bound for the far-coordinate large prime
range. -/
theorem farLargePrimeCenteredFourthMoment_le
    {A : ℝ} (hA : HasUniformWirsingBound A)
    {K k : ℕ} (hreg : NormalizationRegular A K)
    (hkK : K < k) :
    largePrimeCenteredFourthMoment K k (farPrimes K k) ≤
      largePrimeFourthMomentConstant * (k : ℝ) ^ 2 * sieveMass K := by
  have hk1 : 1 ≤ k := hreg.1.trans_le hkK.le
  apply largePrimeCenteredFourthMoment_le_of_correlations hA hreg hk1
  · exact farPrimes_card_le_largestRadius K k
  · intro p hp
    exact prime_of_mem_farPrimes hp
  · exact sum_farPrimes_inv_le_uniform_scale hreg.1 hkK.le
  · exact (sum_farPrimes_inv_le hreg.1 hkK.le).trans (by
      gcongr
      exact farPrimeReciprocalConstant_le_uniform)
  · intro J hJI hJcard
    have hJprime : ∀ p ∈ J, p.Prime := fun p hp ↦
      prime_of_mem_farPrimes (hJI hp)
    have hJcut : ∀ p ∈ J, tinyCutoff K < p := fun p hp ↦
      tinyCutoff_lt_of_mem_farPrimes (hJI hp)
    have hraw := farPrimeProductEventMass_centered_le
      hA hreg hJcard
      (fun h ↦ by
        have hhK := (mem_nearShifts.mp h.property).2
        omega)
      hJprime hJcut
      (fun p hp h ↦ farPrime_separated hkK (hJI hp) h)
    have hrel := primeProductEventError_le_largeRelative hreg.1
      hJcard hJprime hJcut
    exact hraw.trans hrel

end Erdos248
