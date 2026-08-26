import ErdosProblems.Erdos380.PrimeRadical
import ErdosProblems.Erdos380.SmallPrimeTupleMoments

/-! # A smooth shifted integer forces a large prime-divisibility mass -/

open scoped BigOperators Classical

namespace Erdos380

noncomputable def smallShiftPrimes (T : ℕ) (h : ℤ) : Finset ℕ :=
  (Nat.primesLE T).filter fun p => ¬ (p : ℤ) ∣ h

noncomputable def largeShiftPrimeCount (T Y c V : ℕ) (h : ℤ) : ℝ :=
  ∑ p ∈ (Finset.Ioc T Y).filter Nat.Prime,
    if smallPrimeDivisibilityEvent c h p V then (1 : ℝ) else 0

lemma log_mul_normalizedSmallPrimeMass (t : Finset ℕ) {T : ℕ} (hT : 2 ≤ T)
    (c : ℕ) (h : ℤ) (V : ℕ) :
    Real.log (T : ℝ) * normalizedSmallPrimeMass t T c h V =
      ∑ p ∈ t, Real.log (p : ℝ) *
        if smallPrimeDivisibilityEvent c h p V then (1 : ℝ) else 0 := by
  have hlog : Real.log (T : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < T))).ne'
  unfold normalizedSmallPrimeMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  field_simp

theorem primeFactors_log_sum_le_shift_masses
    {n T Y c V : ℕ} {h : ℤ} (hn : 0 < n) (hT : 2 ≤ T) (hh : h ≠ 0)
    (heq : (n : ℤ) = (c * V : ℕ) + h) (hsmooth : largestPrimeFactor n ≤ Y) :
    (∑ p ∈ n.primeFactors, Real.log (p : ℝ)) ≤
      Real.log (h.natAbs : ℝ) +
        Real.log (T : ℝ) * normalizedSmallPrimeMass (smallShiftPrimes T h) T c h V +
        Real.log (Y : ℝ) * largeShiftPrimeCount T Y c V h := by
  classical
  let A := n.primeFactors.filter fun p : ℕ => (p : ℤ) ∣ h
  let B := n.primeFactors.filter fun p : ℕ => ¬ (p : ℤ) ∣ h ∧ p ≤ T
  let C := n.primeFactors.filter fun p : ℕ => ¬ (p : ℤ) ∣ h ∧ T < p
  have hhit {p : ℕ} (hp : p ∈ n.primeFactors) : smallPrimeDivisibilityEvent c h p V := by
    unfold smallPrimeDivisibilityEvent
    rw [← heq]
    exact_mod_cast Nat.dvd_of_mem_primeFactors hp
  have hsplit : (∑ p ∈ n.primeFactors, Real.log (p : ℝ)) =
      (∑ p ∈ A, Real.log (p : ℝ)) + (∑ p ∈ B, Real.log (p : ℝ)) +
        (∑ p ∈ C, Real.log (p : ℝ)) := by
    simp only [A, B, C, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hph : (p : ℤ) ∣ h <;> by_cases hpT : p ≤ T <;>
      simp [hph, hpT, show (T < p) ↔ ¬ p ≤ T by omega]
  have hA : (∑ p ∈ A, Real.log (p : ℝ)) ≤ Real.log (h.natAbs : ℝ) :=
    sum_log_distinct_prime_divisors_int_le hh
      (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (fun p hp => (Finset.mem_filter.mp hp).2)
  have hBsub : B ⊆ smallShiftPrimes T h := by
    intro p hp
    obtain ⟨hp, hph, hpT⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpT, Nat.prime_of_mem_primeFactors hp⟩, hph⟩
  have hB : (∑ p ∈ B, Real.log (p : ℝ)) ≤
      Real.log (T : ℝ) * normalizedSmallPrimeMass (smallShiftPrimes T h) T c h V := by
    rw [log_mul_normalizedSmallPrimeMass _ hT]
    calc
      _ = ∑ p ∈ B, Real.log (p : ℝ) *
          if smallPrimeDivisibilityEvent c h p V then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [if_pos (hhit (Finset.mem_filter.mp hp).1), mul_one]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hBsub (fun p _ _ =>
        mul_nonneg (Real.log_natCast_nonneg p) (by split_ifs <;> norm_num))
  have hCsub : C ⊆ (Finset.Ioc T Y).filter Nat.Prime := by
    intro p hp
    obtain ⟨hp, _, hpT⟩ := Finset.mem_filter.mp hp
    have hpP := Nat.prime_of_mem_primeFactors hp
    have hpY := (prime_le_largestPrimeFactor hn.ne' hpP (Nat.dvd_of_mem_primeFactors hp)).trans hsmooth
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpT, hpY⟩, hpP⟩
  have hC : (∑ p ∈ C, Real.log (p : ℝ)) ≤ Real.log (Y : ℝ) * largeShiftPrimeCount T Y c V h := by
    unfold largeShiftPrimeCount
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ p ∈ C, Real.log (Y : ℝ) *
          if smallPrimeDivisibilityEvent c h p V then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro p hp
        have hpf := (Finset.mem_filter.mp hp).1
        rw [if_pos (hhit hpf), mul_one]
        exact Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hpf).pos)
          (by exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hCsub hp)).1).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hCsub (fun p _ _ =>
        mul_nonneg (Real.log_natCast_nonneg Y) (by split_ifs <;> norm_num))
  rw [hsplit]
  linarith

/-- The pointwise arithmetic implication used before applying the two
probability estimates. -/
theorem smooth_shift_log_le_masses
    {n D T Y c V : ℕ} {h : ℤ} (hn : 0 < n) (hDpos : 0 < D)
    (hD : ∀ d : ℕ, d ^ 2 ∣ n → d ≤ D) (hT : 2 ≤ T) (hh : h ≠ 0)
    (heq : (n : ℤ) = (c * V : ℕ) + h) (hsmooth : largestPrimeFactor n ≤ Y) :
    Real.log (n : ℝ) ≤ 2 * Real.log (D : ℝ) + Real.log (h.natAbs : ℝ) +
      Real.log (T : ℝ) * normalizedSmallPrimeMass (smallShiftPrimes T h) T c h V +
      Real.log (Y : ℝ) * largeShiftPrimeCount T Y c V h := by
  have hrad := log_le_square_cutoff_add_primeFactors hn hDpos hD
  have hmass := primeFactors_log_sum_le_shift_masses hn hT hh heq hsmooth
  linarith

end Erdos380
