import ErdosProblems.Erdos587.HooleyPrimeError
import ErdosProblems.Erdos587.HooleySmoothEnvelope

/-!
# Initial cutoffs for the harmonic moment induction

Below three the only possible largest prime is two, and its cofactor is
one. The resulting exponential bound is absorbed uniformly by the cubic
factorial envelope.
-/

open scoped BigOperators

namespace Erdos587

@[simp] lemma deltaSmoothNumbers_two : deltaSmoothNumbers 2 = {1} := by
  have hp : Nat.primesBelow 2 = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    obtain ⟨hp, hprime⟩ := Nat.mem_primesBelow.mp hp
    exact (not_lt_of_ge hprime.two_le) hp
  simp [deltaSmoothNumbers, deltaPrimeProduct, hp]

lemma deltaPrimeIncrement_at_one_le (q : ℕ) :
    deltaPrimeIncrement 1 2 q ≤ (2 : ℝ) ^ q := by
  have hsum : (∑ b ∈ Finset.Icc 1 (q / 2),
      (q.choose b : ℝ) * deltaMixedMoment 1 (q - b) b (Real.log 2)) ≤ (2 : ℝ) ^ q := by
    calc
      _ ≤ ∑ b ∈ Finset.Icc 1 (q / 2), (q.choose b : ℝ) := by
        apply Finset.sum_le_sum
        intro b hb
        obtain ⟨hb, hbq⟩ := Finset.mem_Icc.mp hb
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (deltaMixedMoment_at_one_le (by omega : q - b ≠ 0) b (Real.log 2))
          (show (0 : ℝ) ≤ q.choose b by positivity)
      _ ≤ ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro b hb
          have hbq := (Finset.mem_Icc.mp hb).2
          exact Finset.mem_range.mpr (by omega)
        · intro b hb hnot
          positivity
      _ = _ := by exact_mod_cast Nat.sum_range_choose q
  unfold deltaPrimeIncrement
  simp only [Nat.divisors_one, Finset.card_singleton, Nat.cast_one, Nat.cast_ofNat, one_mul]
  have hpow : 0 ≤ (2 : ℝ) ^ q := by positivity
  linarith

lemma restrictedDeltaPrimeError_small (G : ℕ → Prop) [DecidablePred G]
    (q : ℕ) {x : ℕ} (hx : x ≤ 3) :
    restrictedDeltaPrimeError G q x ≤ (2 : ℝ) ^ q := by
  have hprimes : x.primesBelow ⊆ {2} := by
    intro p hp
    obtain ⟨hpx, hp⟩ := Nat.mem_primesBelow.mp hp
    have hp2 := hp.two_le
    simpa only [Finset.mem_singleton] using (show p = 2 by omega)
  unfold restrictedDeltaPrimeError
  calc
    _ ≤ ∑ p ∈ ({2} : Finset ℕ),
        ∑ n ∈ (deltaSmoothNumbers p).filter G, deltaPrimeIncrement n p q :=
      Finset.sum_le_sum_of_subset_of_nonneg hprimes (fun p _ _ =>
        Finset.sum_nonneg (fun n _ => deltaPrimeIncrement_nonneg n p q))
    _ ≤ deltaPrimeIncrement 1 2 q := by
      simp only [Finset.sum_singleton, deltaSmoothNumbers_two]
      have h := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset G ({1} : Finset ℕ))
        (fun n _ _ => deltaPrimeIncrement_nonneg n 2 q)
      simpa only [Finset.sum_singleton] using h
    _ ≤ _ := deltaPrimeIncrement_at_one_le q

lemma two_pow_le_two_mul_factorial (q : ℕ) : 2 ^ q ≤ 2 * q.factorial := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    by_cases hq : q = 0
    · subst q
      norm_num
    · rw [pow_succ, Nat.factorial_succ]
      nlinarith [Nat.factorial_pos q, Nat.one_le_iff_ne_zero.mpr hq]

lemma small_cutoff_le_deltaSmoothMomentEnvelope {B : ℝ} (hB : 1 ≤ B)
    {q : ℕ} (hq : 2 ≤ q) :
    (1 + (2 : ℝ) ^ q) ≤ 3 * deltaSmoothMomentEnvelope B q / ((q : ℝ) ^ 2 * B) := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hfact : (q : ℝ) ≤ q.factorial := by exact_mod_cast Nat.self_le_factorial q
  have hfpos : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
  have htwo : (2 : ℝ) ^ q ≤ 2 * q.factorial := by
    exact_mod_cast two_pow_le_two_mul_factorial q
  have hBpow : B ≤ B ^ (q - 1) := by
    exact le_self_pow₀ hB (by omega)
  have hsq : (q : ℝ) ^ 2 ≤ (q.factorial : ℝ) ^ 2 := by gcongr
  have hcube : (1 + (2 : ℝ) ^ q) * (q : ℝ) ^ 2 ≤ 3 * (q.factorial : ℝ) ^ 3 := by
    calc
      _ ≤ (3 * q.factorial) * (q : ℝ) ^ 2 := by gcongr; linarith
      _ ≤ (3 * q.factorial) * (q.factorial : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hqpos) hBpos)).mpr
  calc
    _ = ((1 + (2 : ℝ) ^ q) * (q : ℝ) ^ 2) * B := by ring
    _ ≤ (3 * (q.factorial : ℝ) ^ 3) * B := mul_le_mul_of_nonneg_right hcube hBpos.le
    _ ≤ (3 * (q.factorial : ℝ) ^ 3) * B ^ (q - 1) := by gcongr
    _ = _ := by unfold deltaSmoothMomentEnvelope deltaMomentEnvelope; ring

end Erdos587
