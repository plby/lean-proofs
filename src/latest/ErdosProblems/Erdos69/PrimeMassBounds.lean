import ErdosProblems.Erdos69.RoughSizeBounds
import ErdosProblems.Erdos697.Erdos697PrimeHarmonic

/-!
# Elementary reciprocal-prime bounds

We reuse the repository's unconditional, bounded-error Mertens theorem.
Its proof uses the von Mangoldt divisor identity and finite Abel summation.
-/

open scoped BigOperators

namespace Erdos69.Elementary

noncomputable def primeReciprocalSum (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE x, (1 : ℝ) / p

theorem exists_primeReciprocal_error_constant :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 2 ≤ x →
      |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C := by
  exact Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log

theorem reciprocal_primeFactors_le_cutoff (Q R : ℕ) (hQ : 0 < Q) (hR : 0 < R) :
    (∑ p ∈ Q.primeFactors, (1 : ℝ) / p) ≤
      primeReciprocalSum R + Real.log Q / ((R : ℝ) * Real.log 2) := by
  classical
  let small := Q.primeFactors.filter (fun p ↦ p ≤ R)
  let large := Q.primeFactors.filter (fun p ↦ ¬p ≤ R)
  have hsmall : small ⊆ Nat.primesLE R := by
    intro p hp
    obtain ⟨hpQ, hpR⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpR, (Nat.mem_primeFactors.mp hpQ).1⟩
  have hs : (∑ p ∈ small, (1 : ℝ) / p) ≤ primeReciprocalSum R :=
    Finset.sum_le_sum_of_subset_of_nonneg hsmall (fun _ _ _ ↦ by positivity)
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hlarge : (∑ p ∈ large, (1 : ℝ) / p) ≤ (large.card : ℝ) / R := by
    calc
      _ ≤ ∑ _p ∈ large, (1 : ℝ) / R := by
        apply Finset.sum_le_sum
        intro p hp
        have hpR : R < p := Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2
        exact one_div_le_one_div_of_le hRR (by exact_mod_cast hpR.le)
      _ = _ := by simp [div_eq_mul_inv]
  have hcard : (large.card : ℝ) ≤ omegaCount Q := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hlog := omegaCount_mul_log_two_le hQ
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have homega : (omegaCount Q : ℝ) ≤ Real.log Q / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr hlog
  have hl : (∑ p ∈ large, (1 : ℝ) / p) ≤ Real.log Q / ((R : ℝ) * Real.log 2) := by
    calc
      _ ≤ (large.card : ℝ) / R := hlarge
      _ ≤ (Real.log Q / Real.log 2) / R :=
        div_le_div_of_nonneg_right (hcard.trans homega) hRR.le
      _ = _ := by ring
  have hsplit : (∑ p ∈ Q.primeFactors, (1 : ℝ) / p) =
      (∑ p ∈ small, (1 : ℝ) / p) + ∑ p ∈ large, (1 : ℝ) / p := by
    exact (Finset.sum_filter_add_sum_filter_not Q.primeFactors (fun p ↦ p ≤ R) _).symm
  rw [hsplit]
  exact add_le_add hs hl

noncomputable def goodPrimes (Q L y : ℕ) : Finset ℕ :=
  (Nat.primesLE y).filter (fun p ↦ L < p ∧ ¬p ∣ Q)

theorem goodPrime_reciprocal_lower (Q L y : ℕ) (hQ : 0 < Q) :
    primeReciprocalSum y - primeReciprocalSum L -
      (∑ p ∈ Q.primeFactors, (1 : ℝ) / p) ≤
        ∑ p ∈ goodPrimes Q L y, (1 : ℝ) / p := by
  classical
  have hcover : Nat.primesLE y ⊆ goodPrimes Q L y ∪ Nat.primesLE L ∪ Q.primeFactors := by
    intro p hp
    by_cases hL : L < p
    · by_cases hd : p ∣ Q
      · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
          ⟨(Nat.mem_primesLE.mp hp).2, hd, hQ.ne'⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hp, hL, hd⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Nat.mem_primesLE.mpr ⟨by omega, (Nat.mem_primesLE.mp hp).2⟩))
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ ↦ (1 : ℝ) / p)
    hcover (fun p _ _ ↦ by positivity)
  have hule (s t : Finset ℕ) : (∑ p ∈ s ∪ t, (1 : ℝ) / p) ≤
      (∑ p ∈ s, (1 : ℝ) / p) + ∑ p ∈ t, (1 : ℝ) / p := by
    have heq := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := fun p : ℕ ↦ (1 : ℝ) / p)
    have hn : 0 ≤ ∑ p ∈ s ∩ t, (1 : ℝ) / p := Finset.sum_nonneg (fun _ _ ↦ by positivity)
    linarith
  have hu₁ := hule (goodPrimes Q L y ∪ Nat.primesLE L) Q.primeFactors
  have hu₂ := hule (goodPrimes Q L y) (Nat.primesLE L)
  unfold primeReciprocalSum
  linarith

end Erdos69.Elementary
