import Util.Bernays.LocalParity

/-!
# Logarithmic coefficients for general local norm conditions

The exact prime-power convolution generalizes the corresponding argument in
Erdős 1081 to any set of obstruction primes.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

/-- Logarithmic-derivative coefficient of the local Euler factor.  It is
`log l` at every positive exponent of an allowed prime, while at an
obstruction prime it is `2 log l` at positive even exponents and zero at odd
exponents. -/
noncomputable def localLogCoeff (S : ℕ → Prop) (l k : ℕ) : ℝ :=
  if k = 0 then 0
  else if S l then
    if Even k then 2 * Real.log l else 0
  else Real.log l

theorem localLogCoeff_nonneg
    (S : ℕ → Prop) (k : ℕ) {l : ℕ} (_hl : l.Prime) :
    0 ≤ localLogCoeff S l k := by
  classical
  unfold localLogCoeff
  split_ifs <;> positivity

/-- Among `1,...,2r`, exactly the even indices contribute to the doubled
logarithmic coefficient.  The formulation as a real-valued sum is the one
used directly in the local convolution identity. -/
theorem sum_Icc_even_two (r : ℕ) :
    (∑ k ∈ Finset.Icc 1 (2 * r),
        if Even k then (2 : ℝ) else 0) = 2 * r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [show 2 * (r + 1) = 2 * r + 2 by omega,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ 2 * r + 2),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ 2 * r + 1)]
      simp only [ih]
      have heven : Even (2 * r + 2) := ⟨r + 1, by omega⟩
      simp [heven]
      ring

/-- Exact one-prime logarithmic convolution.  This is the coefficient-level
identity behind the Wirsing recurrence for the local norm indicator. -/
theorem localParity_prime_pow_log_convolution
    (S : ℕ → Prop) {l e : ℕ} (hl : l.Prime) :
    localParity S (l ^ e) * Real.log ((l ^ e : ℕ) : ℝ) =
      ∑ k ∈ Finset.Icc 1 e,
        localParity S (l ^ (e - k)) *
          localLogCoeff S l k := by
  classical
  by_cases hobs : S l
  · by_cases he : Even e
    · obtain ⟨r, rfl⟩ := he
      simp only [show r + r = 2 * r by omega]
      have heven : Even (2 * r) := ⟨r, by omega⟩
      have hind : localParity S (l ^ (2 * r)) = 1 := by
        rw [localParity_prime_pow S hl]
        simp [hobs, Nat.not_odd_iff_even.mpr heven]
      have hsumPoint (k : ℕ) (hk : k ∈ Finset.Icc 1 (2 * r)) :
          localParity S (l ^ (2 * r - k)) *
              localLogCoeff S l k =
            (if Even k then (2 : ℝ) else 0) * Real.log l := by
        have hkI := Finset.mem_Icc.mp hk
        have hk0 : k ≠ 0 := by omega
        rw [localLogCoeff, if_neg hk0, if_pos hobs]
        by_cases hke : Even k
        · rcases hke with ⟨s, hs⟩
          have hdiff : Even (2 * r - k) := ⟨r - s, by omega⟩
          have hke' : Even k := ⟨s, hs⟩
          have hdiffNotOdd : ¬ Odd (2 * r - k) :=
            Nat.not_odd_iff_even.mpr hdiff
          simp [hke', hdiffNotOdd, localParity_prime_pow S hl, hobs]
        · simp [hke]
      calc
        localParity S (l ^ (2 * r)) *
            Real.log ((l ^ (2 * r) : ℕ) : ℝ) =
            (2 * r : ℝ) * Real.log l := by
              rw [hind, one_mul, Nat.cast_pow, Real.log_pow]
              push_cast
              ring
        _ = (∑ k ∈ Finset.Icc 1 (2 * r),
              if Even k then (2 : ℝ) else 0) * Real.log l := by
              rw [sum_Icc_even_two]
        _ = ∑ k ∈ Finset.Icc 1 (2 * r),
              localParity S (l ^ (2 * r - k)) *
                localLogCoeff S l k := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro k hk
              exact (hsumPoint k hk).symm
    · have heodd : Odd e := Nat.not_even_iff_odd.mp he
      rw [localParity_prime_pow S hl]
      simp only [hobs, true_and, heodd, if_pos, zero_mul]
      apply (Finset.sum_eq_zero ?_).symm
      intro k hk
      have hkI := Finset.mem_Icc.mp hk
      have hk0 : k ≠ 0 := by omega
      rw [localLogCoeff, if_neg hk0, if_pos hobs]
      by_cases hke : Even k
      · rcases heodd with ⟨r, hr⟩
        rcases hke with ⟨s, hs⟩
        have hdiff : Odd (e - k) := ⟨r - s, by omega⟩
        have hke' : Even k := ⟨s, hs⟩
        rw [localParity_prime_pow S hl]
        simp [hobs, hke', hdiff]
      · simp [hke]
  · rw [localParity_prime_pow S hl]
    simp only [hobs, false_and, if_false]
    rw [Nat.cast_pow, Real.log_pow]
    calc
      (1 : ℝ) * ((e : ℝ) * Real.log l) =
          ∑ k ∈ Finset.Icc 1 e, Real.log l := by simp
      _ = ∑ k ∈ Finset.Icc 1 e,
          localParity S (l ^ (e - k)) *
            localLogCoeff S l k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkI := Finset.mem_Icc.mp hk
        have hk0 : k ≠ 0 := by omega
        rw [localLogCoeff, if_neg hk0, if_neg hobs,
          localParity_prime_pow S hl]
        simp [hobs]

/-- Cumulative logarithmic-derivative mass through `Q`. -/
noncomputable def localLogMass (S : ℕ → Prop) (Q : ℕ) : ℝ :=
  ∑ l ∈ (Q + 1).primesBelow,
    ∑ k ∈ Finset.Icc 1 (Nat.log l Q), localLogCoeff S l k


end Bernays
