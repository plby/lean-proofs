import ErdosProblems.Erdos964.Basic

/-!
# Exact prime-slice formulas for semiprimes

The sieve counts semiprimes by their smaller prime factor. Ordering the
factors makes this parametrization injective and avoids counting squares.
The identities here retain a general weight, so they can be applied to
the square divisor weights in a GPY sum.
-/

namespace Erdos964

open scoped BigOperators

/-- The finite prime pairs under consideration; `P` specifies the permitted
smaller prime factors. -/
def semiprimePairs (C : ℕ) (P : Finset ℕ) (X : ℕ) : Finset (ℕ × ℕ) :=
  (P ×ˢ Finset.range (X + 1)).filter fun pq =>
    pq.1.Prime ∧ pq.2.Prime ∧ C < pq.1 ∧ pq.1 < pq.2 ∧ pq.1 * pq.2 ≤ X

theorem prime_pair_mul_injective :
    Set.InjOn (fun pq : ℕ × ℕ => pq.1 * pq.2)
      {pq | pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2} := by
  rintro ⟨p, q⟩ ⟨hp, hq, hpq⟩ ⟨r, s⟩ ⟨hr, hs, hrs⟩ heq
  dsimp only at heq
  have hpr : p = r ∨ p = s := by
    have hdiv : p ∣ r * s := heq ▸ dvd_mul_right p q
    exact (hp.dvd_mul.mp hdiv).imp
      (Nat.prime_dvd_prime_iff_eq hp hr).mp (Nat.prime_dvd_prime_iff_eq hp hs).mp
  rcases hpr with rfl | hps
  · have hqs := Nat.eq_of_mul_eq_mul_left hp.pos heq
    exact Prod.ext rfl hqs
  · have hqr : q = r := by
      subst s
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      simpa only [mul_comm r p] using heq
    omega

/-- The semiprimes with smaller prime factor in `P`. -/
def slicedSemiprimes (C : ℕ) (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (semiprimePairs C P X).image fun pq => pq.1 * pq.2

theorem slicedSemiprimes_subset_E2 (C : ℕ) (P : Finset ℕ) (X : ℕ) :
    ↑(slicedSemiprimes C P X) ⊆ E2 C := by
  intro n hn
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨_, hp, hq, hpC, hpq, _⟩ := Finset.mem_filter.mp hpq
  exact ⟨p, q, hp, hq, ne_of_lt hpq, hpC, lt_trans hpC hpq, rfl⟩

/-- The weighted semiprime sum is an exact sum over prime pairs. -/
theorem sum_slicedSemiprimes (C : ℕ) (P : Finset ℕ) (X : ℕ) (w : ℕ → ℝ) :
    ∑ n ∈ slicedSemiprimes C P X, w n =
      ∑ pq ∈ semiprimePairs C P X, w (pq.1 * pq.2) := by
  apply Finset.sum_image
  intro pq hpq rs hrs heq
  have hpq' := (Finset.mem_filter.mp hpq).2
  have hrs' := (Finset.mem_filter.mp hrs).2
  exact prime_pair_mul_injective ⟨hpq'.1, hpq'.2.1, hpq'.2.2.2.1⟩
    ⟨hrs'.1, hrs'.2.1, hrs'.2.2.2.1⟩ heq

/-- Expanding the smaller prime first gives exactly the prime sums to which
distribution estimates will be applied. No asymptotic approximation is made. -/
theorem sum_slicedSemiprimes_eq_prime_slices
    (C : ℕ) (P : Finset ℕ) (X : ℕ) (w : ℕ → ℝ) :
    ∑ n ∈ slicedSemiprimes C P X, w n =
      ∑ p ∈ P.filter (fun p => p.Prime ∧ C < p),
        ∑ q ∈ (Finset.Ioc p (X / p)).filter Nat.Prime, w (p * q) := by
  rw [sum_slicedSemiprimes]
  unfold semiprimePairs
  rw [Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hpP
  by_cases hp : p.Prime ∧ C < p
  · rw [if_pos hp]
    have hfilter :
        (Finset.range (X + 1)).filter
          (fun q => p.Prime ∧ q.Prime ∧ C < p ∧ p < q ∧ p * q ≤ X) =
        (Finset.Ioc p (X / p)).filter Nat.Prime := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
      constructor
      · rintro ⟨_, _, hq, _, hpq, hmul⟩
        exact ⟨⟨hpq, (Nat.le_div_iff_mul_le hp.1.pos).mpr (by simpa [mul_comm] using hmul)⟩, hq⟩
      · rintro ⟨⟨hpq, hqX⟩, hq⟩
        have hmul := (Nat.le_div_iff_mul_le hp.1.pos).mp hqX
        have hqle : q ≤ X := (Nat.div_le_self X p).trans' hqX
        exact ⟨by omega, hp.1, hq, hp.2, hpq, by simpa [mul_comm] using hmul⟩
    rw [← hfilter, Finset.sum_filter]
  · simp only [if_neg hp]
    apply Finset.sum_eq_zero
    intro q hq
    exact if_neg (fun h => hp ⟨h.1, h.2.2.1⟩)

end Erdos964
