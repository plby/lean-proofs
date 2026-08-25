import ErdosProblems.Erdos964.Admissibility
import ErdosProblems.Erdos964.SemiprimeCounts
import BoundedGaps.Maynard.Distribution

/-!
# Explicit distribution errors for prime slices of the semiprime sequence

These finite bounds use the actual prime-counting discrepancy from the
installed Bombieri--Vinogradov development. The permitted smaller prime
factors may depend on the endpoint. No assertion of the three-form sieve
theorem is made here.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

def primeIntervalCount (l u m a : ℕ) : ℕ :=
  ((Finset.Ioc l u).filter (fun q => q.Prime ∧ q ≡ a [MOD m])).card

theorem cast_primeIntervalCount (l u m a : ℕ) (hlu : l ≤ u) :
    (primeIntervalCount l u m a : ℝ) =
      (primeCountUpTo u m a : ℝ) - (primeCountUpTo l m a : ℝ) := by
  have hinterval : Finset.Ioc l u = Finset.Ico (l + 1) (u + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  unfold primeIntervalCount primeCountUpTo
  rw [hinterval, Finset.natCast_card_filter, Finset.natCast_card_filter,
    Finset.natCast_card_filter]
  exact Finset.sum_Ico_eq_sub _ (by omega)

theorem progressionDiscrepancy_le_max_of_coprime (X m a : ℕ)
    (hm : 0 < m) (ha : a.Coprime m) :
    progressionDiscrepancy X m a ≤ maxProgressionDiscrepancy X m := by
  have hcop : (a % m).Coprime m := by
    change (a % m).gcd m = 1
    rw [(Nat.mod_modEq a m).gcd_eq]
    exact ha
  have hmem : a % m ∈ coprimeResidues m :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt a hm), hcop⟩
  simpa only [progressionDiscrepancy, primeCountUpTo, Nat.mod_mod] using
    progressionDiscrepancy_le_max (x := X) hm hmem

theorem primeIntervalCount_error_le (l u m a : ℕ)
    (hlu : l ≤ u) (hm : 0 < m) (ha : a.Coprime m) :
    |(primeIntervalCount l u m a : ℝ) -
      ((primeCountTotal u : ℝ) - primeCountTotal l) / m.totient| ≤
      maxProgressionDiscrepancy u m + maxProgressionDiscrepancy l m := by
  rw [cast_primeIntervalCount l u m a hlu]
  calc
    _ = |((primeCountUpTo u m a : ℝ) - (primeCountTotal u : ℝ) / m.totient) -
        ((primeCountUpTo l m a : ℝ) - (primeCountTotal l : ℝ) / m.totient)| := by
      congr 1
      ring
    _ ≤ progressionDiscrepancy u m a + progressionDiscrepancy l m a := by
      exact abs_sub _ _
    _ ≤ _ := add_le_add (progressionDiscrepancy_le_max_of_coprime u m a hm ha)
      (progressionDiscrepancy_le_max_of_coprime l m a hm ha)

/-- Count the sliced semiprimes in a fixed arithmetic progression. -/
def slicedSemiprimeCount (C : ℕ) (P : Finset ℕ) (X m a : ℕ) : ℕ :=
  ((slicedSemiprimes C P X).filter (fun n => n ≡ a [MOD m])).card

theorem prime_slice_count_eq (p X m a t : ℕ)
    (hpm : p.Coprime m) (ht : p * t ≡ a [MOD m]) :
    (∑ q ∈ (Finset.Ioc p (X / p)).filter Nat.Prime,
      if p * q ≡ a [MOD m] then (1 : ℝ) else 0) =
      primeIntervalCount p (X / p) m t := by
  have heq q : p * q ≡ a [MOD m] ↔ q ≡ t [MOD m] := by
    constructor
    · intro hq
      exact (hq.trans ht.symm).cancel_left_of_coprime hpm.symm
    · intro hq
      exact (hq.mul_left p).trans ht
  simp_rw [heq]
  rw [← Finset.natCast_card_filter]
  unfold primeIntervalCount
  congr 2
  ext q
  simp only [Finset.mem_filter, and_assoc]

theorem cast_slicedSemiprimeCount_eq (C : ℕ) (P : Finset ℕ) (X m a : ℕ)
    (t : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ C < p ∧ p.Coprime m)
    (ht : ∀ p ∈ P, p * t p ≡ a [MOD m]) :
    (slicedSemiprimeCount C P X m a : ℝ) =
      ∑ p ∈ P, (primeIntervalCount p (X / p) m (t p) : ℝ) := by
  unfold slicedSemiprimeCount
  rw [Finset.natCast_card_filter, sum_slicedSemiprimes_eq_prime_slices]
  have hfilter : P.filter (fun p => p.Prime ∧ C < p) = P := by
    exact Finset.filter_eq_self.mpr (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩)
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro p hp
  exact prime_slice_count_eq p X m a (t p) (hP p hp).2.2 (ht p hp)

/-- The exact finite error bound for semiprimes obtained by slicing over their
smaller prime factor. The right side contains only known prime discrepancies. -/
theorem slicedSemiprimeCount_error_le (C : ℕ) (P : Finset ℕ) (X m a : ℕ)
    (hm : 0 < m) (ha : a.Coprime m)
    (hP : ∀ p ∈ P, p.Prime ∧ C < p ∧ p * p ≤ X ∧ p.Coprime m) :
    |(slicedSemiprimeCount C P X m a : ℝ) -
      ∑ p ∈ P, ((primeCountTotal (X / p) : ℝ) - primeCountTotal p) / m.totient| ≤
      ∑ p ∈ P, (maxProgressionDiscrepancy (X / p) m +
        maxProgressionDiscrepancy p m) := by
  classical
  have hroots : ∀ p, ∃ t, p ∈ P → p * t ≡ a [MOD m] := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨t, ht⟩ := exists_affine_modEq p 0 a m hm (hP p hp).2.2.2
      exact ⟨t, fun _ => by simpa only [add_zero] using ht⟩
    · exact ⟨0, fun h => (hp h).elim⟩
  choose t ht using hroots
  rw [cast_slicedSemiprimeCount_eq C P X m a t
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1, (hP p hp).2.2.2⟩) ht,
    ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hprod : (p * t p).Coprime m := by
    change (p * t p).gcd m = 1
    rw [(ht p hp).gcd_eq]
    exact ha
  have htm : (t p).Coprime m := hprod.of_dvd_left (dvd_mul_left _ _)
  exact primeIntervalCount_error_le p (X / p) m (t p)
    ((Nat.le_div_iff_mul_le (hP p hp).1.pos).mpr (hP p hp).2.2.1) hm htm

end Erdos964
