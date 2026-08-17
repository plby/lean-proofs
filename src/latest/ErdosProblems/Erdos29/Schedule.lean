import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The explicit radix schedule for Erdős problem 29

For the digit construction we need, at level `i`, a prime which is larger than
`i + 11` but at most twice that number.  `primeAt` is the least such prime in
the indicated *finite* interval.  Thus this is an executable bounded search;
Bertrand's postulate is used only to prove that its search interval is nonempty.

The radix at level `i` is the square of this prime, and `place k` is the
product of the first `k` radices.
-/

namespace Erdos29

open scoped BigOperators

/-- The finite search space used to choose the prime at level `i`. -/
def primeCandidates (i : ℕ) : Finset ℕ :=
  (Finset.Icc (i + 12) (2 * (i + 11))).filter Nat.Prime

theorem primeCandidates_nonempty (i : ℕ) : (primeCandidates i).Nonempty := by
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.bertrand (i + 11) (by omega)
  refine ⟨p, ?_⟩
  simp only [primeCandidates, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, hhi⟩, hp⟩

/--
The least prime strictly larger than `i + 11` and at most `2 * (i + 11)`.

This definition is computational: `Finset.min'` searches the bounded finset
`primeCandidates i`; its proof argument is erased by code generation.
-/
def primeAt (i : ℕ) : ℕ :=
  (primeCandidates i).min' (primeCandidates_nonempty i)

theorem primeAt_mem (i : ℕ) : primeAt i ∈ primeCandidates i := by
  exact Finset.min'_mem _ _

theorem primeAt_prime (i : ℕ) : Nat.Prime (primeAt i) := by
  exact (Finset.mem_filter.mp (primeAt_mem i)).2

theorem primeAt_lower (i : ℕ) : i + 11 < primeAt i := by
  have h := (Finset.mem_Icc.mp (Finset.mem_of_mem_filter (primeAt i) (primeAt_mem i))).1
  omega

theorem primeAt_ge (i : ℕ) : i + 12 ≤ primeAt i := by
  have h := primeAt_lower i
  omega

theorem primeAt_upper (i : ℕ) : primeAt i ≤ 2 * (i + 11) := by
  exact (Finset.mem_Icc.mp (Finset.mem_of_mem_filter (primeAt i) (primeAt_mem i))).2

theorem primeAt_minimal {i q : ℕ} (hqPrime : Nat.Prime q)
    (hqLower : i + 11 < q) (hqUpper : q ≤ 2 * (i + 11)) : primeAt i ≤ q := by
  apply Finset.min'_le
  simp only [primeCandidates, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, hqUpper⟩, hqPrime⟩

theorem primeAt_mono : Monotone primeAt := by
  intro i j hij
  by_cases hq : primeAt j ≤ 2 * (i + 11)
  · apply primeAt_minimal (primeAt_prime j)
    · exact lt_of_le_of_lt (Nat.add_le_add_right hij 11) (primeAt_lower j)
    · exact hq
  · exact (primeAt_upper i).trans (Nat.le_of_lt (not_le.mp hq))

theorem twelve_le_primeAt (i : ℕ) : 12 ≤ primeAt i := by
  have h := primeAt_ge i
  omega

/-- The mixed-radix base at level `i`. -/
def radix (i : ℕ) : ℕ := (primeAt i) ^ 2

theorem radix_eq (i : ℕ) : radix i = (primeAt i) ^ 2 := rfl

theorem radix_prime_sq (i : ℕ) : ∃ p : ℕ, Nat.Prime p ∧ radix i = p ^ 2 := by
  exact ⟨primeAt i, primeAt_prime i, rfl⟩

theorem radix_pos (i : ℕ) : 0 < radix i := by
  simp only [radix, pow_two]
  exact Nat.mul_pos (primeAt_prime i).pos (primeAt_prime i).pos

theorem radix_ne_zero (i : ℕ) : radix i ≠ 0 := (radix_pos i).ne'

theorem one_lt_radix (i : ℕ) : 1 < radix i := by
  have hp := twelve_le_primeAt i
  simp only [radix, pow_two]
  nlinarith

theorem radix_lower_index (i : ℕ) : (i + 12) ^ 2 ≤ radix i := by
  exact Nat.pow_le_pow_left (primeAt_ge i) 2

theorem radix_lower_factorial (i : ℕ) : (i + 1) ^ 2 ≤ radix i := by
  apply Nat.pow_le_pow_left
  have h := primeAt_ge i
  omega

theorem one_hundred_twenty_one_le_radix (i : ℕ) : 121 ≤ radix i := by
  calc
    121 = 11 ^ 2 := by norm_num
    _ ≤ radix i := Nat.pow_le_pow_left (by
      have h := primeAt_ge i
      omega) 2

theorem radix_upper (i : ℕ) : radix i ≤ 4 * (i + 11) ^ 2 := by
  calc
    radix i ≤ (2 * (i + 11)) ^ 2 := Nat.pow_le_pow_left (primeAt_upper i) 2
    _ = 4 * (i + 11) ^ 2 := by ring

theorem radix_mono : Monotone radix := by
  intro i j hij
  exact Nat.pow_le_pow_left (primeAt_mono hij) 2

/-- The place value immediately above the first `k` digits. -/
def place (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, radix i

@[simp] theorem place_zero : place 0 = 1 := by
  simp [place]

theorem place_succ (k : ℕ) : place (k + 1) = place k * radix k := by
  simp [place, Finset.prod_range_succ]

theorem place_pos (k : ℕ) : 0 < place k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show k + 1 = Nat.succ k by omega, place_succ]
      exact Nat.mul_pos ih (radix_pos k)

theorem place_ne_zero (k : ℕ) : place k ≠ 0 := (place_pos k).ne'

theorem place_lt_place_succ (k : ℕ) : place k < place (k + 1) := by
  rw [place_succ]
  exact lt_mul_of_one_lt_right (place_pos k) (one_lt_radix k)

theorem place_strictMono : StrictMono place :=
  strictMono_nat_of_lt_succ place_lt_place_succ

theorem place_mono : Monotone place := place_strictMono.monotone

theorem place_dvd_place_succ (k : ℕ) : place k ∣ place (k + 1) := by
  rw [place_succ]
  exact dvd_mul_right _ _

theorem place_dvd_place {i j : ℕ} (hij : i ≤ j) : place i ∣ place j := by
  induction hij with
  | refl => exact dvd_rfl
  | @step j _ ih => exact ih.trans (place_dvd_place_succ j)

theorem pow_radix_lower_le_place (k : ℕ) : 121 ^ k ≤ place k := by
  simp only [place]
  calc
    121 ^ k = ∏ _i ∈ Finset.range k, 121 := by simp
    _ ≤ ∏ i ∈ Finset.range k, radix i := by
      exact Finset.prod_le_prod' fun i _hi ↦ one_hundred_twenty_one_le_radix i

theorem factorial_sq_le_place (k : ℕ) : (Nat.factorial k) ^ 2 ≤ place k := by
  rw [← Finset.prod_range_add_one_eq_factorial]
  rw [← Finset.prod_pow]
  exact Finset.prod_le_prod' fun i _hi ↦ radix_lower_factorial i

/-- The place value grows at least as fast as the superexponential scale used
by the final little-o estimate. -/
theorem half_pow_le_factorial_sq (k : ℕ) : (k / 2) ^ k ≤ (Nat.factorial k) ^ 2 := by
  by_cases hm : k / 2 = 0
  · have hk : k < 2 := by omega
    interval_cases k <;> norm_num
  · have hmpos : 0 < k / 2 := Nat.pos_of_ne_zero hm
    have hmle : k / 2 ≤ k := Nat.div_le_self _ _
    have htail := Nat.factorial_mul_pow_sub_le_factorial hmle
    have hpow : (k / 2) ^ (k - k / 2) ≤ Nat.factorial k :=
      (Nat.le_mul_of_pos_left _ (Nat.factorial_pos (k / 2))).trans htail
    have hexp : k ≤ 2 * (k - k / 2) := by omega
    calc
      (k / 2) ^ k ≤ (k / 2) ^ (2 * (k - k / 2)) :=
        Nat.pow_le_pow_right hmpos hexp
      _ = ((k / 2) ^ (k - k / 2)) ^ 2 := by
        rw [pow_two, ← pow_add]
        congr 1
        omega
      _ ≤ (Nat.factorial k) ^ 2 := Nat.pow_le_pow_left hpow 2

theorem half_pow_le_place (k : ℕ) : (k / 2) ^ k ≤ place k :=
  (half_pow_le_factorial_sq k).trans (factorial_sq_le_place k)

theorem place_upper (k : ℕ) : place k ≤ (4 * (k + 11) ^ 2) ^ k := by
  simp only [place]
  calc
    (∏ i ∈ Finset.range k, radix i) ≤
        ∏ _i ∈ Finset.range k, (4 * (k + 11) ^ 2) := by
      apply Finset.prod_le_prod'
      intro i hi
      refine (radix_upper i).trans ?_
      exact Nat.mul_le_mul_left 4
        (Nat.pow_le_pow_left (by simpa using (Finset.mem_range.mp hi).le : i + 11 ≤ k + 11) 2)
    _ = (4 * (k + 11) ^ 2) ^ k := by simp

theorem index_lt_place_succ (n : ℕ) : n < place (n + 1) := by
  calc
    n < 2 ^ n := n.lt_two_pow_self
    _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ 121 ^ (n + 1) := Nat.pow_le_pow_left (by norm_num) (n + 1)
    _ ≤ place (n + 1) := pow_radix_lower_le_place (n + 1)

end Erdos29
