import ErdosProblems.Erdos1188.AssignmentCounting

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# An elementary prime sequence for large arithmetic frames
-/

namespace Erdos1188

open scoped BigOperators

noncomputable section

abbrev nthPrime (i : ℕ) : ℕ := Nat.nth Nat.Prime i

@[simp] theorem nthPrime_prime (i : ℕ) : Nat.Prime (nthPrime i) :=
  Nat.prime_nth_prime i

theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

/-- Bertrand's postulate bounds each next prime by twice its predecessor. -/
theorem nthPrime_succ_le_two_mul (i : ℕ) :
    nthPrime (i + 1) ≤ 2 * nthPrime i := by
  have hnonzero : nthPrime i ≠ 0 := (nthPrime_prime i).ne_zero
  obtain ⟨p, hp, hip, hp2⟩ := Nat.bertrand (nthPrime i) hnonzero
  have hleP : nthPrime (i + 1) ≤ p :=
    (Nat.isLeast_nth_of_infinite Nat.infinite_setOf_prime (i + 1)).2 <| by
      refine ⟨hp, ?_⟩
      intro k hk
      have hki : k ≤ i := Nat.le_of_lt_succ (by simpa using hk)
      exact lt_of_le_of_lt (nthPrime_strictMono.monotone hki) hip
  exact le_trans hleP hp2

private theorem nthPrime_five_eq_thirteen : nthPrime 5 = 13 := by
  have hp : Nat.Prime 13 := by norm_num
  have h := Nat.nth_count hp
  have hc : Nat.count Nat.Prime 13 = 5 := by decide
  rw [hc] at h
  exact h

/-- From the fifth indexed prime onward, the crude exponential bound
`p_i ≤ 2^(i-1)` follows by Bertrand induction. -/
theorem nthPrime_le_two_pow_pred {i : ℕ} (hi : 5 ≤ i) :
    nthPrime i ≤ 2 ^ (i - 1) := by
  induction i, hi using Nat.le_induction with
  | base => norm_num [nthPrime_five_eq_thirteen]
  | succ i hi ih =>
      calc
        nthPrime (i + 1) ≤ 2 * nthPrime i := nthPrime_succ_le_two_mul i
        _ ≤ 2 * 2 ^ (i - 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ ((i + 1) - 1) := by
          rw [Nat.succ_sub_one]
          calc
            2 * 2 ^ (i - 1) = 2 ^ (i - 1) * 2 := Nat.mul_comm _ _
            _ = 2 ^ ((i - 1) + 1) := (pow_succ 2 (i - 1)).symm
            _ = 2 ^ i := by congr 1 <;> omega

/-- Every indexed prime has enough earlier subsets for its nonzero residues. -/
theorem nthPrime_sub_one_le_two_pow (i : ℕ) :
    nthPrime i - 1 ≤ 2 ^ i := by
  by_cases hi : i < 5
  · interval_cases i <;>
      simp [nthPrime, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
        Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven,
        Nat.nth_prime_four_eq_eleven]
  · have h5 : 5 ≤ i := by omega
    have hbound := nthPrime_le_two_pow_pred h5
    have hp : 2 ^ (i - 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (Nat.sub_le i 1)
    omega

/-- Distinct indexed primes are pairwise coprime. -/
theorem nthPrime_pairwise_coprime :
    Pairwise (Function.onFun Nat.Coprime nthPrime) := by
  intro i j hij
  change Nat.Coprime (nthPrime i) (nthPrime j)
  rw [Nat.coprime_primes (nthPrime_prime i) (nthPrime_prime j)]
  exact fun h => hij (nthPrime_strictMono.injective h)

/-- Append one new prime as the greatest coordinate after the first `m`
indexed primes. -/
def extendedPrimeFactors (m P : ℕ) : Fin (m + 1) → ℕ :=
  Fin.lastCases P (fun i : Fin m => nthPrime i.val)

@[simp] theorem extendedPrimeFactors_last (m P : ℕ) :
    extendedPrimeFactors m P (Fin.last m) = P := by
  simp [extendedPrimeFactors]

@[simp] theorem extendedPrimeFactors_castSucc (m P : ℕ) (i : Fin m) :
    extendedPrimeFactors m P i.castSucc = nthPrime i.val := by
  simp [extendedPrimeFactors]

theorem extendedPrimeFactors_prime (m P : ℕ) (hP : Nat.Prime P) :
    ∀ i, Nat.Prime (extendedPrimeFactors m P i) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [extendedPrimeFactors] using hP
  · simpa [extendedPrimeFactors] using nthPrime_prime j.val

theorem extendedPrimeFactors_injective (m P : ℕ)
    (hbase : ∀ i : Fin m, nthPrime i.val < P) :
    Function.Injective (extendedPrimeFactors m P) := by
  intro i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · intro j
    refine Fin.lastCases (fun _ => rfl) (fun b h => ?_) j
    simp only [extendedPrimeFactors, Fin.lastCases_last,
      Fin.lastCases_castSucc] at h
    exact False.elim ((ne_of_lt (hbase b)) h.symm)
  · intro j
    refine Fin.lastCases (fun h => ?_) (fun b h => ?_) j
    · simp only [extendedPrimeFactors, Fin.lastCases_last,
        Fin.lastCases_castSucc] at h
      exact False.elim ((ne_of_lt (hbase a)) h)
    simp only [extendedPrimeFactors, Fin.lastCases_castSucc] at h
    have hab : a.val = b.val := nthPrime_strictMono.injective h
    exact Fin.ext hab

theorem extendedPrimeFactors_pairwise_coprime (m P : ℕ)
    (hP : Nat.Prime P) (hbase : ∀ i : Fin m, nthPrime i.val < P) :
    Pairwise (Function.onFun Nat.Coprime (extendedPrimeFactors m P)) := by
  intro i j hij
  change Nat.Coprime (extendedPrimeFactors m P i) (extendedPrimeFactors m P j)
  rw [Nat.coprime_primes (extendedPrimeFactors_prime m P hP i)
    (extendedPrimeFactors_prime m P hP j)]
  exact fun h => hij (extendedPrimeFactors_injective m P hbase h)

/-- The first `m` indexed primes lie below `2^(m-2)` once `m≥6`. -/
theorem basePrimes_le_quarterCapacity {m : ℕ} (hm : 6 ≤ m) (i : Fin m) :
    nthPrime i.val ≤ 2 ^ (m - 2) := by
  have hi : i.val ≤ m - 1 := by omega
  have hmono : nthPrime i.val ≤ nthPrime (m - 1) :=
    nthPrime_strictMono.monotone hi
  have h5 : 5 ≤ m - 1 := by omega
  have hb := nthPrime_le_two_pow_pred h5
  have he : (m - 1) - 1 = m - 2 := by omega
  rw [he] at hb
  exact le_trans hmono hb

/-- For every `m≥6`, Bertrand supplies a new final prime between one quarter
and one half of the subset capacity, and F-010 gives the corresponding exact
binomial lower bound. -/
theorem exists_large_prime_frame_count (m : ℕ) (hm : 6 ≤ m) :
    ∃ P : ℕ, Nat.Prime P ∧
      2 ^ (m - 2) < P ∧ P ≤ 2 ^ (m - 1) ∧
      (2 ^ m - 1).choose (P - 1) ≤
        coveringCount (P * ∏ i : Fin m, nthPrime i.val) := by
  let t := 2 ^ (m - 2)
  have ht0 : t ≠ 0 := pow_ne_zero _ (by decide)
  obtain ⟨P, hP, hPt, hP2⟩ := Nat.bertrand t ht0
  have hupper : P ≤ 2 ^ (m - 1) := by
    calc
      P ≤ 2 * t := hP2
      _ = 2 ^ (m - 1) := by
        simp only [t]
        calc
          2 * 2 ^ (m - 2) = 2 ^ (m - 2) * 2 := Nat.mul_comm _ _
          _ = 2 ^ ((m - 2) + 1) := (pow_succ 2 (m - 2)).symm
          _ = 2 ^ (m - 1) := by congr 1 <;> omega
  let q := extendedPrimeFactors m P
  have hbase : ∀ i : Fin m, nthPrime i.val < P := fun i =>
    lt_of_le_of_lt (basePrimes_le_quarterCapacity hm i) hPt
  have hqprime : ∀ i, Nat.Prime (q i) := extendedPrimeFactors_prime m P hP
  letI : (i : Fin (m + 1)) → NeZero (q i) := fun i => ⟨(hqprime i).ne_zero⟩
  have hq : ∀ i, 2 ≤ q i := fun i => (hqprime i).two_le
  have hcop := extendedPrimeFactors_pairwise_coprime m P hP hbase
  have hcap : ∀ i : Fin (m + 1), q i - 1 ≤ 2 ^ i.val := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [q, extendedPrimeFactors_last, Fin.val_last]
      have hmexp : m - 1 < m := by omega
      have hpPow : 2 ^ (m - 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (le_of_lt hmexp)
      omega
    · simpa [q] using nthPrime_sub_one_le_two_pow j.val
  have hcount := choose_le_coveringCount q (by omega) hq hcop (Fin.last m)
    (fun i => Fin.le_last i) hcap
  refine ⟨P, hP, hPt, hupper, ?_⟩
  simpa [q, Fin.prod_univ_castSucc, Nat.mul_comm] using hcount

/-- The stronger version counts every injective assignment, giving a descending
factorial rather than merely a binomial coefficient. -/
theorem exists_large_prime_frame_descFactorial_count (m : ℕ) (hm : 6 ≤ m) :
    ∃ P : ℕ, Nat.Prime P ∧
      2 ^ (m - 2) < P ∧ P ≤ 2 ^ (m - 1) ∧
      (2 ^ m - 1).descFactorial (P - 1) ≤
        coveringCount (P * ∏ i : Fin m, nthPrime i.val) := by
  let t := 2 ^ (m - 2)
  have ht0 : t ≠ 0 := pow_ne_zero _ (by decide)
  obtain ⟨P, hP, hPt, hP2⟩ := Nat.bertrand t ht0
  have hupper : P ≤ 2 ^ (m - 1) := by
    calc
      P ≤ 2 * t := hP2
      _ = 2 ^ (m - 1) := by
        simp only [t]
        calc
          2 * 2 ^ (m - 2) = 2 ^ (m - 2) * 2 := Nat.mul_comm _ _
          _ = 2 ^ ((m - 2) + 1) := (pow_succ 2 (m - 2)).symm
          _ = 2 ^ (m - 1) := by congr 1 <;> omega
  let q := extendedPrimeFactors m P
  have hbase : ∀ i : Fin m, nthPrime i.val < P := fun i =>
    lt_of_le_of_lt (basePrimes_le_quarterCapacity hm i) hPt
  have hqprime : ∀ i, Nat.Prime (q i) := extendedPrimeFactors_prime m P hP
  letI : (i : Fin (m + 1)) → NeZero (q i) := fun i => ⟨(hqprime i).ne_zero⟩
  have hq : ∀ i, 2 ≤ q i := fun i => (hqprime i).two_le
  have hcop := extendedPrimeFactors_pairwise_coprime m P hP hbase
  have hcap : ∀ i : Fin (m + 1), q i - 1 ≤ 2 ^ i.val := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [q, extendedPrimeFactors_last, Fin.val_last]
      have hmexp : m - 1 < m := by omega
      have hpPow : 2 ^ (m - 1) ≤ 2 ^ m :=
        Nat.pow_le_pow_right (by decide) (le_of_lt hmexp)
      omega
    · simpa [q] using nthPrime_sub_one_le_two_pow j.val
  have hcount := descFactorial_le_coveringCount q (by omega) hq hcop (Fin.last m)
    (fun i => Fin.le_last i) hcap
  refine ⟨P, hP, hPt, hupper, ?_⟩
  simpa [q, Fin.prod_univ_castSucc, Nat.mul_comm] using hcount

end

end Erdos1188
