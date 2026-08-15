import ErdosProblems.Erdos321.BadPrimes
import ErdosProblems.Erdos321.SignedPairs

namespace Erdos321

/-- Prime factors of `n` which are at least `Y`. -/
def largePrimeFactors (Y n : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p => Y ≤ p

/-- The product of the large distinct prime factors gives an exact power bound
on their number. -/
theorem pow_card_largePrimeFactors_le {Y n : ℕ} (hn : n ≠ 0) :
    Y ^ (largePrimeFactors Y n).card ≤ n := by
  let s := largePrimeFactors Y n
  have hs : s ⊆ n.primeFactors := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hpow : Y ^ s.card ≤ ∏ p ∈ s, p :=
    Finset.pow_card_le_prod s id Y (by
      intro p hp
      exact (Finset.mem_filter.mp hp).2)
  have hprodDvd : (∏ p ∈ s, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset s n.primeFactors id hs).trans
      (Nat.prod_primeFactors_dvd n)
  exact hpow.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprodDvd)

/-- Union of all large prime divisors of canonical signed numerators on `B`. -/
def relationPrimeFactors (t Y : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (disjointPairs B).biUnion fun r =>
    largePrimeFactors Y (factorialNumerator t r.1 r.2).natAbs

/-- The finite set of bad fibre primes in `[t+1,X]`. -/
noncomputable def badPrimeSet (t X : ℕ) (B : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (t + 1) X).filter fun p =>
    p.Prime ∧ ¬ ModularlySeparated p B

/-- Every bad prime above `Y` occurs among the prime divisors of one of the
`3^|B|` canonical signed numerators. -/
theorem badPrimeSet_subset_relationPrimeFactors
    {t X Y : ℕ} {B : Finset ℕ} (hY : Y ≤ t + 1)
    (hBsub : B ⊆ Finset.Icc 1 t) (hB : Valid B) :
    badPrimeSet t X B ⊆ relationPrimeFactors t Y B := by
  classical
  intro p hpBad
  rw [badPrimeSet] at hpBad
  have hpData := Finset.mem_filter.mp hpBad
  have hpIcc := Finset.mem_Icc.mp hpData.1
  have hpPrime := hpData.2.1
  have htp : t < p := by omega
  obtain ⟨U, hU, V, hV, hUV, hNumNe, hpDvd⟩ :=
    bad_prime_dvd_some_factorialNumerator hpPrime htp hBsub hB hpData.2.2
  let U' := U \ V
  let V' := V \ U
  have hPair : Sigma.mk U' V' ∈ disjointPairs B :=
    sdiff_pair_mem_disjointPairs (Finset.mem_powerset.mp hU)
      (Finset.mem_powerset.mp hV)
  have hNumEq : factorialNumerator t U' V' = factorialNumerator t U V := by
    exact factorialNumerator_sdiff t U V
  have hNumNe' : factorialNumerator t U' V' ≠ 0 := hNumEq ▸ hNumNe
  have hpDvd' : (p : ℤ) ∣ factorialNumerator t U' V' := hNumEq ▸ hpDvd
  have hpDvdNat : p ∣ (factorialNumerator t U' V').natAbs := by
    simpa using (Int.natAbs_dvd_natAbs.mpr hpDvd')
  have hpMemFactors : p ∈ (factorialNumerator t U' V').natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpPrime, hpDvdNat, by simpa using hNumNe'⟩
  rw [relationPrimeFactors, Finset.mem_biUnion]
  refine ⟨Sigma.mk U' V', hPair, ?_⟩
  rw [largePrimeFactors, Finset.mem_filter]
  exact ⟨hpMemFactors, hY.trans hpIcc.1⟩

/-- Consequently, the number of bad primes is at most the sum of the numbers
of large prime factors of the canonical signed numerators. -/
theorem card_badPrimeSet_le_sum_card_largePrimeFactors
    {t X Y : ℕ} {B : Finset ℕ} (hY : Y ≤ t + 1)
    (hBsub : B ⊆ Finset.Icc 1 t) (hB : Valid B) :
    (badPrimeSet t X B).card ≤
      ∑ r ∈ disjointPairs B,
        (largePrimeFactors Y (factorialNumerator t r.1 r.2).natAbs).card := by
  classical
  exact (Finset.card_le_card
    (badPrimeSet_subset_relationPrimeFactors hY hBsub hB)).trans
      Finset.card_biUnion_le

/-- Exact logarithm-free bad-prime bound.  If `B` is nonempty and valid in
`[1,t]`, then the `Y`-power of the number of bad primes is bounded by one copy
of `|B| t!` for each of the `3^|B|` signed coefficient vectors. -/
theorem pow_card_badPrimeSet_le
    {t X Y : ℕ} {B : Finset ℕ} (hYpos : 0 < Y) (hY : Y ≤ t + 1)
    (hBne : B.Nonempty) (hBsub : B ⊆ Finset.Icc 1 t) (hB : Valid B) :
    Y ^ (badPrimeSet t X B).card ≤
      (B.card * t.factorial) ^ (3 ^ B.card) := by
  classical
  let M := B.card * t.factorial
  have hMpos : 0 < M := Nat.mul_pos (Finset.card_pos.mpr hBne) (Nat.factorial_pos t)
  have hCard := card_badPrimeSet_le_sum_card_largePrimeFactors
    (X := X) hY hBsub hB
  have hPowCard : Y ^ (badPrimeSet t X B).card ≤
      Y ^ (∑ r ∈ disjointPairs B,
        (largePrimeFactors Y (factorialNumerator t r.1 r.2).natAbs).card) :=
    Nat.pow_le_pow_right hYpos hCard
  have hEach : ∀ r ∈ disjointPairs B,
      Y ^ (largePrimeFactors Y (factorialNumerator t r.1 r.2).natAbs).card ≤ M := by
    intro r hr
    have hrData := Finset.mem_sigma.mp hr
    have hUsub : r.1 ⊆ B := Finset.mem_powerset.mp hrData.1
    have hVcomp : r.2 ⊆ B \ r.1 := Finset.mem_powerset.mp hrData.2
    have hVsub : r.2 ⊆ B := hVcomp.trans Finset.sdiff_subset
    have hDisjoint : Disjoint r.1 r.2 := by
      rw [Finset.disjoint_left]
      intro a haU haV
      exact (Finset.mem_sdiff.mp (hVcomp haV)).2 haU
    by_cases hNum : factorialNumerator t r.1 r.2 = 0
    · have hMone : 1 ≤ M := hMpos
      simpa [largePrimeFactors, hNum] using hMone
    · exact (pow_card_largePrimeFactors_le
        (by simpa using hNum)).trans
          (factorialNumerator_natAbs_le hUsub hVsub hDisjoint)
  calc
    Y ^ (badPrimeSet t X B).card ≤
        Y ^ (∑ r ∈ disjointPairs B,
          (largePrimeFactors Y (factorialNumerator t r.1 r.2).natAbs).card) := hPowCard
    _ = ∏ r ∈ disjointPairs B,
        Y ^ (largePrimeFactors Y (factorialNumerator t r.1 r.2).natAbs).card := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ _r ∈ disjointPairs B, M := by
      exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _ ) hEach
    _ = M ^ (disjointPairs B).card := Finset.prod_const M
    _ = M ^ (3 ^ B.card) := by rw [card_disjointPairs]

/-- Bad modular primes in an arbitrary interval `[L,X]`, decoupling the
prime cutoff from the cofactor bound. -/
noncomputable def badPrimeSetFrom (L X : ℕ) (B : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc L X).filter fun p =>
    p.Prime ∧ ¬ ModularlySeparated p B

/-- General interval version of the bad-prime divisor inclusion. -/
theorem badPrimeSetFrom_subset_relationPrimeFactors
    {t L X Y : ℕ} {B : Finset ℕ} (htL : t < L) (hY : Y ≤ L)
    (hBsub : B ⊆ Finset.Icc 1 t) (hB : Valid B) :
    badPrimeSetFrom L X B ⊆ relationPrimeFactors t Y B := by
  classical
  intro p hpBad
  rw [badPrimeSetFrom] at hpBad
  have hpData := Finset.mem_filter.mp hpBad
  have hpIcc := Finset.mem_Icc.mp hpData.1
  have hpPrime := hpData.2.1
  have htp : t < p := htL.trans_le hpIcc.1
  obtain ⟨U, hU, V, hV, hUV, hNumNe, hpDvd⟩ :=
    bad_prime_dvd_some_factorialNumerator hpPrime htp hBsub hB hpData.2.2
  let U' := U \ V
  let V' := V \ U
  have hPair : Sigma.mk U' V' ∈ disjointPairs B :=
    sdiff_pair_mem_disjointPairs (Finset.mem_powerset.mp hU)
      (Finset.mem_powerset.mp hV)
  have hNumEq : factorialNumerator t U' V' = factorialNumerator t U V :=
    factorialNumerator_sdiff t U V
  have hNumNe' : factorialNumerator t U' V' ≠ 0 := hNumEq ▸ hNumNe
  have hpDvd' : (p : ℤ) ∣ factorialNumerator t U' V' := hNumEq ▸ hpDvd
  have hpDvdNat : p ∣ (factorialNumerator t U' V').natAbs := by
    simpa using (Int.natAbs_dvd_natAbs.mpr hpDvd')
  have hpMemFactors : p ∈ (factorialNumerator t U' V').natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpPrime, hpDvdNat, by simpa using hNumNe'⟩
  rw [relationPrimeFactors, Finset.mem_biUnion]
  refine ⟨Sigma.mk U' V', hPair, ?_⟩
  rw [largePrimeFactors, Finset.mem_filter]
  exact ⟨hpMemFactors, hY.trans hpIcc.1⟩

/-- Exact power count for bad primes in `[L,X]`. -/
theorem pow_card_badPrimeSetFrom_le
    {t L X Y : ℕ} {B : Finset ℕ}
    (htL : t < L) (hYpos : 0 < Y) (hY : Y ≤ L)
    (hBne : B.Nonempty) (hBsub : B ⊆ Finset.Icc 1 t) (hB : Valid B) :
    Y ^ (badPrimeSetFrom L X B).card ≤
      (B.card * t.factorial) ^ (3 ^ B.card) := by
  classical
  let M := B.card * t.factorial
  have hMpos : 0 < M := Nat.mul_pos (Finset.card_pos.mpr hBne) (Nat.factorial_pos t)
  have hSubset := badPrimeSetFrom_subset_relationPrimeFactors
    (X := X) htL hY hBsub hB
  have hCard : (badPrimeSetFrom L X B).card ≤
      ∑ r ∈ disjointPairs B,
        (largePrimeFactors Y (factorialNumerator t r.1 r.2).natAbs).card :=
    (Finset.card_le_card hSubset).trans Finset.card_biUnion_le
  have hPowCard : Y ^ (badPrimeSetFrom L X B).card ≤
      Y ^ (∑ r ∈ disjointPairs B,
        (largePrimeFactors Y (factorialNumerator t r.1 r.2).natAbs).card) :=
    Nat.pow_le_pow_right hYpos hCard
  have hEach : ∀ r ∈ disjointPairs B,
      Y ^ (largePrimeFactors Y (factorialNumerator t r.1 r.2).natAbs).card ≤ M := by
    intro r hr
    have hrData := Finset.mem_sigma.mp hr
    have hUsub : r.1 ⊆ B := Finset.mem_powerset.mp hrData.1
    have hVcomp : r.2 ⊆ B \ r.1 := Finset.mem_powerset.mp hrData.2
    have hVsub : r.2 ⊆ B := hVcomp.trans Finset.sdiff_subset
    have hDisjoint : Disjoint r.1 r.2 := by
      rw [Finset.disjoint_left]
      intro a haU haV
      exact (Finset.mem_sdiff.mp (hVcomp haV)).2 haU
    by_cases hNum : factorialNumerator t r.1 r.2 = 0
    · have hMone : 1 ≤ M := hMpos
      simpa [largePrimeFactors, hNum] using hMone
    · exact (pow_card_largePrimeFactors_le (by simpa using hNum)).trans
        (factorialNumerator_natAbs_le hUsub hVsub hDisjoint)
  calc
    Y ^ (badPrimeSetFrom L X B).card ≤
        Y ^ (∑ r ∈ disjointPairs B,
          (largePrimeFactors Y (factorialNumerator t r.1 r.2).natAbs).card) := hPowCard
    _ = ∏ r ∈ disjointPairs B,
        Y ^ (largePrimeFactors Y (factorialNumerator t r.1 r.2).natAbs).card := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ _r ∈ disjointPairs B, M := by
      exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hEach
    _ = M ^ (disjointPairs B).card := Finset.prod_const M
    _ = M ^ (3 ^ B.card) := by rw [card_disjointPairs]

end Erdos321
