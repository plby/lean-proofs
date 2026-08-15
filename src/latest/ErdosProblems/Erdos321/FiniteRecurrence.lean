import ErdosProblems.Erdos321.MultiFiber
import ErdosProblems.Erdos321.PrimeFactorCount
import ErdosProblems.Erdos321.ElementaryBounds

namespace Erdos321

/-- A fixed extremizer at each finite parameter, chosen noncomputably. -/
noncomputable def chosenExtremizer (t : ℕ) : Finset ℕ :=
  Classical.choose (exists_extremizer t)

theorem chosenExtremizer_spec (t : ℕ) :
    Admissible t (chosenExtremizer t) ∧
      (chosenExtremizer t).card = extremalSize t :=
  Classical.choose_spec (exists_extremizer t)

/-- Primes above the common cofactor cutoff `T` whose quotient is `t` and for
which the chosen `t`-extremizer is modularly separated. -/
noncomputable def goodFiberPrimes (N T t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (T + 1) N).filter fun p =>
    p.Prime ∧ N / p = t ∧ ModularlySeparated p (chosenExtremizer t)

/-- Union of the good-prime classes for `1≤t≤T`. -/
noncomputable def goodPrimeIndexSet (N T : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 T).biUnion fun t => goodFiberPrimes N T t

/-- Exact self-referential finite lower recurrence supplied by the modular
multifibre construction. -/
theorem sum_extremalSize_div_over_goodPrimes_le (N T : ℕ) :
    (∑ p ∈ goodPrimeIndexSet N T, extremalSize (N / p)) ≤ extremalSize N := by
  classical
  let P := goodPrimeIndexSet N T
  let B : ℕ → Finset ℕ := fun p => chosenExtremizer (N / p)
  have unpack {p : ℕ} (hp : p ∈ P) :
      ∃ t ∈ Finset.Icc 1 T, p ∈ goodFiberPrimes N T t := by
    exact Finset.mem_biUnion.mp hp
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    obtain ⟨t, ht, hpgood⟩ := unpack hp
    exact (Finset.mem_filter.mp hpgood).2.1
  have hlarge : ∀ p ∈ P, T < p := by
    intro p hp
    obtain ⟨t, ht, hpgood⟩ := unpack hp
    exact Nat.lt_of_succ_le (Finset.mem_Icc.mp (Finset.mem_filter.mp hpgood).1).1
  have hBsub : ∀ p ∈ P, B p ⊆ Finset.Icc 1 T := by
    intro p hp b hb
    obtain ⟨t, ht, hpgood⟩ := unpack hp
    have hquot : N / p = t := (Finset.mem_filter.mp hpgood).2.2.1
    have hbIcc := Finset.mem_Icc.mp ((chosenExtremizer_spec (N / p)).1.1 hb)
    exact Finset.mem_Icc.mpr ⟨hbIcc.1, hbIcc.2.trans (hquot.le.trans (Finset.mem_Icc.mp ht).2)⟩
  have hmod : ∀ p ∈ P, ModularlySeparated p (B p) := by
    intro p hp
    obtain ⟨t, ht, hpgood⟩ := unpack hp
    have hpData := (Finset.mem_filter.mp hpgood).2
    change ModularlySeparated p (chosenExtremizer (N / p))
    rw [hpData.2.1]
    exact hpData.2.2
  have hprod : ∀ p ∈ P, ∀ b ∈ B p, p * b ≤ N := by
    intro p hp b hb
    have hbLe : b ≤ N / p := (Finset.mem_Icc.mp ((chosenExtremizer_spec (N / p)).1.1 hb)).2
    calc
      p * b ≤ p * (N / p) := Nat.mul_le_mul_left p hbLe
      _ = (N / p) * p := Nat.mul_comm _ _
      _ ≤ N := Nat.div_mul_le_self N p
  have hLower := multiFiber_card_le_extremalSize hprime hlarge hBsub hmod hprod
  simpa [P, B, chosenExtremizer_spec] using hLower

/-- All candidate primes in the quotient class `⌊N/p⌋=t`, before removing
modularly bad primes. -/
def quotientPrimes (N T t : ℕ) : Finset ℕ :=
  (Finset.Icc (T + 1) N).filter fun p => p.Prime ∧ N / p = t

private theorem goodFiberPrimes_subset_quotientPrimes (N T t : ℕ) :
    goodFiberPrimes N T t ⊆ quotientPrimes N T t := by
  classical
  intro p hp
  rw [goodFiberPrimes] at hp
  rw [quotientPrimes, Finset.mem_filter]
  have h := Finset.mem_filter.mp hp
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Candidate quotient classes are disjoint, so the good-prime recurrence can
be grouped exactly by `t`. -/
theorem sum_goodFiberPrimes_mul_extremalSize_le (N T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T,
      (goodFiberPrimes N T t).card * extremalSize t) ≤ extremalSize N := by
  classical
  have hPairwise : (↑(Finset.Icc 1 T) : Set ℕ).PairwiseDisjoint
      (goodFiberPrimes N T) := by
    intro t ht u hu htu
    change Disjoint (goodFiberPrimes N T t) (goodFiberPrimes N T u)
    rw [Finset.disjoint_left]
    intro p hpt hpu
    rw [goodFiberPrimes] at hpt hpu
    have htq := (Finset.mem_filter.mp hpt).2.2.1
    have huq := (Finset.mem_filter.mp hpu).2.2.1
    exact htu (htq.symm.trans huq)
  have hRegroup :
      (∑ p ∈ goodPrimeIndexSet N T, extremalSize (N / p)) =
        ∑ t ∈ Finset.Icc 1 T,
          (goodFiberPrimes N T t).card * extremalSize t := by
    rw [goodPrimeIndexSet, Finset.sum_biUnion hPairwise]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_const_nat
    intro p hp
    rw [goodFiberPrimes] at hp
    exact congrArg extremalSize (Finset.mem_filter.mp hp).2.2.1
  rw [← hRegroup]
  exact sum_extremalSize_div_over_goodPrimes_le N T

/-- In each quotient class, all candidate primes not selected as good belong
to the corresponding bad-prime set. -/
theorem card_quotientPrimes_sub_bad_le_good
    {N T t : ℕ} (ht : t ∈ Finset.Icc 1 T) :
    (quotientPrimes N T t).card -
      (badPrimeSet t N (chosenExtremizer t)).card ≤
        (goodFiberPrimes N T t).card := by
  classical
  let Q := quotientPrimes N T t
  let G := goodFiberPrimes N T t
  have hGQ : G ⊆ Q := goodFiberPrimes_subset_quotientPrimes N T t
  have hDiffBad : Q \ G ⊆ badPrimeSet t N (chosenExtremizer t) := by
    intro p hpDiff
    have hpQ : p ∈ Q := (Finset.mem_sdiff.mp hpDiff).1
    have hpNotG : p ∉ G := (Finset.mem_sdiff.mp hpDiff).2
    change p ∈ quotientPrimes N T t at hpQ
    change p ∉ goodFiberPrimes N T t at hpNotG
    rw [quotientPrimes] at hpQ
    have hpData := Finset.mem_filter.mp hpQ
    rw [badPrimeSet, Finset.mem_filter]
    refine ⟨Finset.mem_Icc.mpr ⟨?_, (Finset.mem_Icc.mp hpData.1).2⟩,
      hpData.2.1, ?_⟩
    · have hpLower := (Finset.mem_Icc.mp hpData.1).1
      have htUpper := (Finset.mem_Icc.mp ht).2
      omega
    · intro hMod
      apply hpNotG
      rw [goodFiberPrimes, Finset.mem_filter]
      exact ⟨hpData.1, hpData.2.1, hpData.2.2, hMod⟩
  have hDiffCard : (Q \ G).card ≤
      (badPrimeSet t N (chosenExtremizer t)).card :=
    Finset.card_le_card hDiffBad
  have hCardEq : (Q \ G).card = Q.card - G.card :=
    Finset.card_sdiff_of_subset hGQ
  dsimp [Q, G] at hDiffCard hCardEq
  omega

/-- Exact recurrence with an explicit bad-prime subtraction in every quotient
class. -/
theorem sum_quotient_sub_bad_mul_extremalSize_le (N T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T,
      ((quotientPrimes N T t).card -
        (badPrimeSet t N (chosenExtremizer t)).card) * extremalSize t) ≤
      extremalSize N := by
  calc
    (∑ t ∈ Finset.Icc 1 T,
      ((quotientPrimes N T t).card -
        (badPrimeSet t N (chosenExtremizer t)).card) * extremalSize t) ≤
        ∑ t ∈ Finset.Icc 1 T,
          (goodFiberPrimes N T t).card * extremalSize t := by
      apply Finset.sum_le_sum
      intro t ht
      exact Nat.mul_le_mul_right (extremalSize t)
        (card_quotientPrimes_sub_bad_le_good ht)
    _ ≤ extremalSize N := sum_goodFiberPrimes_mul_extremalSize_le N T

/-- Sharper class bound using only bad primes in the actual candidate interval
`[T+1,N]`. -/
theorem card_quotientPrimes_sub_restrictedBad_le_good (N T t : ℕ) :
    (quotientPrimes N T t).card -
      (badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card ≤
        (goodFiberPrimes N T t).card := by
  classical
  let Q := quotientPrimes N T t
  let G := goodFiberPrimes N T t
  have hGQ : G ⊆ Q := goodFiberPrimes_subset_quotientPrimes N T t
  have hDiffBad : Q \ G ⊆ badPrimeSetFrom (T + 1) N (chosenExtremizer t) := by
    intro p hpDiff
    have hpQ : p ∈ Q := (Finset.mem_sdiff.mp hpDiff).1
    have hpNotG : p ∉ G := (Finset.mem_sdiff.mp hpDiff).2
    change p ∈ quotientPrimes N T t at hpQ
    change p ∉ goodFiberPrimes N T t at hpNotG
    rw [quotientPrimes] at hpQ
    have hpData := Finset.mem_filter.mp hpQ
    rw [badPrimeSetFrom, Finset.mem_filter]
    refine ⟨hpData.1, hpData.2.1, ?_⟩
    intro hMod
    apply hpNotG
    rw [goodFiberPrimes, Finset.mem_filter]
    exact ⟨hpData.1, hpData.2.1, hpData.2.2, hMod⟩
  have hDiffCard : (Q \ G).card ≤
      (badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card :=
    Finset.card_le_card hDiffBad
  have hCardEq : (Q \ G).card = Q.card - G.card :=
    Finset.card_sdiff_of_subset hGQ
  dsimp [Q, G] at hDiffCard hCardEq
  omega

/-- Sharp exact recurrence, subtracting only modularly bad primes in the true
candidate interval. -/
theorem sum_quotient_sub_restrictedBad_mul_extremalSize_le (N T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T,
      ((quotientPrimes N T t).card -
        (badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card) *
          extremalSize t) ≤ extremalSize N := by
  calc
    (∑ t ∈ Finset.Icc 1 T,
      ((quotientPrimes N T t).card -
        (badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card) *
          extremalSize t) ≤
        ∑ t ∈ Finset.Icc 1 T,
          (goodFiberPrimes N T t).card * extremalSize t := by
      apply Finset.sum_le_sum
      intro t ht
      exact Nat.mul_le_mul_right (extremalSize t)
        (card_quotientPrimes_sub_restrictedBad_le_good N T t)
    _ ≤ extremalSize N := sum_goodFiberPrimes_mul_extremalSize_le N T

/-- Closed bad-prime error bound for the chosen extremizer in every class of
the sharp recurrence. -/
theorem chosenExtremizer_restrictedBad_power_bound
    {N T t : ℕ} (ht : t ∈ Finset.Icc 1 T) :
    (T + 1) ^ (badPrimeSetFrom (T + 1) N (chosenExtremizer t)).card ≤
      (extremalSize t * t.factorial) ^ (3 ^ extremalSize t) := by
  have htData := Finset.mem_Icc.mp ht
  have hSpec := chosenExtremizer_spec t
  have hOne : 1 ≤ extremalSize t := one_le_extremalSize htData.1
  have hNonempty : (chosenExtremizer t).Nonempty := by
    rw [← Finset.card_pos, hSpec.2]
    exact hOne
  have hBound := pow_card_badPrimeSetFrom_le
    (X := N) (Y := T + 1) (B := chosenExtremizer t)
    (by omega) (by omega) (le_rfl) hNonempty hSpec.1.1 hSpec.1.2
  simpa [hSpec.2] using hBound

end Erdos321
