/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RoughDivisorBound
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Dist

/-!
# Counting rough divisors of an arbitrary integer

In the off-diagonal part of BNPZ Lemma 9.2, a nonzero cleared numerator need
not itself be rough, but every modulus being counted is a rough divisor of
it.  We encode such a divisor by its prime-factor list, padded with ones to a
fixed length.  This gives the explicit bound

`# {d | d ∣ F, d is z-rough} ≤ (# primeFactors F + 1) ^ L`

whenever `F < z ^ (L + 1)`.  No average-order divisor theorem is used.
-/

namespace Erdos387

open scoped ArithmeticFunction.Omega BigOperators

/-- The positive divisors of `F` all of whose prime factors are at least
`z`. -/
noncomputable def roughDivisors (z F : ℕ) : Finset ℕ := by
  classical
  exact F.divisors.filter (IsZRough z)

theorem roughDivisor_pos {z F d : ℕ} (hF : F ≠ 0)
    (hd : d ∈ roughDivisors z F) : 0 < d := by
  classical
  rw [roughDivisors, Finset.mem_filter, Nat.mem_divisors] at hd
  exact Nat.pos_of_dvd_of_pos hd.1.1 (Nat.pos_of_ne_zero hF)

theorem roughDivisor_dvd {z F d : ℕ}
    (hd : d ∈ roughDivisors z F) : d ∣ F := by
  classical
  rw [roughDivisors, Finset.mem_filter, Nat.mem_divisors] at hd
  exact hd.1.1

theorem roughDivisor_isZRough {z F d : ℕ}
    (hd : d ∈ roughDivisors z F) : IsZRough z d := by
  classical
  rw [roughDivisors, Finset.mem_filter] at hd
  exact hd.2

/-- Prime-factor list padded by ones, viewed as a fixed-length tuple. -/
def roughDivisorCode (L d : ℕ) : Fin L → ℕ :=
  fun i => d.primeFactorsList.getD i.val 1

/-- The product of a list padded by ones to a length at least its actual
length is the original list product. -/
theorem prod_getD_one_eq_prod (l : List ℕ) (L : ℕ)
    (hlen : l.length ≤ L) :
    (∏ i : Fin L, l.getD i.val 1) = l.prod := by
  induction L generalizing l with
  | zero =>
      have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst l
      simp
  | succ L ih =>
      cases l with
      | nil => simp
      | cons a l =>
          have htail : l.length ≤ L := by simpa using hlen
          rw [Fin.prod_univ_succ]
          change a * (∏ i : Fin L, l.getD i.val 1) = a * l.prod
          rw [ih l htail]

theorem roughDivisorCode_prod {L d : ℕ}
    (hd : d ≠ 0)
    (hlen : ArithmeticFunction.cardFactors d ≤ L) :
    (∏ i : Fin L, roughDivisorCode L d i) = d := by
  change (∏ i : Fin L, d.primeFactorsList.getD i.val 1) = d
  rw [prod_getD_one_eq_prod d.primeFactorsList L (by
      simpa [ArithmeticFunction.cardFactors_apply] using hlen),
    Nat.prod_primeFactorsList hd]

theorem roughDivisorCode_coordinate_mem
    {z F L d : ℕ} (hF : F ≠ 0) (hd : d ∈ roughDivisors z F)
    (i : Fin L) :
    roughDivisorCode L d i ∈ insert 1 F.primeFactors := by
  classical
  unfold roughDivisorCode
  by_cases hi : i.val < d.primeFactorsList.length
  · rw [List.getD_eq_getElem _ _ hi]
    apply Finset.mem_insert_of_mem
    have hpList : d.primeFactorsList[i.val] ∈ d.primeFactorsList :=
      List.getElem_mem hi
    have hpPrime : d.primeFactorsList[i.val].Prime :=
      Nat.prime_of_mem_primeFactorsList hpList
    have hpd : d.primeFactorsList[i.val] ∣ d :=
      Nat.dvd_of_mem_primeFactorsList hpList
    exact hpPrime.mem_primeFactors
      (hpd.trans (roughDivisor_dvd hd)) hF
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Finset.mem_insert_self 1 F.primeFactors

/-- A rough divisor below `z^(L+1)` has a prime-factor list of length at
most `L`. -/
theorem roughDivisor_cardFactors_le
    {z F L d : ℕ} (hz : 1 < z) (hF : F ≠ 0)
    (hFPow : F < z ^ (L + 1)) (hd : d ∈ roughDivisors z F) :
    ArithmeticFunction.cardFactors d ≤ L := by
  apply cardFactors_le_of_rough_lt_pow hz (roughDivisor_pos hF hd).ne'
    (roughDivisor_isZRough hd)
  exact lt_of_le_of_lt
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hF) (roughDivisor_dvd hd)) hFPow

theorem roughDivisorCode_injectiveOn
    {z F L : ℕ} (hz : 1 < z) (hF : F ≠ 0)
    (hFPow : F < z ^ (L + 1)) :
    ((roughDivisors z F : Finset ℕ) : Set ℕ).InjOn
      (roughDivisorCode L) := by
  intro d hd e he hcode
  have hdprod := roughDivisorCode_prod (roughDivisor_pos hF hd).ne'
    (roughDivisor_cardFactors_le hz hF hFPow hd)
  have heprod := roughDivisorCode_prod (roughDivisor_pos hF he).ne'
    (roughDivisor_cardFactors_le hz hF hFPow he)
  rw [← hdprod, ← heprod, hcode]

/-- Explicit bound for the family of rough divisors of a not-necessarily
rough integer. -/
theorem roughDivisors_card_le_primeFactors_add_one_pow
    {z F L : ℕ} (hz : 1 < z) (hF : F ≠ 0)
    (hFPow : F < z ^ (L + 1)) :
    (roughDivisors z F).card ≤ (F.primeFactors.card + 1) ^ L := by
  classical
  let box : Finset (Fin L → ℕ) :=
    Fintype.piFinset fun _ : Fin L => insert 1 F.primeFactors
  have hmaps : ((roughDivisors z F : Finset ℕ) : Set ℕ).MapsTo
      (roughDivisorCode L) (box : Set (Fin L → ℕ)) := by
    intro d hd
    change roughDivisorCode L d ∈
      Fintype.piFinset (fun _ : Fin L => insert 1 F.primeFactors)
    rw [Fintype.mem_piFinset]
    exact roughDivisorCode_coordinate_mem hF hd
  calc
    (roughDivisors z F).card ≤ box.card :=
      Finset.card_le_card_of_injOn (roughDivisorCode L) hmaps
        (roughDivisorCode_injectiveOn hz hF hFPow)
    _ = (F.primeFactors.card + 1) ^ L := by
      have hone : 1 ∉ F.primeFactors := by
        intro h
        exact (Nat.prime_of_mem_primeFactors h).ne_one rfl
      simp [box, Finset.card_insert_of_notMem hone]

/-- Any finite family of positive rough divisors inherits the preceding
bound. -/
theorem roughDivisorFamily_card_le
    {z F L : ℕ} (hz : 1 < z) (hF : F ≠ 0)
    (hFPow : F < z ^ (L + 1)) (Q : Finset ℕ)
    (hQrough : ∀ q ∈ Q, IsZRough z q)
    (hQdvd : ∀ q ∈ Q, q ∣ F) :
    Q.card ≤ (F.primeFactors.card + 1) ^ L := by
  classical
  apply (Finset.card_le_card ?_).trans
    (roughDivisors_card_le_primeFactors_add_one_pow hz hF hFPow)
  intro q hq
  rw [roughDivisors, Finset.mem_filter, Nat.mem_divisors]
  exact ⟨⟨hQdvd q hq, hF⟩, hQrough q hq⟩

/-- A natural congruence makes the modulus divide the distance between the
two representatives. -/
theorem Nat.ModEq.dvd_dist {q a b : ℕ} (h : Nat.ModEq q a b) :
    q ∣ Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    exact (Nat.modEq_iff_dvd' hab).mp h
  · rw [Nat.dist_eq_sub_of_le_right hba]
    exact (Nat.modEq_iff_dvd' hba).mp h.symm

/-- Every natural number is `2`-rough. -/
theorem isZRough_two (n : ℕ) : IsZRough 2 n := by
  intro p hp hpTwo hpd
  exact (not_lt_of_ge hp.two_le) hpTwo

/-- The number of distinct prime factors is bounded by the number counted
with multiplicity. -/
theorem primeFactors_card_le_cardFactors (n : ℕ) :
    n.primeFactors.card ≤ ArithmeticFunction.cardFactors n := by
  rw [ArithmeticFunction.cardFactors_apply]
  change n.primeFactorsList.toFinset.card ≤ n.primeFactorsList.length
  exact List.toFinset_card_le _

/-- A powers-of-two size bound controls the number of distinct prime
factors. -/
theorem primeFactors_card_le_of_lt_two_pow
    {n D : ℕ} (hn : n ≠ 0) (hnPow : n < 2 ^ (D + 1)) :
    n.primeFactors.card ≤ D := by
  exact (primeFactors_card_le_cardFactors n).trans
    (cardFactors_le_of_rough_lt_pow (by norm_num) hn
      (isZRough_two n) hnPow)

end Erdos387
