/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import Mathlib

/-!
# Erdős 730: Kummer and the lower-half digit criterion

This module formalizes the exact transition from Kummer's theorem to the
digit set `D_p` used in equation (4) of the positive-density proof.

For an odd prime `p`, `LowerHalfDigits p t` says that every base-`p` digit
of `t` is at most `(p-1)/2`.  We prove

`p ∤ centralBinom t ↔ LowerHalfDigits p t`.

The intermediate predicate `NoSelfCarry` is an exact prefix-remainder form
of saying that adding `t+t` creates no base-`p` carry.  The proof imports
mathlib's kernel-checked `Nat.factorization_choose'`; it introduces no
analytic hypothesis and no new axiom.
-/

namespace Erdos730
namespace KummerTransition

open Finset

/-- A carry occurs at depth `i` when the two length-`i` base-`p` prefixes
of `t` sum to at least `p^i`. -/
def SelfCarryAt (p t i : ℕ) : Prop :=
  p ^ i ≤ t % p ^ i + t % p ^ i

instance selfCarryAtDecidable (p t i : ℕ) : Decidable (SelfCarryAt p t i) := by
  unfold SelfCarryAt
  infer_instance

/-- There is no carry at any positive base-`p` prefix depth. -/
def NoSelfCarry (p t : ℕ) : Prop :=
  ∀ i, 0 < i → ¬SelfCarryAt p t i

/-- The digit set `D_p` from the paper. -/
def LowerHalfDigits (p t : ℕ) : Prop :=
  ∀ d ∈ p.digits t, d ≤ (p - 1) / 2

/-- Mathlib's Kummer theorem specialized to the central binomial
coefficient.  The right side counts all carry depths below any strict
logarithmic bound `b`. -/
theorem factorization_centralBinom_eq_carryCount
    {p t b : ℕ} (hp : p.Prime) (hb : Nat.log p (2 * t) < b) :
    t.centralBinom.factorization p =
      #{i ∈ Finset.Ico 1 b | SelfCarryAt p t i} := by
  classical
  simpa only [Nat.centralBinom, two_mul, SelfCarryAt] using
    (Nat.factorization_choose' (n := t) (k := t) hp (by simpa [two_mul] using hb))

/-- For an odd base, its paper half `(p-1)/2` is characterized by
`2*h+1=p`. -/
theorem two_mul_paperHalf_add_one {p : ℕ} (hpodd : Odd p) :
    2 * ((p - 1) / 2) + 1 = p := by
  have h := Nat.two_mul_div_two_add_one_of_odd hpodd
  omega

/-- A list whose digits lie in the lower half has no self-carry within its
own length.  This is the finite combinatorial core of the `D_p` criterion. -/
theorem two_mul_ofDigits_lt_pow_length
    {p : ℕ} (hpodd : Odd p) (l : List ℕ)
    (hl : ∀ d ∈ l, d ≤ (p - 1) / 2) :
    2 * Nat.ofDigits p l < p ^ l.length := by
  induction l with
  | nil => simp [Nat.ofDigits]
  | cons d l ih =>
      have hd : 2 * d + 1 ≤ p := by
        have hd' := hl d (by simp)
        have hpform := two_mul_paperHalf_add_one hpodd
        omega
      have htail : ∀ e ∈ l, e ≤ (p - 1) / 2 := by
        intro e he
        exact hl e (by simp [he])
      have hih := ih htail
      rw [Nat.ofDigits_cons, List.length_cons, pow_succ']
      rw [Nat.lt_iff_add_one_le]
      calc
        2 * (d + p * Nat.ofDigits p l) + 1 =
            (2 * d + 1) + p * (2 * Nat.ofDigits p l) := by ring
        _ ≤ p + p * (2 * Nat.ofDigits p l) :=
          Nat.add_le_add_right hd _
        _ = p * (2 * Nat.ofDigits p l + 1) := by ring
        _ ≤ p * p ^ l.length := by
          exact Nat.mul_le_mul_left p (Nat.lt_iff_add_one_le.mp hih)

/-- The contribution of digit `j` is a lower bound for the represented
number. -/
theorem pow_mul_getElem_le_ofDigits
    (p : ℕ) (l : List ℕ) (j : ℕ) (hj : j < l.length) :
    p ^ j * l[j] ≤ Nat.ofDigits p l := by
  induction l generalizing j with
  | nil => simp at hj
  | cons d l ih =>
      cases j with
      | zero =>
          simp only [pow_zero, one_mul, List.getElem_cons_zero, Nat.ofDigits_cons]
          exact Nat.le_add_right _ _
      | succ j =>
          have hj' : j < l.length := by simpa using hj
          have hih := ih j hj'
          simp only [List.getElem_cons_succ, pow_succ', Nat.ofDigits_cons]
          calc
            p * p ^ j * l[j] = p * (p ^ j * l[j]) := by ring
            _ ≤ p * Nat.ofDigits p l := Nat.mul_le_mul_left p hih
            _ ≤ d + p * Nat.ofDigits p l := Nat.le_add_left _ _

/-- Lower-half digits imply the exact absence of every self-carry. -/
theorem noSelfCarry_of_lowerHalfDigits
    {p t : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (ht : LowerHalfDigits p t) : NoSelfCarry p t := by
  intro i hi
  rw [SelfCarryAt, not_le]
  rw [Nat.self_mod_pow_eq_ofDigits_take i t hp.two_le]
  have htake : ∀ d ∈ (p.digits t).take i, d ≤ (p - 1) / 2 := by
    intro d hd
    exact ht d (List.mem_of_mem_take hd)
  have hshort := two_mul_ofDigits_lt_pow_length hpodd _ htake
  simpa [two_mul] using hshort.trans_le
    (Nat.pow_le_pow_right hp.one_le (List.length_take_le i (p.digits t)))

/-- Absence of every self-carry forces every base-`p` digit into the lower
half. -/
theorem lowerHalfDigits_of_noSelfCarry
    {p t : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (ht : NoSelfCarry p t) : LowerHalfDigits p t := by
  intro d hd
  obtain ⟨j, hj, rfl⟩ := (List.mem_iff_getElem.mp hd)
  by_contra hlarge
  have hdlarge : (p - 1) / 2 < (p.digits t)[j] := Nat.lt_of_not_ge hlarge
  have hp_le_two_digit : p ≤ 2 * (p.digits t)[j] := by
    have hpform := two_mul_paperHalf_add_one hpodd
    omega
  have hjtake : j < ((p.digits t).take (j + 1)).length := by
    simp [List.length_take, hj]
  have hget : ((p.digits t).take (j + 1))[j] = (p.digits t)[j] := by
    simp [List.getElem_take]
  have hlower := pow_mul_getElem_le_ofDigits p ((p.digits t).take (j + 1)) j hjtake
  rw [hget] at hlower
  have hprefix :
      2 * Nat.ofDigits p ((p.digits t).take (j + 1)) < p ^ (j + 1) := by
    have := ht (j + 1) (by omega)
    rw [SelfCarryAt, not_le] at this
    simpa [Nat.self_mod_pow_eq_ofDigits_take (j + 1) t hp.two_le, two_mul] using this
  have hcontra : p ^ (j + 1) ≤
      2 * Nat.ofDigits p ((p.digits t).take (j + 1)) := by
    calc
      p ^ (j + 1) = p ^ j * p := by rw [pow_succ]
      _ ≤ p ^ j * (2 * (p.digits t)[j]) :=
        Nat.mul_le_mul_left (p ^ j) hp_le_two_digit
      _ = 2 * (p ^ j * (p.digits t)[j]) := by ring
      _ ≤ 2 * Nat.ofDigits p ((p.digits t).take (j + 1)) :=
        Nat.mul_le_mul_left 2 hlower
  exact (not_le_of_gt hprefix) hcontra

/-- Exact equivalence between the paper's digit set `D_p` and Kummer's
prefix carry condition. -/
theorem lowerHalfDigits_iff_noSelfCarry
    {p t : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    LowerHalfDigits p t ↔ NoSelfCarry p t :=
  ⟨noSelfCarry_of_lowerHalfDigits hp hpodd,
    lowerHalfDigits_of_noSelfCarry hp hpodd⟩

/-! ## Kummer's theorem and divisibility -/

/-- Kummer's finite carry count vanishes exactly when no positive prefix
has a self-carry.  Carry depths beyond the logarithmic window are impossible
because `p^i > 2*t`. -/
theorem factorization_centralBinom_eq_zero_iff_noSelfCarry
    {p t : ℕ} (hp : p.Prime) :
    t.centralBinom.factorization p = 0 ↔ NoSelfCarry p t := by
  let b := Nat.log p (2 * t) + 1
  have hb : Nat.log p (2 * t) < b := by
    simp only [b]
    omega
  rw [factorization_centralBinom_eq_carryCount hp hb]
  constructor
  · intro hzero i hi
    have hempty : {j ∈ Finset.Ico 1 b | SelfCarryAt p t j} = ∅ :=
      Finset.card_eq_zero.mp hzero
    by_cases hib : i < b
    · have hiIco : i ∈ Finset.Ico 1 b := Finset.mem_Ico.mpr ⟨hi, hib⟩
      exact (Finset.filter_eq_empty_iff.mp hempty) hiIco
    · rw [SelfCarryAt, not_le]
      have hbi : b ≤ i := Nat.le_of_not_gt hib
      have hlogi : Nat.log p (2 * t) < i := hb.trans_le hbi
      have hpow : 2 * t < p ^ i := Nat.lt_pow_of_log_lt hp.one_lt hlogi
      have hmod : t % p ^ i ≤ t := Nat.mod_le _ _
      omega
  · intro hnone
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    exact hnone i (Finset.mem_Ico.mp hi).1

/-- For a prime, zero factorization is the same as nondivisibility of the
nonzero central binomial coefficient. -/
theorem not_dvd_centralBinom_iff_factorization_eq_zero
    {p t : ℕ} (hp : p.Prime) :
    ¬p ∣ t.centralBinom ↔ t.centralBinom.factorization p = 0 := by
  constructor
  · intro hnot
    exact (Nat.factorization_eq_zero_iff _ _).2 (Or.inr (Or.inl hnot))
  · intro hzero
    rcases (Nat.factorization_eq_zero_iff _ _).1 hzero with hnp | hnot | hzero'
    · exact (hnp hp).elim
    · exact hnot
    · exact (Nat.centralBinom_ne_zero t hzero').elim

/-- Equation (4) of the paper, with `D_p` represented by
`LowerHalfDigits`: an odd prime is absent from the support of `B(t)` exactly
when every base-`p` digit of `t` lies in the lower half. -/
theorem not_dvd_centralBinom_iff_lowerHalfDigits
    {p t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ∣ t.centralBinom ↔ LowerHalfDigits p t := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  rw [not_dvd_centralBinom_iff_factorization_eq_zero hp,
    factorization_centralBinom_eq_zero_iff_noSelfCarry hp]
  exact (lowerHalfDigits_iff_noSelfCarry hp hpodd).symm

/-- Contrapositive support form of equation (4). -/
theorem dvd_centralBinom_iff_not_lowerHalfDigits
    {p t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ t.centralBinom ↔ ¬LowerHalfDigits p t := by
  constructor
  · intro hd hlow
    exact (not_dvd_centralBinom_iff_lowerHalfDigits hp hp2).2 hlow hd
  · intro hnlow
    by_contra hndvd
    exact hnlow ((not_dvd_centralBinom_iff_lowerHalfDigits hp hp2).1 hndvd)

/-! ## Elementary digit shifts used in Proposition 1 -/

/-- Appending `a` zero digits does not affect membership in `D_p`. -/
theorem lowerHalfDigits_primePow_mul_iff
    {p a c : ℕ} (hp : p.Prime) (hc : 0 < c) :
    LowerHalfDigits p (p ^ a * c) ↔ LowerHalfDigits p c := by
  rw [LowerHalfDigits, LowerHalfDigits,
    Nat.digits_base_pow_mul hp.one_lt hc]
  constructor
  · intro h d hd
    exact h d (List.mem_append_right _ hd)
  · intro h d hd
    rcases List.mem_append.mp hd with hzero | hc
    · have hd0 : d = 0 := List.eq_of_mem_replicate hzero
      omega
    · exact h d hc

/-- Exact value of the block of `a` repeated lower-half digits. -/
theorem two_mul_ofDigits_replicate_paperHalf_add_one
    {p : ℕ} (hpodd : Odd p) (a : ℕ) :
    2 * Nat.ofDigits p (List.replicate a ((p - 1) / 2)) + 1 = p ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ']
      have hpform := two_mul_paperHalf_add_one hpodd
      calc
        2 * ((p - 1) / 2 +
            p * Nat.ofDigits p (List.replicate a ((p - 1) / 2))) + 1 =
            (2 * ((p - 1) / 2) + 1) +
              p * (2 * Nat.ofDigits p
                (List.replicate a ((p - 1) / 2))) := by ring
        _ = p + p * (2 * Nat.ofDigits p
              (List.replicate a ((p - 1) / 2))) := by rw [hpform]
        _ = p * (2 * Nat.ofDigits p
              (List.replicate a ((p - 1) / 2)) + 1) := by ring
        _ = p * p ^ a := by rw [ih]

/-- The represented repeated block is `(p^a-1)/2`. -/
theorem ofDigits_replicate_paperHalf
    {p : ℕ} (hpodd : Odd p) (a : ℕ) :
    Nat.ofDigits p (List.replicate a ((p - 1) / 2)) =
      (p ^ a - 1) / 2 := by
  have h := two_mul_ofDigits_replicate_paperHalf_add_one hpodd a
  omega

/-- The low block `(p^a-1)/2` consists of exactly `a` copies of the
lower-half endpoint. -/
theorem digits_pow_sub_one_div_two
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) :
    p.digits ((p ^ a - 1) / 2) =
      List.replicate a ((p - 1) / 2) := by
  have hpodd := hp.odd_of_ne_two hp2
  rw [← ofDigits_replicate_paperHalf hpodd a]
  apply Nat.digits_ofDigits p hp.one_lt
  · intro d hd
    have hdeq : d = (p - 1) / 2 := List.eq_of_mem_replicate hd
    rw [hdeq]
    have hpform := two_mul_paperHalf_add_one hpodd
    omega
  · intro hne
    cases a with
    | zero => simp at hne
    | succ a =>
        have hhalf : 0 < (p - 1) / 2 := by
          have hpform := two_mul_paperHalf_add_one hpodd
          have hp3 : 3 ≤ p := by
            have hp2le := hp.two_le
            omega
          omega
        simpa using hhalf.ne'

/-- Concatenation identity for equation (7): the lower `a` digits of
`p^a*m + (p^a-1)/2` are all the permitted endpoint digit. -/
theorem digits_mul_pow_add_pow_sub_one_div_two
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a m : ℕ) :
    p.digits (p ^ a * m + (p ^ a - 1) / 2) =
      List.replicate a ((p - 1) / 2) ++ p.digits m := by
  have happ := Nat.digits_append_digits (m := m)
    (n := (p ^ a - 1) / 2) hp.pos
  rw [digits_pow_sub_one_div_two hp hp2 a] at happ
  simpa [List.length_replicate, Nat.add_comm] using happ.symm

/-- Equation (8): adjoining the permitted low half-block preserves and
reflects membership in `D_p`. -/
theorem lowerHalfDigits_mul_pow_add_pow_sub_one_div_two_iff
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a m : ℕ) :
    LowerHalfDigits p (p ^ a * m + (p ^ a - 1) / 2) ↔
      LowerHalfDigits p m := by
  rw [LowerHalfDigits, LowerHalfDigits,
    digits_mul_pow_add_pow_sub_one_div_two hp hp2 a m]
  constructor
  · intro h d hd
    exact h d (List.mem_append_right _ hd)
  · intro h d hd
    rcases List.mem_append.mp hd with hhalf | hm
    · exact (List.eq_of_mem_replicate hhalf).le
    · exact h d hm

/-- Exact value of the exceptional low block occurring in `n+1` in the
second transition case. -/
theorem two_mul_ofDigits_upperHalfBlock
    {p : ℕ} (hpodd : Odd p) (a : ℕ) :
    2 * Nat.ofDigits p
        (((p - 1) / 2 + 1) :: List.replicate a ((p - 1) / 2)) =
      p ^ (a + 1) + 1 := by
  rw [Nat.ofDigits_cons]
  have hpform := two_mul_paperHalf_add_one hpodd
  have hrep := two_mul_ofDigits_replicate_paperHalf_add_one hpodd a
  rw [pow_succ']
  calc
    2 * ((p - 1) / 2 + 1 +
        p * Nat.ofDigits p (List.replicate a ((p - 1) / 2))) =
        (2 * ((p - 1) / 2) + 1) + 1 +
          p * (2 * Nat.ofDigits p
            (List.replicate a ((p - 1) / 2))) := by ring
    _ = p + 1 + p * (2 * Nat.ofDigits p
          (List.replicate a ((p - 1) / 2))) := by rw [hpform]
    _ = p * (2 * Nat.ofDigits p
          (List.replicate a ((p - 1) / 2)) + 1) + 1 := by ring
    _ = p * p ^ a + 1 := by rw [hrep]

/-- The low block `(p^(a+1)+1)/2` begins with the forbidden digit
`(p-1)/2+1`, followed by `a` endpoint digits. -/
theorem digits_pow_add_one_div_two
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) :
    p.digits ((p ^ (a + 1) + 1) / 2) =
      ((p - 1) / 2 + 1) :: List.replicate a ((p - 1) / 2) := by
  have hpodd := hp.odd_of_ne_two hp2
  have hvalue : Nat.ofDigits p
      (((p - 1) / 2 + 1) :: List.replicate a ((p - 1) / 2)) =
      (p ^ (a + 1) + 1) / 2 := by
    have h := two_mul_ofDigits_upperHalfBlock hpodd a
    omega
  rw [← hvalue]
  apply Nat.digits_ofDigits p hp.one_lt
  · intro d hd
    have hp2le := hp.two_le
    have hpform := two_mul_paperHalf_add_one hpodd
    have hp3 : 3 ≤ p := by omega
    rcases List.mem_cons.mp hd with rfl | hdrep
    · omega
    · have hdeq : d = (p - 1) / 2 := List.eq_of_mem_replicate hdrep
      omega
  · intro hne
    have hmem := List.getLast_mem hne
    have hp2le := hp.two_le
    have hpform := two_mul_paperHalf_add_one hpodd
    have hp3 : 3 ≤ p := by omega
    rcases List.mem_cons.mp hmem with hfirst | hrep
    · omega
    · have hlast := List.eq_of_mem_replicate hrep
      rw [hlast]
      omega

/-- The exceptional low block, even after adjoining arbitrary higher
digits, is outside `D_p`.  This is the units-digit exclusion used in (6). -/
theorem not_lowerHalfDigits_mul_pow_add_pow_add_one_div_two
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a m : ℕ) :
    ¬LowerHalfDigits p
      (p ^ (a + 1) * m + (p ^ (a + 1) + 1) / 2) := by
  have happ := Nat.digits_append_digits (m := m)
    (n := (p ^ (a + 1) + 1) / 2) hp.pos
  rw [digits_pow_add_one_div_two hp hp2 a] at happ
  have hdigits :
      p.digits (p ^ (a + 1) * m + (p ^ (a + 1) + 1) / 2) =
        (((p - 1) / 2 + 1) :: List.replicate a ((p - 1) / 2)) ++
          p.digits m := by
    simpa [Nat.add_comm] using happ.symm
  intro hlow
  have hforbidden := hlow ((p - 1) / 2 + 1) (by
    rw [hdigits]
    simp)
  omega

/-- Equation (5) at its shifted endpoint: after removing a positive power
of `p`, absence from the support is exactly membership of the cofactor in
`D_p`. -/
theorem not_dvd_centralBinom_primePow_mul_iff
    {p a c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hc : 0 < c) :
    ¬p ∣ (p ^ a * c).centralBinom ↔ LowerHalfDigits p c := by
  rw [not_dvd_centralBinom_iff_lowerHalfDigits hp hp2,
    lowerHalfDigits_primePow_mul_iff hp hc]

/-- Equation (6), lower endpoint: the permitted status of `n` is exactly
that of the high cofactor `(c-1)/2` in decomposition (7). -/
theorem not_dvd_centralBinom_lowerHalfBlock_iff
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a m : ℕ) :
    ¬p ∣ (p ^ a * m + (p ^ a - 1) / 2).centralBinom ↔
      LowerHalfDigits p m := by
  rw [not_dvd_centralBinom_iff_lowerHalfDigits hp hp2,
    lowerHalfDigits_mul_pow_add_pow_sub_one_div_two_iff hp hp2]

/-- Equation (6), upper endpoint: the exceptional units digit forces the
prime into the support of `B(n+1)`. -/
theorem dvd_centralBinom_upperHalfBlock
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a m : ℕ) :
    p ∣ (p ^ (a + 1) * m + (p ^ (a + 1) + 1) / 2).centralBinom := by
  rw [dvd_centralBinom_iff_not_lowerHalfDigits hp hp2]
  exact not_lowerHalfDigits_mul_pow_add_pow_add_one_div_two hp hp2 a m

#print axioms factorization_centralBinom_eq_carryCount
#print axioms lowerHalfDigits_iff_noSelfCarry
#print axioms factorization_centralBinom_eq_zero_iff_noSelfCarry
#print axioms not_dvd_centralBinom_iff_lowerHalfDigits
#print axioms dvd_centralBinom_iff_not_lowerHalfDigits
#print axioms lowerHalfDigits_primePow_mul_iff
#print axioms lowerHalfDigits_mul_pow_add_pow_sub_one_div_two_iff
#print axioms not_lowerHalfDigits_mul_pow_add_pow_add_one_div_two
#print axioms not_dvd_centralBinom_primePow_mul_iff
#print axioms not_dvd_centralBinom_lowerHalfBlock_iff
#print axioms dvd_centralBinom_upperHalfBlock

end KummerTransition
end Erdos730
