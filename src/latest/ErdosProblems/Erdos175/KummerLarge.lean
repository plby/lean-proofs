/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# The large-prime-power part of the Kummer detector for Erdős 175

This file contains only the elementary arithmetic behind equation (7.1) of
Granville--Ramaré.  If `d = p ^ a` lies in

`sqrt n < d ≤ sqrt (2 * n)`,

then the addition `n + n` has a forced carry at the `d ^ 2` position.  If the
central binomial coefficient is squarefree, Kummer's theorem says that this
is its only base-`p` carry, so there is no carry at the `d` position.  The
latter assertion is equivalent both to a remainder inequality and to the
corresponding floor identity.
-/

namespace Erdos175.KummerLarge

open Nat
open scoped ArithmeticFunction

/-- The set of carry positions in the base-`p` addition `n + n`, using the
canonical finite bound occurring in Mathlib's version of Kummer's theorem. -/
def centralCarries (p n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (Nat.log p (n + n) + 1)).filter fun i =>
    p ^ i ≤ n % p ^ i + n % p ^ i

/-- Kummer's theorem, written for the central binomial coefficient and the
canonical finite set `centralCarries`. -/
lemma factorization_centralBinom_eq_card_centralCarries
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (Nat.choose (2 * n) n).factorization p = (centralCarries p n).card := by
  rw [show 2 * n = n + n by omega]
  exact Nat.factorization_choose' hp (Nat.lt_succ_self _)

/-- A carry in position `i` is exactly the failure of additivity of division
by `p ^ i`.  This is the natural-number form of the familiar identity for
fractional parts. -/
lemma carry_iff_div_two_sub
    {p n i : ℕ} (hp : 0 < p) :
    p ^ i ≤ n % p ^ i + n % p ^ i ↔
      (2 * n) / p ^ i - 2 * (n / p ^ i) = 1 := by
  have hpow : 0 < p ^ i := pow_pos hp i
  have hadd := Nat.add_div (a := n) (b := n) hpow
  rw [show n + n = 2 * n by omega] at hadd
  split_ifs at hadd with hcarry
  · constructor
    · intro _
      omega
    · intro _
      exact hcarry
  · constructor
    · intro h
      exact False.elim (hcarry h)
    · intro h
      omega

/-- The complementary no-carry form of `carry_iff_div_two_sub`. -/
lemma no_carry_iff_div_two
    {p n i : ℕ} (hp : 0 < p) :
    n % p ^ i + n % p ^ i < p ^ i ↔
      (2 * n) / p ^ i = 2 * (n / p ^ i) := by
  have hpow : 0 < p ^ i := pow_pos hp i
  have hadd := Nat.add_div (a := n) (b := n) hpow
  rw [show n + n = 2 * n by omega] at hadd
  split_ifs at hadd with hcarry
  · constructor
    · intro h
      omega
    · intro h
      omega
  · constructor
    · intro _
      omega
    · intro _
      omega

/-- If `2n < p ^ 2`, only the first Kummer position can occur.  Thus the
factorization of `p` in the central binomial coefficient is exactly the
indicator of the remainder carry. -/
lemma factorization_centralBinom_eq_ite_remainder
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hlarge : 2 * n < p ^ 2) :
    (Nat.choose (2 * n) n).factorization p =
      if p ≤ n % p + n % p then 1 else 0 := by
  have hlog : Nat.log p (2 * n) < 2 :=
    (Nat.log_lt_iff_lt_pow hp.one_lt (by positivity)).2 hlarge
  have hlog' : Nat.log p (n + n) < 2 := by simpa [two_mul] using hlog
  rw [show 2 * n = n + n by omega, Nat.factorization_choose' hp hlog']
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega]
  by_cases hcarry : p ≤ n % p + n % p
  · rw [if_pos hcarry]
    have heq :
        ({i ∈ ({1} : Finset ℕ) | p ^ i ≤ n % p ^ i + n % p ^ i}) = {1} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact And.left
      · intro hi
        subst i
        exact ⟨rfl, by simpa only [pow_one] using hcarry⟩
    rw [heq]
    simp
  · rw [if_neg hcarry]
    have heq :
        ({i ∈ ({1} : Finset ℕ) | p ^ i ≤ n % p ^ i + n % p ^ i}) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨rfl, hi⟩
      exact hcarry (by simpa only [pow_one] using hi)
    rw [heq]
    simp

/-- Legendre's floor formula for a prime larger than `sqrt (2n)`. -/
lemma factorization_centralBinom_eq_div_sub
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hlarge : 2 * n < p ^ 2) :
    (Nat.choose (2 * n) n).factorization p =
      (2 * n) / p - 2 * (n / p) := by
  rw [factorization_centralBinom_eq_ite_remainder hp hn hlarge]
  by_cases hcarry : p ≤ n % p + n % p
  · rw [if_pos hcarry]
    have hc := (carry_iff_div_two_sub (p := p) (n := n) (i := 1) hp.pos).mp
      (by simpa only [pow_one] using hcarry)
    simpa only [pow_one] using hc.symm
  · rw [if_neg hcarry]
    have hnocarry : n % p + n % p < p := by omega
    have hdiv : (2 * n) / p = 2 * (n / p) := by
      simpa only [pow_one] using
        (no_carry_iff_div_two (p := p) (n := n) (i := 1) hp.pos).mp
          (by simpa only [pow_one] using hnocarry)
    omega

/-- If `p ^ i` is at most `2n`, then the Kummer carry set is long enough to
contain the position `i`. -/
lemma mem_centralCarries_of_pow_le
    {p n i : ℕ} (hp : p.Prime) (hi : 1 ≤ i)
    (hpow : p ^ i ≤ 2 * n)
    (hcarry : p ^ i ≤ n % p ^ i + n % p ^ i) :
    i ∈ centralCarries p n := by
  simp only [centralCarries, Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨hi, ?_⟩, hcarry⟩
  have hn : 0 < n + n := by
    have : 0 < p ^ i := pow_pos hp.pos i
    omega
  have hilog : i ≤ Nat.log p (n + n) :=
    (Nat.le_log_iff_pow_le hp.one_lt hn.ne').2 (by simpa [two_mul] using hpow)
  omega

/-- If the square of a prime power `p ^ a` lies in `(n, 2n]`, then Kummer
forces a carry at position `2a`. -/
lemma twice_exponent_mem_centralCarries
    {p n a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hlower : n < (p ^ a) ^ 2) (hupper : (p ^ a) ^ 2 ≤ 2 * n) :
    2 * a ∈ centralCarries p n := by
  have hpow_eq : p ^ (2 * a) = (p ^ a) ^ 2 := by ring
  apply mem_centralCarries_of_pow_le hp (by omega) (by simpa [hpow_eq] using hupper)
  rw [hpow_eq]
  have hnmod : n % (p ^ a) ^ 2 = n := Nat.mod_eq_of_lt hlower
  rw [hnmod]
  omega

/-- In the prime-square interval `n < p ^ 2 ≤ 2n`, a carry at the first
position combines with the forced carry at the second position and produces
a square divisor of the central binomial coefficient. -/
lemma prime_sq_dvd_centralBinom_of_carry
    {p n : ℕ} (hp : p.Prime)
    (hlower : n < p ^ 2) (hupper : p ^ 2 ≤ 2 * n)
    (hcarry : p ≤ n % p + n % p) :
    p ^ 2 ∣ Nat.choose (2 * n) n := by
  have hmem1 : 1 ∈ centralCarries p n := by
    apply mem_centralCarries_of_pow_le hp (by omega)
    · have hpp : p ≤ p ^ 2 := by nlinarith [hp.two_le]
      simpa only [pow_one] using hpp.trans hupper
    · simpa using hcarry
  have hmem2 : 2 ∈ centralCarries p n := by
    simpa using twice_exponent_mem_centralCarries hp (a := 1) (by omega)
      (by simpa using hlower) (by simpa using hupper)
  have hsubset : ({1, 2} : Finset ℕ) ⊆ centralCarries p n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hmem1
    · exact hmem2
  have hcard : 2 ≤ (centralCarries p n).card := by
    have := Finset.card_le_card hsubset
    simpa using this
  apply (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero (by omega))).2
  rw [factorization_centralBinom_eq_card_centralCarries hp n]
  exact hcard

/-- Contrapositive detector: if no large-prime square divides the central
binomial coefficient, then the first base-`p` position has no carry.  Unlike
the squarefree lemmas below, this needs no assumption on any other prime. -/
lemma no_carry_at_large_prime_of_not_sq_dvd
    {p n : ℕ} (hp : p.Prime)
    (hlower : n < p ^ 2) (hupper : p ^ 2 ≤ 2 * n)
    (hnot : ¬p ^ 2 ∣ Nat.choose (2 * n) n) :
    n % p + n % p < p := by
  by_contra h
  exact hnot (prime_sq_dvd_centralBinom_of_carry hp hlower hupper (by omega))

/-- Floor form of `no_carry_at_large_prime_of_not_sq_dvd`. -/
lemma div_large_prime_additive_of_not_sq_dvd
    {p n : ℕ} (hp : p.Prime)
    (hlower : n < p ^ 2) (hupper : p ^ 2 ≤ 2 * n)
    (hnot : ¬p ^ 2 ∣ Nat.choose (2 * n) n) :
    (2 * n) / p = 2 * (n / p) := by
  simpa only [pow_one] using
    (no_carry_iff_div_two (p := p) (n := n) (i := 1) hp.pos).mp
      (by simpa only [pow_one] using
        no_carry_at_large_prime_of_not_sq_dvd hp hlower hupper hnot)

/-- Squarefreeness makes the forced carry at `2a` the unique base-`p` carry. -/
lemma centralCarries_eq_singleton_twice_exponent_of_squarefree
    {p n a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hlower : n < (p ^ a) ^ 2) (hupper : (p ^ a) ^ 2 ≤ 2 * n)
    (hsq : Squarefree (Nat.choose (2 * n) n)) :
    centralCarries p n = {2 * a} := by
  have hmem : 2 * a ∈ centralCarries p n :=
    twice_exponent_mem_centralCarries hp ha hlower hupper
  apply Finset.Subset.antisymm
  · intro i hi
    have hcard : (centralCarries p n).card ≤ 1 := by
      rw [← factorization_centralBinom_eq_card_centralCarries hp n]
      exact hsq.natFactorization_le_one p
    have hieq : i = 2 * a := Finset.card_le_one.mp hcard i hi (2 * a) hmem
    simp [hieq]
  · simpa using hmem

/-- The forced carry at `2a`, together with squarefreeness, excludes a carry
at the distinct position `a`. -/
lemma no_carry_at_prime_power_of_squarefree
    {p n a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hlower : n < (p ^ a) ^ 2) (hupper : (p ^ a) ^ 2 ≤ 2 * n)
    (hsq : Squarefree (Nat.choose (2 * n) n)) :
    n % p ^ a + n % p ^ a < p ^ a := by
  have hsingle := centralCarries_eq_singleton_twice_exponent_of_squarefree
    hp ha hlower hupper hsq
  by_contra h
  have hcarry : p ^ a ≤ n % p ^ a + n % p ^ a := by omega
  have hmem : a ∈ centralCarries p n := by
    apply mem_centralCarries_of_pow_le hp ha
    · have hdle : p ^ a ≤ (p ^ a) ^ 2 := by
        have : 1 ≤ p ^ a := pow_pos hp.pos a
        nlinarith
      exact hdle.trans hupper
    · exact hcarry
  rw [hsingle] at hmem
  simp only [Finset.mem_singleton] at hmem
  omega

/-- Floor/division version of the no-carry conclusion. -/
lemma div_prime_power_additive_of_squarefree
    {p n a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hlower : n < (p ^ a) ^ 2) (hupper : (p ^ a) ^ 2 ≤ 2 * n)
    (hsq : Squarefree (Nat.choose (2 * n) n)) :
    (2 * n) / p ^ a = 2 * (n / p ^ a) := by
  exact (no_carry_iff_div_two hp.pos).mp
    (no_carry_at_prime_power_of_squarefree hp ha hlower hupper hsq)

/-- For a prime `p > sqrt n` with `p ≤ sqrt (2n)`, squarefreeness is
equivalent to saying that the forced second-position carry is the only one;
in particular the first position has no carry. -/
lemma no_carry_at_large_prime_of_squarefree
    {p n : ℕ} (hp : p.Prime)
    (hlower : n < p ^ 2) (hupper : p ^ 2 ≤ 2 * n)
    (hsq : Squarefree (Nat.choose (2 * n) n)) :
    n % p + n % p < p := by
  simpa using no_carry_at_prime_power_of_squarefree hp (a := 1) (by omega)
    (by simpa using hlower) (by simpa using hupper) hsq

/-- The same large-prime statement expressed by natural-number floors. -/
lemma div_large_prime_additive_of_squarefree
    {p n : ℕ} (hp : p.Prime)
    (hlower : n < p ^ 2) (hupper : p ^ 2 ≤ 2 * n)
    (hsq : Squarefree (Nat.choose (2 * n) n)) :
    (2 * n) / p = 2 * (n / p) := by
  simpa using div_prime_power_additive_of_squarefree hp (a := 1) (by omega)
    (by simpa using hlower) (by simpa using hupper) hsq

/-- A prime strictly above `sqrt n` is automatically in the lower half of
the prime-square interval used by the detector. -/
lemma sq_lt_of_sqrt_lt {p n : ℕ} (h : Nat.sqrt n < p) : n < p ^ 2 := by
  rw [Nat.sqrt_lt] at h
  simpa [pow_two] using h

/-- A prime at most `sqrt (2n)` is automatically in the upper half of the
prime-square interval used by the detector. -/
lemma sq_le_of_le_sqrt {p n : ℕ} (h : p ≤ Nat.sqrt (2 * n)) : p ^ 2 ≤ 2 * n := by
  simpa [pow_two] using (Nat.le_sqrt.mp h)

/-- Prime powers in the half-open interval used in Granville--Ramaré (7.1). -/
def primePowerInterval (n : ℕ) : Finset ℕ :=
  (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n))).filter IsPrimePow

lemma mem_primePowerInterval {n d : ℕ} :
    d ∈ primePowerInterval n ↔
      Nat.sqrt n < d ∧ d ≤ Nat.sqrt (2 * n) ∧ IsPrimePow d := by
  simp only [primePowerInterval, Finset.mem_filter, Finset.mem_Ioc]
  tauto

/-- Membership in `primePowerInterval` implies the squared interval
inequalities in the exact form required by the Kummer lemmas. -/
lemma sq_bounds_of_mem_primePowerInterval {n d : ℕ} (hd : d ∈ primePowerInterval n) :
    n < d ^ 2 ∧ d ^ 2 ≤ 2 * n := by
  rw [mem_primePowerInterval] at hd
  exact ⟨sq_lt_of_sqrt_lt hd.1, sq_le_of_le_sqrt hd.2.1⟩

/-- Convenient interval form of `no_carry_at_large_prime_of_squarefree`. -/
lemma no_carry_at_large_prime_of_sqrt_bounds
    {p n : ℕ} (hp : p.Prime)
    (hlower : Nat.sqrt n < p) (hupper : p ≤ Nat.sqrt (2 * n))
    (hsq : Squarefree (Nat.choose (2 * n) n)) :
    n % p + n % p < p :=
  no_carry_at_large_prime_of_squarefree hp (sq_lt_of_sqrt_lt hlower)
    (sq_le_of_le_sqrt hupper) hsq

/-- Sqrt-bound form of the detector under the precise local hypothesis that
`p ^ 2` does not divide the central binomial coefficient. -/
lemma no_carry_at_large_prime_of_not_sq_dvd_sqrt_bounds
    {p n : ℕ} (hp : p.Prime)
    (hlower : Nat.sqrt n < p) (hupper : p ≤ Nat.sqrt (2 * n))
    (hnot : ¬p ^ 2 ∣ Nat.choose (2 * n) n) :
    n % p + n % p < p :=
  no_carry_at_large_prime_of_not_sq_dvd hp (sq_lt_of_sqrt_lt hlower)
    (sq_le_of_le_sqrt hupper) hnot

/-- The von Mangoldt weight of a prime power is the logarithm of its base
prime.  This is the termwise conversion used when the Kummer identities are
summed over the interval `sqrt n < d ≤ sqrt (2n)`. -/
lemma vonMangoldt_prime_power {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    ArithmeticFunction.vonMangoldt (p ^ a) = Real.log p := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- Every prime-power term in the Kummer interval obeys the no-carry floor
identity under squarefreeness.  This is the exact termwise arithmetic input
to the weighted sums in Granville--Ramaré (7.1). -/
lemma prime_power_interval_term_of_squarefree
    {n d : ℕ} (hd : IsPrimePow d)
    (hlower : n < d ^ 2) (hupper : d ^ 2 ≤ 2 * n)
    (hsq : Squarefree (Nat.choose (2 * n) n)) :
    ∃ p a : ℕ,
      p.Prime ∧ 1 ≤ a ∧ d = p ^ a ∧
      n % d + n % d < d ∧
      (2 * n) / d = 2 * (n / d) ∧
      ArithmeticFunction.vonMangoldt d = Real.log p := by
  rw [isPrimePow_nat_iff] at hd
  obtain ⟨p, a, hp, ha, rfl⟩ := hd
  refine ⟨p, a, hp, ha, rfl, ?_, ?_, ?_⟩
  · exact no_carry_at_prime_power_of_squarefree hp ha hlower hupper hsq
  · exact div_prime_power_additive_of_squarefree hp ha hlower hupper hsq
  · exact vonMangoldt_prime_power hp ha

/-- The termwise floor identity, now packaged directly for membership in the
finite prime-power interval. -/
lemma div_primePowerInterval_additive_of_squarefree
    {n d : ℕ} (hd : d ∈ primePowerInterval n)
    (hsq : Squarefree (Nat.choose (2 * n) n)) :
    (2 * n) / d = 2 * (n / d) := by
  have hb := sq_bounds_of_mem_primePowerInterval hd
  have hpp : IsPrimePow d := (mem_primePowerInterval.mp hd).2.2
  obtain ⟨p, a, hp, ha, hpa, hrem, hdiv, hLambda⟩ :=
    prime_power_interval_term_of_squarefree hpp hb.1 hb.2 hsq
  exact hdiv

/-- Consequently, the von Mangoldt weighted floor defect vanishes over the
whole interval.  This is the finite-sum form of the elementary arithmetic
input to equation (7.1), before the sawtooth rewrite. -/
lemma sum_vonMangoldt_mul_floor_defect_eq_zero
    {n : ℕ} (hsq : Squarefree (Nat.choose (2 * n) n)) :
    ∑ d ∈ primePowerInterval n,
        ArithmeticFunction.vonMangoldt d *
          (((((2 * n) / d : ℕ) : ℝ)) - 2 * (((n / d : ℕ) : ℝ))) = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  rw [div_primePowerInterval_additive_of_squarefree hd hsq]
  norm_num

end Erdos175.KummerLarge
