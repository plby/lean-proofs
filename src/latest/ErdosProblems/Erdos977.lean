/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 977.
https://www.erdosproblems.com/forum/thread/977

Informal authors:
- C. L. Stewart

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos977.md
-/
/-
This file formalizes the exact statement of Erdős Problem 977 and proves it
unconditionally through a cyclotomic reduction and a specialized p-adic
interpolation determinant.

Mathematical source:
C. L. Stewart, "On divisors of Lucas and Lehmer numbers",
Acta Math. 211 (2013), 291--314, formula (1.8), and
Y. Yamada, "A note on the divisibility of Fermat quotients" (2006).
-/
import Mathlib
import Mathlib.LinearAlgebra.Vandermonde

namespace Erdos977

open Filter Set Finset Function
open scoped Topology fwdDiff Polynomial
open scoped ArithmeticFunction.Moebius

/-- The greatest prime divisor of a natural number, with value `1` when
there is no prime divisor.  In particular the exceptional values at `0` and
`1` agree with Stewart's convention. -/
noncomputable def greatestPrimeFactor (m : ℕ) : ℕ :=
  if h : m.primeFactors.Nonempty then m.primeFactors.max' h else 1

@[simp]
theorem greatestPrimeFactor_eq_one_of_le_one {m : ℕ} (hm : m ≤ 1) :
    greatestPrimeFactor m = 1 := by
  simp [greatestPrimeFactor, Nat.nonempty_primeFactors, not_lt.mpr hm]

theorem greatestPrimeFactor_eq_max' {m : ℕ} (hm : 1 < m) :
    greatestPrimeFactor m =
      m.primeFactors.max' (Nat.nonempty_primeFactors.mpr hm) := by
  simp [greatestPrimeFactor, Nat.nonempty_primeFactors.mpr hm]

theorem greatestPrimeFactor_mem_primeFactors {m : ℕ} (hm : 1 < m) :
    greatestPrimeFactor m ∈ m.primeFactors := by
  rw [greatestPrimeFactor_eq_max' hm]
  exact Finset.max'_mem _ _

theorem greatestPrimeFactor_prime {m : ℕ} (hm : 1 < m) :
    (greatestPrimeFactor m).Prime :=
  Nat.prime_of_mem_primeFactors (greatestPrimeFactor_mem_primeFactors hm)

theorem greatestPrimeFactor_dvd {m : ℕ} (hm : 1 < m) :
    greatestPrimeFactor m ∣ m :=
  Nat.dvd_of_mem_primeFactors (greatestPrimeFactor_mem_primeFactors hm)

theorem prime_le_greatestPrimeFactor {m p : ℕ} (hm : 1 < m)
    (hp : p.Prime) (hpm : p ∣ m) : p ≤ greatestPrimeFactor m := by
  rw [greatestPrimeFactor_eq_max' hm]
  apply Finset.le_max'
  exact hp.mem_primeFactors hpm (ne_of_gt (lt_trans Nat.zero_lt_one hm))

theorem greatestPrimeFactor_mono_dvd {u v : ℕ} (hu : 1 < u) (hv0 : v ≠ 0)
    (huv : u ∣ v) :
    greatestPrimeFactor u ≤ greatestPrimeFactor v := by
  have hv : 1 < v := lt_of_lt_of_le hu (Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) huv)
  exact prime_le_greatestPrimeFactor hv (greatestPrimeFactor_prime hu)
    (dvd_trans (greatestPrimeFactor_dvd hu) huv)

/-- The `n`th Mersenne number. -/
def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

theorem mersenne_pos {n : ℕ} (hn : 0 < n) : 0 < mersenne n := by
  rw [mersenne, Nat.sub_pos_iff_lt]
  exact one_lt_pow₀ one_lt_two hn.ne'

theorem one_lt_mersenne {n : ℕ} (hn : 1 < n) : 1 < mersenne n := by
  have hpow : 2 ^ 2 ≤ 2 ^ n := pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) hn
  norm_num [mersenne] at hpow ⊢
  omega

theorem mersenne_odd {n : ℕ} (hn : 0 < n) : Odd (mersenne n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  refine ⟨2 ^ k - 1, ?_⟩
  rw [mersenne, pow_succ]
  have : 1 ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  omega

/-- The positive integer obtained by evaluating the `n`th cyclotomic
polynomial at `2`.  The `natAbs` presentation interacts directly with
Mathlib's integral cyclotomic API and is total also at `n = 0`. -/
noncomputable def cyclotomicValue (n : ℕ) : ℕ :=
  ((Polynomial.cyclotomic n ℤ).eval 2).natAbs

theorem cyclotomicValue_pos (n : ℕ) : 0 < cyclotomicValue n := by
  rw [cyclotomicValue, Int.natAbs_pos]
  exact ne_of_gt (Polynomial.cyclotomic_pos' n (by norm_num : (1 : ℤ) < 2))

/-- The cyclotomic value `Φₙ(2)` is a divisor of the Mersenne number
`2^n - 1`. -/
theorem cyclotomicValue_dvd_mersenne (n : ℕ) :
    cyclotomicValue n ∣ mersenne n := by
  have hdiv :
      (Polynomial.cyclotomic n ℤ).eval 2 ∣
        (Polynomial.X ^ n - 1 : Polynomial ℤ).eval 2 :=
    Polynomial.eval_dvd (Polynomial.cyclotomic.dvd_X_pow_sub_one n ℤ)
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one] at hdiv
  rw [cyclotomicValue, mersenne]
  convert Int.natAbs_dvd_natAbs.mpr hdiv using 1
  have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  exact (Int.natAbs_natCast_sub_natCast_of_ge hpow).symm

/-- A prime divisor of `Φₙ(2)` makes `2` a root of the `n`th cyclotomic
polynomial modulo that prime. -/
theorem isRoot_cyclotomic_two_of_prime_dvd_cyclotomicValue {n p : ℕ}
    (hp : p.Prime) (hpd : p ∣ cyclotomicValue n) :
    Polynomial.IsRoot (Polynomial.cyclotomic n (ZMod p))
      (Nat.castRingHom (ZMod p) 2) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hcast : (Nat.castRingHom (ZMod p)) 2 =
      (Int.castRingHom (ZMod p)) (2 : ℤ) := by norm_num
  rw [Polynomial.IsRoot.def, ← Polynomial.map_cyclotomic_int n (ZMod p),
    Polynomial.eval_map, hcast, Polynomial.eval₂_hom,
    Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
  apply Int.dvd_natAbs.1
  exact_mod_cast hpd

/-- Apart from the exceptional primes dividing the index, every prime
divisor of `Φₙ(2)` is congruent to `1` modulo `n`. -/
theorem index_dvd_prime_sub_one_of_prime_dvd_cyclotomicValue {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpd : p ∣ cyclotomicValue n)
    (hpn : ¬p ∣ n) : n ∣ p - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hroot := isRoot_cyclotomic_two_of_prime_dvd_cyclotomicValue hp hpd
  have hcoprime : (2 : ℕ).Coprime p :=
    Polynomial.coprime_of_root_cyclotomic hn hroot
  have htwo : (2 : ZMod p) ≠ 0 := by
    exact mt (CharP.cast_eq_zero_iff (ZMod p) p 2).1
      (hp.coprime_iff_not_dvd.mp hcoprime.symm)
  have horder : orderOf (2 : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one htwo
  letI : NeZero (n : ZMod p) := NeZero.of_not_dvd (ZMod p) hpn
  have hnorder : n = orderOf (2 : ZMod p) :=
    (Polynomial.isRoot_cyclotomic_iff.mp hroot).eq_orderOf
  rwa [hnorder]

/-- In arbitrary characteristic, the index of a cyclotomic root can differ
from its multiplicative order only by a power of the characteristic.  This is
the form needed to treat uniformly both the ordinary primes `p ≡ 1 (mod n)`
and the single possible index-dividing prime. -/
theorem index_eq_prime_pow_mul_orderOf_two {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpd : p ∣ cyclotomicValue n) :
    ∃ k : ℕ, n = p ^ k * orderOf (2 : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, m, hpm, hnm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
  have hm : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hm
    rw [hm, mul_zero] at hnm
    omega
  letI : NeZero (m : ZMod p) := NeZero.of_not_dvd (ZMod p) hpm
  have hroot := isRoot_cyclotomic_two_of_prime_dvd_cyclotomicValue hp hpd
  rw [hnm] at hroot
  have hprimitive : IsPrimitiveRoot (2 : ZMod p) m :=
    Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hroot
  exact ⟨k, hnm.trans (congrArg (p ^ k * ·) hprimitive.eq_orderOf)⟩

/-- The order occurring in the characteristic-`p` classification always
divides `p - 1`. -/
theorem orderOf_two_dvd_prime_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    orderOf (2 : ZMod p) ∣ p - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    apply hp2
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp h)
  exact ZMod.orderOf_dvd_card_sub_one htwo

/-- `p`-adic valuation is monotone under divisibility away from zero. -/
theorem padicValNat_mono_dvd {p a b : ℕ} (hp : p.Prime) (hb : b ≠ 0)
    (hab : a ∣ b) : padicValNat p a ≤ padicValNat p b := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [← padicValNat_dvd_iff_le hb]
  exact (pow_padicValNat_dvd (p := p) (n := a)).trans hab

/-- Every prime factor of a positive-index cyclotomic value at `2` is odd. -/
theorem prime_dvd_cyclotomicValue_odd {n p : ℕ} (hn : 0 < n)
    (hp : p.Prime) (hpd : p ∣ cyclotomicValue n) : Odd p := by
  apply hp.odd_of_ne_two
  intro hp2
  subst p
  exact (mersenne_odd hn).not_two_dvd_nat
    (hpd.trans (cyclotomicValue_dvd_mersenne n))

/-- A prime valuation of `Φₙ(2)` is controlled by the Fermat quotient at
that prime, plus the valuation already present in the index.  This lemma is
the arithmetic bridge between the cyclotomic factorization and Yamada's
two-logarithm estimate. -/
theorem cyclotomicValue_padicVal_le_fermat_add_index {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpd : p ∣ cyclotomicValue n) :
    padicValNat p (cyclotomicValue n) ≤
      padicValNat p (mersenne (p - 1)) + padicValNat p n := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := prime_dvd_cyclotomicValue_odd hn hp hpd
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpodd
  obtain ⟨k, hnk⟩ := index_eq_prime_pow_mul_orderOf_two hn hp hpd
  let m := orderOf (2 : ZMod p)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    apply hp2
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp h)
  have hmdvd : m ∣ p - 1 := orderOf_two_dvd_prime_sub_one hp hp2
  have hp1pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hmdvd hp1pos
  have hmlt : m < p := by
    exact lt_of_le_of_lt (Nat.le_of_dvd hp1pos hmdvd) (Nat.sub_lt hp.pos zero_lt_one)
  have hpnotm : ¬p ∣ m := by
    intro hpm
    exact (not_le_of_gt hmlt) (Nat.le_of_dvd hmpos hpm)
  have hp_mersenne_m : p ∣ mersenne m := by
    have hz : ((2 ^ m : ℕ) : ZMod p) = (1 : ZMod p) := by
      simpa [m] using pow_orderOf_eq_one (2 : ZMod p)
    have hz' : ((1 : ℕ) : ZMod p) = ((2 ^ m : ℕ) : ZMod p) := by
      simpa only [Nat.cast_one] using hz.symm
    have hmod : 1 ≡ 2 ^ m [MOD p] :=
      (ZMod.natCast_eq_natCast_iff 1 (2 ^ m) p).mp hz'
    exact (Nat.modEq_iff_dvd' (one_le_pow₀ (by norm_num))).mp hmod
  have hpnotpow : ¬p ∣ 2 ^ m := by
    intro hpow
    apply hp2
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow hpow)
  have hpowne : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hlte := padicValNat.pow_sub_pow hpodd
    (x := 2 ^ m) (y := 1) (one_lt_pow₀ one_lt_two hmpos.ne')
    (by simpa [mersenne] using hp_mersenne_m) hpnotpow hpowne
  have hval_mersenne :
      padicValNat p (mersenne n) = padicValNat p (mersenne m) + k := by
    have hpowexp : (2 ^ m) ^ (p ^ k) = 2 ^ n := by
      rw [← pow_mul, hnk, mul_comm]
    rw [one_pow, hpowexp, padicValNat.prime_pow] at hlte
    simpa [mersenne] using hlte
  have hval_index : padicValNat p n = k := by
    rw [hnk, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hmpos.ne',
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hpnotm, add_zero]
  have hcyclo_le :
      padicValNat p (cyclotomicValue n) ≤ padicValNat p (mersenne n) :=
    padicValNat_mono_dvd hp (mersenne_pos hn).ne'
      (cyclotomicValue_dvd_mersenne n)
  have hm_dvd : mersenne m ∣ mersenne (p - 1) := by
    exact Nat.pow_sub_one_dvd_pow_sub_one 2 hmdvd
  have hfermat_ne : mersenne (p - 1) ≠ 0 := by
    apply (mersenne_pos (Nat.sub_pos_of_lt hp.one_lt)).ne'
  have hsmall_le :
      padicValNat p (mersenne m) ≤ padicValNat p (mersenne (p - 1)) :=
    padicValNat_mono_dvd hp hfermat_ne hm_dvd
  rw [hval_mersenne] at hcyclo_le
  rw [hval_index]
  exact hcyclo_le.trans (Nat.add_le_add_right hsmall_le k)

/-- If a prime factor of `Φₙ(2)` also divides the index, it is the greatest
prime factor of the index.  In particular there is at most one such
exceptional prime. -/
theorem prime_dvd_cyclotomicValue_and_index_eq_greatestPrimeFactor
    {n p : ℕ} (hn : 1 < n) (hp : p.Prime)
    (hpc : p ∣ cyclotomicValue n) (hpn : p ∣ n) :
    p = greatestPrimeFactor n := by
  have hpodd : Odd p := prime_dvd_cyclotomicValue_odd (lt_trans zero_lt_one hn) hp hpc
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpodd
  obtain ⟨k, hnk⟩ :=
    index_eq_prime_pow_mul_orderOf_two (lt_trans zero_lt_one hn) hp hpc
  let m := orderOf (2 : ZMod p)
  have hmdvd : m ∣ p - 1 := orderOf_two_dvd_prime_sub_one hp hp2
  have hp1pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hmdvd hp1pos
  have hmlt : m < p :=
    lt_of_le_of_lt (Nat.le_of_dvd hp1pos hmdvd) (Nat.sub_lt hp.pos zero_lt_one)
  have hpnotm : ¬p ∣ m := by
    intro hpm
    exact (not_le_of_gt hmlt) (Nat.le_of_dvd hmpos hpm)
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk
    rw [hk, pow_zero, one_mul] at hnk
    apply hpnotm
    change p ∣ orderOf (2 : ZMod p)
    rw [← hnk]
    exact hpn
  have hqle : ∀ q : ℕ, q.Prime → q ∣ n → q ≤ p := by
    intro q hq hqn
    have hqprod : q ∣ p ^ k * m := hnk ▸ hqn
    rcases hq.dvd_mul.mp hqprod with hqpk | hqm
    · have hqp : q ∣ p := hq.dvd_of_dvd_pow hqpk
      exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp ▸ le_rfl
    · exact (Nat.le_of_dvd hmpos hqm).trans hmlt.le
  apply le_antisymm
  · exact prime_le_greatestPrimeFactor hn hp hpn
  · exact hqle (greatestPrimeFactor n) (greatestPrimeFactor_prime hn)
      (greatestPrimeFactor_dvd hn)

/-- If the Mersenne greatest prime factor is at most `C n`, then `Φₙ(2)`
has at most `C+1` distinct prime factors: at most `C` ordinary factors
`a n + 1`, and at most one exceptional index-dividing factor. -/
theorem card_primeFactors_cyclotomicValue_le_of_greatestPrimeFactor_le_mul
    {n C : ℕ} (hn : 1 < n)
    (hP : greatestPrimeFactor (mersenne n) ≤ C * n) :
    (cyclotomicValue n).primeFactors.card ≤ C + 1 := by
  classical
  let exceptional : Finset ℕ := {greatestPrimeFactor n}
  let ordinary : Finset ℕ := (Finset.range C).image (fun a => a * n + 1)
  have hsubset : (cyclotomicValue n).primeFactors ⊆ exceptional ∪ ordinary := by
    intro p hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hpd : p ∣ cyclotomicValue n := Nat.dvd_of_mem_primeFactors hpmem
    by_cases hpn : p ∣ n
    · have heq :=
        prime_dvd_cyclotomicValue_and_index_eq_greatestPrimeFactor hn hp hpd hpn
      exact Finset.mem_union_left ordinary (by simpa [exceptional, heq])
    · have hidx : n ∣ p - 1 :=
        index_dvd_prime_sub_one_of_prime_dvd_cyclotomicValue
          (lt_trans zero_lt_one hn) hp hpd hpn
      let a := (p - 1) / n
      have ha_mul : a * n = p - 1 := Nat.div_mul_cancel hidx
      have ha_eq : a * n + 1 = p := by
        have hpone : 1 ≤ p := hp.one_lt.le
        omega
      have hp_le : p ≤ greatestPrimeFactor (mersenne n) :=
        prime_le_greatestPrimeFactor (one_lt_mersenne hn) hp
          (hpd.trans (cyclotomicValue_dvd_mersenne n))
      have ha_mul_lt : a * n < C * n := by
        have := hp_le.trans hP
        omega
      have ha_lt : a < C :=
        (Nat.mul_lt_mul_right (lt_trans zero_lt_one hn)).mp ha_mul_lt
      apply Finset.mem_union_right exceptional
      exact Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr ha_lt, ha_eq⟩
  calc
    (cyclotomicValue n).primeFactors.card ≤ (exceptional ∪ ordinary).card :=
      Finset.card_le_card hsubset
    _ ≤ exceptional.card + ordinary.card := Finset.card_union_le exceptional ordinary
    _ ≤ 1 + C := by
      apply Nat.add_le_add
      · simp [exceptional]
      · exact (Finset.card_image_le.trans_eq (Finset.card_range C))
    _ = C + 1 := by omega

/-- Summing a uniform bound for the logarithmic contribution of every
prime factor gives a bound for the logarithm of the whole cyclotomic value. -/
theorem cyclotomicValue_log_le_card_mul_of_factor_term_le {n : ℕ} {E : ℝ}
    (hE : ∀ p ∈ (cyclotomicValue n).primeFactors,
      ((cyclotomicValue n).factorization p : ℝ) * Real.log (p : ℝ) ≤ E) :
    Real.log (cyclotomicValue n : ℝ) ≤
      ((cyclotomicValue n).primeFactors.card : ℝ) * E := by
  rw [Real.log_nat_eq_sum_factorization]
  change (∑ p ∈ (cyclotomicValue n).primeFactors,
    ((cyclotomicValue n).factorization p : ℝ) * Real.log (p : ℝ)) ≤ _
  calc
    _ ≤ ∑ _p ∈ (cyclotomicValue n).primeFactors, E := by
      apply Finset.sum_le_sum
      intro p hp
      exact hE p hp
    _ = ((cyclotomicValue n).primeFactors.card : ℝ) * E := by simp

/-- The part of a prime valuation already present in the index contributes
at most the logarithm of the index itself. -/
theorem padicValNat_mul_log_le_log {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    (padicValNat p n : ℝ) * Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ^ padicValNat p n ∣ n := pow_padicValNat_dvd
  have hpowNat : p ^ padicValNat p n ≤ n := Nat.le_of_dvd hn hdvd
  have hpow : (p : ℝ) ^ padicValNat p n ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog := Real.log_le_log (pow_pos hpR _) hpow
  simpa [Real.log_pow] using hlog

/-- A uniform elementary estimate for `p / log p` when an odd prime `p`
is bounded by a fixed multiple of the index.  The split at `sqrt n` is what
makes the bound uniform over all prime divisors of `Φₙ(2)`. -/
theorem prime_div_log_le_sqrt_add {n p C : ℕ} (hn : 1 < n)
    (hp : p.Prime) (hpodd : Odd p) (hpC : p ≤ C * n) :
    (p : ℝ) / Real.log (p : ℝ) ≤
      Real.sqrt (n : ℝ) / Real.log 3 +
        (2 * (C : ℝ) * (n : ℝ)) / Real.log (n : ℝ) := by
  have hp3 : 3 ≤ p := by
    have hp2 : 2 ≤ p := hp.two_le
    have hpne : p ≠ 2 := by
      intro h
      subst p
      norm_num at hpodd
    omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hlog3p : Real.log (3 : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) hp3R
  have hlogp : 0 < Real.log (p : ℝ) := hlog3.trans_le hlog3p
  have hpCR : (p : ℝ) ≤ (C : ℝ) * (n : ℝ) := by
    exact_mod_cast hpC
  by_cases hsmall : (p : ℝ) ≤ Real.sqrt (n : ℝ)
  · have hratio : (p : ℝ) / Real.log (p : ℝ) ≤
        Real.sqrt (n : ℝ) / Real.log 3 := by
      apply (div_le_div_iff₀ hlogp hlog3).2
      calc
        (p : ℝ) * Real.log 3 ≤ Real.sqrt (n : ℝ) * Real.log 3 :=
          mul_le_mul_of_nonneg_right hsmall hlog3.le
        _ ≤ Real.sqrt (n : ℝ) * Real.log (p : ℝ) :=
          mul_le_mul_of_nonneg_left hlog3p (Real.sqrt_nonneg _)
    exact hratio.trans (le_add_of_nonneg_right
      (div_nonneg (by positivity) hlogn.le))
  · have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hlogsqrt : Real.log (Real.sqrt (n : ℝ)) ≤ Real.log (p : ℝ) :=
      Real.log_le_log hsqrtpos (le_of_not_ge hsmall)
    rw [Real.log_sqrt (by positivity)] at hlogsqrt
    have hfirst : (p : ℝ) / Real.log (p : ℝ) ≤
        (2 * (p : ℝ)) / Real.log (n : ℝ) := by
      apply (div_le_div_iff₀ hlogp hlogn).2
      have hmul := mul_le_mul_of_nonneg_left hlogsqrt hpR.le
      nlinarith
    have hsecond : (2 * (p : ℝ)) / Real.log (n : ℝ) ≤
        (2 * (C : ℝ) * (n : ℝ)) / Real.log (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hlogn.le
      nlinarith
    exact (hfirst.trans hsecond).trans (le_add_of_nonneg_left
      (div_nonneg (Real.sqrt_nonneg _) hlog3.le))

/-- The fixed-`C` upper bound for `log Φₙ(2)` obtained by combining the
cyclotomic valuation lemma with any uniform Fermat-quotient estimate of
Yamada's shape. -/
theorem cyclotomicValue_log_upper_of_fermat_quotient_bound
    {n C : ℕ} {K : ℝ} (hn : 1 < n) (hCn : C ≤ n)
    (hP : greatestPrimeFactor (mersenne n) ≤ C * n) (hK : 0 ≤ K)
    (hF : ∀ p : ℕ, p.Prime →
      (padicValNat p (mersenne (p - 1)) : ℝ) * Real.log (p : ℝ) ≤
        K * ((p : ℝ) / Real.log (p : ℝ) + Real.log (p : ℝ))) :
    Real.log (cyclotomicValue n : ℝ) ≤
      ((C + 1 : ℕ) : ℝ) *
        (K * (Real.sqrt (n : ℝ) / Real.log 3 +
            (2 * (C : ℝ) * (n : ℝ)) / Real.log (n : ℝ) +
            2 * Real.log (n : ℝ)) + Real.log (n : ℝ)) := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  let E : ℝ := K * (Real.sqrt (n : ℝ) / Real.log 3 +
      (2 * (C : ℝ) * (n : ℝ)) / Real.log (n : ℝ) +
      2 * Real.log (n : ℝ)) + Real.log (n : ℝ)
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hsum : Real.log (cyclotomicValue n : ℝ) ≤
      ((cyclotomicValue n).primeFactors.card : ℝ) * E := by
    apply cyclotomicValue_log_le_card_mul_of_factor_term_le
    intro p hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hpd : p ∣ cyclotomicValue n := Nat.dvd_of_mem_primeFactors hpmem
    have hpodd : Odd p := prime_dvd_cyclotomicValue_odd hn0 hp hpd
    have hpM : p ∣ mersenne n := hpd.trans (cyclotomicValue_dvd_mersenne n)
    have hpP : p ≤ greatestPrimeFactor (mersenne n) :=
      prime_le_greatestPrimeFactor (one_lt_mersenne hn) hp hpM
    have hpC : p ≤ C * n := hpP.trans hP
    have hratio := prime_div_log_le_sqrt_add hn hp hpodd hpC
    have hCmul : C * n ≤ n * n := Nat.mul_le_mul_right n hCn
    have hpnn : p ≤ n ^ 2 := by
      simpa [pow_two] using hpC.trans hCmul
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpnnR : (p : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hpnn
    have hlogp : Real.log (p : ℝ) ≤ 2 * Real.log (n : ℝ) := by
      have h := Real.log_le_log hpR hpnnR
      simpa [Real.log_pow] using h
    have hval := cyclotomicValue_padicVal_le_fermat_add_index hn0 hp hpd
    have hvalR : (padicValNat p (cyclotomicValue n) : ℝ) ≤
        (padicValNat p (mersenne (p - 1)) : ℝ) +
          (padicValNat p n : ℝ) := by
      exact_mod_cast hval
    have hlogp0 : 0 ≤ Real.log (p : ℝ) :=
      (Real.log_pos (by exact_mod_cast hp.one_lt)).le
    rw [Nat.factorization_def _ hp]
    calc
      (padicValNat p (cyclotomicValue n) : ℝ) * Real.log (p : ℝ) ≤
          ((padicValNat p (mersenne (p - 1)) : ℝ) +
            (padicValNat p n : ℝ)) * Real.log (p : ℝ) :=
        mul_le_mul_of_nonneg_right hvalR hlogp0
      _ = (padicValNat p (mersenne (p - 1)) : ℝ) * Real.log (p : ℝ) +
          (padicValNat p n : ℝ) * Real.log (p : ℝ) := by ring
      _ ≤ K * ((p : ℝ) / Real.log (p : ℝ) + Real.log (p : ℝ)) +
          Real.log (n : ℝ) :=
        add_le_add (hF p hp) (padicValNat_mul_log_le_log hn0 hp)
      _ ≤ E := by
        dsimp [E]
        have hadd := add_le_add hratio hlogp
        exact add_le_add (mul_le_mul_of_nonneg_left hadd hK) le_rfl
  have hcard :=
    card_primeFactors_cyclotomicValue_le_of_greatestPrimeFactor_le_mul hn hP
  have hcardR : ((cyclotomicValue n).primeFactors.card : ℝ) ≤ (C + 1 : ℕ) := by
    exact_mod_cast hcard
  exact hsum.trans (mul_le_mul_of_nonneg_right hcardR hE)

/-- For a finite set of distinct primes, the product of `p / (p-1)` is
at most one plus the number of primes.  This elementary telescoping bound
is the quantitative input needed from Euler's product for `φ`. -/
theorem prod_primes_le_card_succ_mul_prod_pred (s : Finset ℕ)
    (hsprime : ∀ p ∈ s, p.Prime) :
    s.prod id ≤ (s.card + 1) * s.prod (fun p => p - 1) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
      by_cases hs : s.Nonempty
      · let p := s.max' hs
        let t := s.erase p
        have hp_mem : p ∈ s := by
          exact Finset.max'_mem s hs
        have ht_ssub : t ⊂ s := Finset.erase_ssubset hp_mem
        have htprime : ∀ q ∈ t, q.Prime := by
          intro q hq
          exact hsprime q (Finset.erase_subset p s hq)
        have hi := ih t ht_ssub htprime
        have ht_Ico : t ⊆ Finset.Ico 2 p := by
          intro q hq
          have hqs : q ∈ s := Finset.erase_subset p s hq
          have hqne : q ≠ p := (Finset.mem_erase.mp hq).1
          have hqle : q ≤ p := Finset.le_max' s q hqs
          exact Finset.mem_Ico.mpr ⟨(hsprime q hqs).two_le,
            lt_of_le_of_ne hqle hqne⟩
        have htcard : t.card ≤ p - 2 := by
          simpa using Finset.card_le_card ht_Ico
        have hpprime : p.Prime := hsprime p hp_mem
        have hp_card : t.card + 2 ≤ p := by
          have hp2le : 2 ≤ p := hpprime.two_le
          omega
        have hratio : (t.card + 1) * p ≤ (t.card + 2) * (p - 1) := by
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hp_card
          rw [hd]
          have hsub : t.card + 2 + d - 1 = t.card + 1 + d := by omega
          rw [hsub]
          nlinarith
        rw [← Finset.prod_erase_mul s id hp_mem,
          ← Finset.prod_erase_mul s (fun q => q - 1) hp_mem]
        have hscard : s.card = t.card + 1 := by
          change s.card = (s.erase p).card + 1
          rw [Finset.card_erase_of_mem hp_mem]
          have hspos : 0 < s.card := Finset.card_pos.mpr hs
          omega
        rw [hscard]
        change t.prod id * p ≤
          (t.card + 1 + 1) * (t.prod (fun q => q - 1) * (p - 1))
        calc
          t.prod id * p ≤ ((t.card + 1) * t.prod (fun q => q - 1)) * p :=
            Nat.mul_le_mul_right p hi
          _ = t.prod (fun q => q - 1) * ((t.card + 1) * p) := by ring
          _ ≤ t.prod (fun q => q - 1) * ((t.card + 2) * (p - 1)) :=
            Nat.mul_le_mul_left _ hratio
          _ = (t.card + 1 + 1) * (t.prod (fun q => q - 1) * (p - 1)) := by ring
      · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.prod_empty,
          Finset.card_empty]
        norm_num

/-- Distinct primes grow at least as fast as the shifted factorial: a set
of `r` primes has product at least `(r+1)!`. -/
theorem card_succ_factorial_le_prod_primes (s : Finset ℕ)
    (hsprime : ∀ p ∈ s, p.Prime) :
    (s.card + 1).factorial ≤ s.prod id := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
      by_cases hs : s.Nonempty
      · let p := s.max' hs
        let t := s.erase p
        have hp_mem : p ∈ s := Finset.max'_mem s hs
        have ht_ssub : t ⊂ s := Finset.erase_ssubset hp_mem
        have htprime : ∀ q ∈ t, q.Prime := by
          intro q hq
          exact hsprime q (Finset.erase_subset p s hq)
        have hi := ih t ht_ssub htprime
        have ht_Ico : t ⊆ Finset.Ico 2 p := by
          intro q hq
          have hqs : q ∈ s := Finset.erase_subset p s hq
          have hqne : q ≠ p := (Finset.mem_erase.mp hq).1
          have hqle : q ≤ p := Finset.le_max' s q hqs
          exact Finset.mem_Ico.mpr ⟨(hsprime q hqs).two_le,
            lt_of_le_of_ne hqle hqne⟩
        have htcard : t.card ≤ p - 2 := by
          simpa using Finset.card_le_card ht_Ico
        have hpprime : p.Prime := hsprime p hp_mem
        have hp_card : t.card + 2 ≤ p := by
          have hp2le : 2 ≤ p := hpprime.two_le
          omega
        have hscard : s.card = t.card + 1 := by
          change s.card = (s.erase p).card + 1
          rw [Finset.card_erase_of_mem hp_mem]
          have hspos : 0 < s.card := Finset.card_pos.mpr hs
          omega
        rw [← Finset.prod_erase_mul s id hp_mem, hscard]
        change (t.card + 1 + 1).factorial ≤ t.prod id * p
        rw [Nat.factorial_succ]
        have hadd : t.card + 1 + 1 = t.card + 2 := by omega
        simpa [hadd, Nat.mul_comm] using Nat.mul_le_mul hp_card hi
      · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

theorem card_primeFactors_eq_cardDistinctFactors (n : ℕ) :
    n.primeFactors.card = ArithmeticFunction.cardDistinctFactors n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    Nat.toFinset_factors]

theorem cardDistinctFactors_succ_factorial_le_self {n : ℕ} (hn : n ≠ 0) :
    (ArithmeticFunction.cardDistinctFactors n + 1).factorial ≤ n := by
  have hprod : (n.primeFactors.card + 1).factorial ≤ n.primeFactors.prod id :=
    card_succ_factorial_le_prod_primes n.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hdiv : n.primeFactors.prod id ∣ n := Nat.prod_primeFactors_dvd n
  have hprodle : n.primeFactors.prod id ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv
  rw [card_primeFactors_eq_cardDistinctFactors] at hprod
  exact hprod.trans hprodle

/-- The elementary factorial bound implies the precise growth fact needed
below: `log n / (ω(n)+1)` tends to infinity. -/
theorem log_div_cardDistinctFactors_succ_tendsto_atTop :
    Tendsto
      (fun n : ℕ =>
        Real.log (n : ℝ) /
          (ArithmeticFunction.cardDistinctFactors n + 1 : ℝ))
      atTop atTop := by
  let logNat : ℕ → ℝ := fun n => Real.log (n : ℝ)
  have hlogNat : Tendsto logNat atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop.mpr fun A => ?_
  let B : ℝ := max A 0
  obtain ⟨K, hKlog⟩ : ∃ K : ℕ, B + 1 ≤ Real.log (K : ℝ) :=
    (hlogNat.eventually_ge_atTop (B + 1)).exists
  have hBnonneg : 0 ≤ B := le_max_right A 0
  have hAleB : A ≤ B := le_max_left A 0
  have hKlogpos : 0 < Real.log (K : ℝ) := lt_of_lt_of_le (by linarith) hKlog
  have hKone : 1 < K := by
    exact_mod_cast (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ K)).mp hKlogpos
  filter_upwards [hlogNat.eventually_ge_atTop (B * K),
    eventually_gt_atTop (0 : ℕ)] with n hnlog hnpos
  let k : ℕ := ArithmeticFunction.cardDistinctFactors n + 1
  have hkpos : 0 < k := by simp [k]
  have hfac : k.factorial ≤ n := by
    simpa [k] using cardDistinctFactors_succ_factorial_le_self hnpos.ne'
  have hlogfac : Real.log (k.factorial : ℝ) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hfac
  have hstirling := Stirling.le_log_factorial_stirling hkpos.ne'
  have hlogk_nonneg : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hkpos)
  have hlogtwopi_nonneg : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  have hbasic :
      (k : ℝ) * Real.log (k : ℝ) - k ≤ Real.log (k.factorial : ℝ) := by
    linarith
  have hAk_log : A * (k : ℝ) ≤ Real.log (n : ℝ) := by
    by_cases hkK : K ≤ k
    · have hlogKle : Real.log (K : ℝ) ≤ Real.log (k : ℝ) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hkK
      have hBlog : B ≤ Real.log (k : ℝ) - 1 := by linarith
      have hBmul : B * (k : ℝ) ≤
          (Real.log (k : ℝ) - 1) * k :=
        mul_le_mul_of_nonneg_right hBlog (by positivity)
      calc
        A * (k : ℝ) ≤ B * k :=
          mul_le_mul_of_nonneg_right hAleB (by positivity)
        _ ≤ (Real.log (k : ℝ) - 1) * k := hBmul
        _ = (k : ℝ) * Real.log (k : ℝ) - k := by ring
        _ ≤ Real.log (k.factorial : ℝ) := hbasic
        _ ≤ Real.log (n : ℝ) := hlogfac
    · have hkK' : k ≤ K := Nat.le_of_lt (lt_of_not_ge hkK)
      calc
        A * (k : ℝ) ≤ B * k :=
          mul_le_mul_of_nonneg_right hAleB (by positivity)
        _ ≤ B * K := mul_le_mul_of_nonneg_left (by exact_mod_cast hkK') hBnonneg
        _ ≤ Real.log (n : ℝ) := hnlog
  have hkcast : (k : ℝ) =
      (ArithmeticFunction.cardDistinctFactors n : ℝ) + 1 := by simp [k]
  rw [← hkcast]
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < k)).2 (by
    simpa [mul_comm] using hAk_log)

/-- A deliberately elementary lower bound for Euler's totient.  If `ω(n)`
is the number of distinct prime factors, then `n / φ(n) ≤ ω(n)+1`. -/
theorem self_le_totient_mul_cardDistinctFactors_succ (n : ℕ) :
    n ≤ Nat.totient n * (ArithmeticFunction.cardDistinctFactors n + 1) := by
  by_cases hn : n = 0
  · simp [hn]
  let s := n.primeFactors
  let P := s.prod id
  let Q := s.prod (fun p => p - 1)
  have hsprime : ∀ p ∈ s, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  have hprod : P ≤ (s.card + 1) * Q :=
    prod_primes_le_card_succ_mul_prod_pred s hsprime
  have hQpos : 0 < Q := by
    apply Finset.prod_pos
    intro p hp
    exact Nat.sub_pos_of_lt (hsprime p hp).one_lt
  have hEuler : Nat.totient n * P = n * Q := by
    simpa [s, P, Q] using Nat.totient_mul_prod_primeFactors n
  have hcross : n * Q ≤
      (Nat.totient n * (s.card + 1)) * Q := by
    calc
      n * Q = Nat.totient n * P := hEuler.symm
      _ ≤ Nat.totient n * ((s.card + 1) * Q) :=
        Nat.mul_le_mul_left _ hprod
      _ = (Nat.totient n * (s.card + 1)) * Q := by ring
  have hmain : n ≤ Nat.totient n * (s.card + 1) :=
    le_of_mul_le_mul_right hcross hQpos
  simpa [s, card_primeFactors_eq_cardDistinctFactors] using hmain

/-- Consequently `φ(n) log n / n` tends to infinity. -/
theorem totient_mul_log_div_self_tendsto_atTop :
    Tendsto
      (fun n : ℕ =>
        (Nat.totient n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop atTop := by
  apply tendsto_atTop_mono' atTop _ log_div_cardDistinctFactors_succ_tendsto_atTop
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  let k : ℕ := ArithmeticFunction.cardDistinctFactors n + 1
  have hk : 0 < k := by simp [k]
  have htot := self_le_totient_mul_cardDistinctFactors_succ n
  have htot' : (n : ℝ) ≤ (Nat.totient n : ℝ) * k := by
    exact_mod_cast htot
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hkcast : (k : ℝ) =
      (ArithmeticFunction.cardDistinctFactors n : ℝ) + 1 := by simp [k]
  rw [← hkcast]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < k)
    (by positivity : (0 : ℝ) < n)).2
  have hmul := mul_le_mul_of_nonneg_left htot' hlog
  nlinarith

/-- A small explicit factorial estimate used to dispose of the finite range
in which `φ(n)` could be less than four. -/
theorem six_mul_self_le_factorial {k : ℕ} (hk : 4 ≤ k) :
    6 * k ≤ k.factorial := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk4 ih =>
      rw [Nat.factorial_succ]
      have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk4
      have hsix : 6 ≤ k.factorial := by
        exact (Nat.le_mul_of_pos_right 6 hkpos).trans ih
      calc
        6 * (k + 1) = (k + 1) * 6 := by ring
        _ ≤ (k + 1) * k.factorial := Nat.mul_le_mul_left _ hsix

/-- In particular, all indices above nine have totient at least four. -/
theorem four_le_totient_of_nine_lt {n : ℕ} (hn : 9 < n) :
    4 ≤ Nat.totient n := by
  by_contra hφ
  have hφ3 : Nat.totient n ≤ 3 := by omega
  let k : ℕ := ArithmeticFunction.cardDistinctFactors n + 1
  have hkpos : 0 < k := by simp [k]
  have hnφ := self_le_totient_mul_cardDistinctFactors_succ n
  have hn3k : n ≤ 3 * k := by
    calc
      n ≤ Nat.totient n * k := by simpa [k] using hnφ
      _ ≤ 3 * k := Nat.mul_le_mul_right k hφ3
  have hfact : k.factorial ≤ n := by
    simpa [k] using
      (cardDistinctFactors_succ_factorial_le_self (n := n) (by omega))
  by_cases hk4 : 4 ≤ k
  · have hsix := six_mul_self_le_factorial hk4
    have : 6 * k ≤ 3 * k := hsix.trans (hfact.trans hn3k)
    omega
  · have hk3 : k ≤ 3 := by omega
    have : n ≤ 9 := hn3k.trans (Nat.mul_le_mul_left 3 hk3)
    omega

/-- The normalized cyclotomic lower bound tends to positive infinity. -/
theorem cyclotomic_lower_normalized_tendsto_atTop :
    Tendsto
      (fun n : ℕ =>
        ((Nat.totient n : ℝ) * Real.log 2 / 8) *
          Real.log (n : ℝ) / (n : ℝ))
      atTop atTop := by
  have hc : 0 < Real.log (2 : ℝ) / 8 :=
    div_pos (Real.log_pos (by norm_num)) (by norm_num)
  convert totient_mul_log_div_self_tendsto_atTop.const_mul_atTop hc using 1
  funext n
  ring

/-- The logarithmic square is negligible compared with the index. -/
theorem log_sq_div_self_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ))
      atTop (𝓝 0) := by
  simpa [Function.comp_def, id_eq] using
    (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

/-- The other error term in the fixed-`C` argument is also negligible. -/
theorem sqrt_mul_log_div_self_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        Real.sqrt (n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hbase : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / Real.sqrt (n : ℝ))
      atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  refine hbase.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
  field_simp [hsqrt]
  rw [Real.sq_sqrt hnR.le]

/-- After multiplication by `log n / n`, the fixed-`C` cyclotomic upper
bound tends to a finite constant. -/
theorem fixedC_cyclotomic_upper_normalized_tendsto (C : ℕ) (K : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (((C + 1 : ℕ) : ℝ) *
          (K * (Real.sqrt (n : ℝ) / Real.log 3 +
              (2 * (C : ℝ) * (n : ℝ)) / Real.log (n : ℝ) +
              2 * Real.log (n : ℝ)) + Real.log (n : ℝ))) *
            Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 (((C + 1 : ℕ) : ℝ) * K * (2 * (C : ℝ)))) := by
  have ha := sqrt_mul_log_div_self_tendsto_zero
  have hb := log_sq_div_self_tendsto_zero
  have hinside : Tendsto
      (fun n : ℕ =>
        (Real.sqrt (n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) / Real.log 3 +
          2 * (C : ℝ) + 2 * (Real.log (n : ℝ) ^ 2 / (n : ℝ)))
      atTop (𝓝 (2 * (C : ℝ))) := by
    simpa using ((ha.div_const (Real.log 3)).add tendsto_const_nhds).add
      (hb.const_mul 2)
  have hexpanded : Tendsto
      (fun n : ℕ =>
        ((C + 1 : ℕ) : ℝ) *
          (K * ((Real.sqrt (n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) /
              Real.log 3 + 2 * (C : ℝ) +
              2 * (Real.log (n : ℝ) ^ 2 / (n : ℝ))) +
            Real.log (n : ℝ) ^ 2 / (n : ℝ)))
      atTop (𝓝 (((C + 1 : ℕ) : ℝ) * K * (2 * (C : ℝ)))) := by
    simpa [mul_assoc] using (hinside.const_mul K).add hb |>.const_mul ((C + 1 : ℕ) : ℝ)
  refine hexpanded.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_trans zero_lt_one hn)
  have hlogn : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  field_simp [hnR.ne', hlogn]

/-- The next-to-leading coefficient of the `n`th cyclotomic polynomial is
the negative of the Möbius function.  We include the proof because this
small coefficient identity supplies the quantitative cyclotomic lower
bound used below. -/
theorem cyclotomic_nextCoeff_eq_neg_moebius (n : ℕ) :
    (Polynomial.cyclotomic n ℤ).nextCoeff = -ArithmeticFunction.moebius n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [Polynomial.cyclotomic_zero]
    have hμ0 : ArithmeticFunction.moebius 0 = 0 := by
      norm_num [ArithmeticFunction.moebius]
    rw [hμ0, neg_zero, ← Polynomial.C_1,
      Polynomial.nextCoeff_C_eq_zero]
  let f : ℕ → ℤ := fun d => (Polynomial.cyclotomic d ℤ).nextCoeff
  let g : ℕ → ℤ := fun d =>
    (Polynomial.X ^ d - 1 : Polynomial ℤ).nextCoeff
  have hsum : ∀ d > 0, ∑ i ∈ d.divisors, f i = g d := by
    intro d hd
    rw [← Polynomial.Monic.nextCoeff_prod d.divisors
      (fun i => Polynomial.cyclotomic i ℤ)]
    · simpa [g] using congrArg Polynomial.nextCoeff
        (Polynomial.prod_cyclotomic_eq_X_pow_sub_one hd ℤ)
    · intro i hi
      exact Polynomial.cyclotomic.monic i ℤ
  have hinv :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hsum) n hn
  change f n = -ArithmeticFunction.moebius n
  rw [← hinv]
  simp only [g]
  rw [Finset.sum_eq_single (n, 1)]
  · simp only [Prod.fst, Prod.snd, pow_one]
    rw [show (1 : Polynomial ℤ) = Polynomial.C 1 by simp,
      Polynomial.nextCoeff_X_sub_C]
    simp
  · intro b hb hbn
    have hprod := Nat.mem_divisorsAntidiagonal.mp hb
    have hne : b.snd ≠ 1 := by
      intro hsnd
      apply hbn
      apply Prod.ext
      · simpa [hsnd] using hprod.1
      · exact hsnd
    have hsndpos : 0 < b.snd := by
      apply Nat.pos_of_ne_zero
      intro hsnd
      apply hn.ne'
      rw [← hprod.1, hsnd, mul_zero]
    have hsndtwo : 2 ≤ b.snd := (Nat.one_lt_iff_ne_zero_and_ne_one).mpr
      ⟨hsndpos.ne', hne⟩
    have hgzero :
        (Polynomial.X ^ b.snd - 1 : Polynomial ℤ).nextCoeff = 0 := by
      change (Polynomial.X ^ b.snd - Polynomial.C 1 : Polynomial ℤ).nextCoeff = 0
      rw [Polynomial.nextCoeff_of_natDegree_pos (by
        rw [Polynomial.natDegree_X_pow_sub_C]
        exact hsndpos), Polynomial.natDegree_X_pow_sub_C]
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg (by omega)]
      rw [Polynomial.coeff_C, if_neg (by omega)]
      simp
    simp [hgzero]
  · simp [Nat.mem_divisorsAntidiagonal, hn.ne']

/-- The sum of the primitive complex `n`th roots of unity is the Möbius
function.  This is the Ramanujan-sum identity at frequency one. -/
theorem sum_primitiveRoots_eq_moebius {n : ℕ} (hn : 0 < n) :
    ∑ z ∈ primitiveRoots n ℂ, z = (ArithmeticFunction.moebius n : ℂ) := by
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hprod := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ
  have hnext :
      (Polynomial.cyclotomic n ℂ).nextCoeff =
        -∑ z ∈ primitiveRoots n ℂ, z := by
    rw [hprod]
    exact Polynomial.prod_X_sub_C_nextCoeff (fun z : ℂ => z)
  have hmap :
      (Polynomial.cyclotomic n ℂ).nextCoeff =
        ((Polynomial.cyclotomic n ℤ).nextCoeff : ℂ) := by
    rw [← Polynomial.map_cyclotomic_int n ℂ,
      Polynomial.nextCoeff_map Int.cast_injective]
    rfl
  rw [hmap, cyclotomic_nextCoeff_eq_neg_moebius] at hnext
  exact neg_injective (by simpa using hnext.symm)

/-- Squared distance from a complex root of unity to `2`. -/
noncomputable def cyclotomicRootWeight (z : ℂ) : ℝ :=
  Complex.normSq (2 - z)

theorem cyclotomicRootWeight_eq {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : z ∈ primitiveRoots n ℂ) :
    cyclotomicRootWeight z = 5 - 4 * z.re := by
  have hprimitive : IsPrimitiveRoot z n :=
    (mem_primitiveRoots hn).mp hz
  have hnorm : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hprimitive.norm'_eq_one hn.ne']
    norm_num
  rw [cyclotomicRootWeight, Complex.normSq_sub, hnorm]
  norm_num [Complex.mul_re]
  ring

theorem cyclotomicRootWeight_bounds {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : z ∈ primitiveRoots n ℂ) :
    1 ≤ cyclotomicRootWeight z ∧ cyclotomicRootWeight z ≤ 9 := by
  have hprimitive : IsPrimitiveRoot z n :=
    (mem_primitiveRoots hn).mp hz
  have hre : |z.re| ≤ 1 := by
    simpa [hprimitive.norm'_eq_one hn.ne'] using Complex.abs_re_le_norm z
  rw [cyclotomicRootWeight_eq hn hz]
  constructor <;> linarith [le_abs_self z.re, neg_le_of_abs_le hre, le_of_abs_le hre]

/-- The total squared distance of the primitive roots from `2` is governed
by the first Ramanujan sum. -/
theorem sum_cyclotomicRootWeight {n : ℕ} (hn : 0 < n) :
    ∑ z ∈ primitiveRoots n ℂ, cyclotomicRootWeight z =
      5 * (Nat.totient n : ℝ) - 4 * (ArithmeticFunction.moebius n : ℝ) := by
  rw [Finset.sum_congr rfl (fun z hz => cyclotomicRootWeight_eq hn hz),
    Finset.sum_sub_distrib, Finset.sum_const, Complex.card_primitiveRoots,
    nsmul_eq_mul]
  have hsum := congrArg Complex.re (sum_primitiveRoots_eq_moebius hn)
  have hsumre : ∑ z ∈ primitiveRoots n ℂ, z.re =
      (ArithmeticFunction.moebius n : ℝ) := by
    simpa only [Complex.re_sum, Complex.intCast_re] using hsum
  rw [← Finset.mul_sum, hsumre]
  ring

/-- Primitive roots whose squared distance from `2` is at least two. -/
noncomputable def largePrimitiveRoots (n : ℕ) : Finset ℂ :=
  (primitiveRoots n ℂ).filter (fun z => 2 ≤ cyclotomicRootWeight z)

/-- At least one quarter of the primitive roots have squared distance at
least two, once the totient is at least four. -/
theorem totient_le_four_mul_card_largePrimitiveRoots {n : ℕ} (hn : 0 < n)
    (hφ : 4 ≤ Nat.totient n) :
    Nat.totient n ≤ 4 * (largePrimitiveRoots n).card := by
  classical
  let s := primitiveRoots n ℂ
  let P : ℂ → Prop := fun z => 2 ≤ cyclotomicRootWeight z
  let t := s.filter P
  let u := s.filter fun z => ¬P z
  have ht : t = largePrimitiveRoots n := rfl
  have hsplit :
      (∑ z ∈ t, cyclotomicRootWeight z) +
          ∑ z ∈ u, cyclotomicRootWeight z =
        ∑ z ∈ s, cyclotomicRootWeight z := by
    change (∑ z ∈ s.filter P, cyclotomicRootWeight z) +
        ∑ z ∈ s.filter (fun z => ¬P z), cyclotomicRootWeight z =
      ∑ z ∈ s, cyclotomicRootWeight z
    exact Finset.sum_filter_add_sum_filter_not (f := cyclotomicRootWeight) s P
  have htupper : (∑ z ∈ t, cyclotomicRootWeight z) ≤ 9 * t.card := by
    calc
      _ ≤ ∑ _z ∈ t, (9 : ℝ) := by
        apply Finset.sum_le_sum
        intro z hz
        exact (cyclotomicRootWeight_bounds hn (Finset.filter_subset P s hz)).2
      _ = 9 * t.card := by simp [mul_comm]
  have huupper : (∑ z ∈ u, cyclotomicRootWeight z) ≤ 2 * u.card := by
    calc
      _ ≤ ∑ _z ∈ u, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro z hz
        have hz' := (Finset.mem_filter.mp hz).2
        exact le_of_not_ge hz'
      _ = 2 * u.card := by simp [mul_comm]
  have hcard : t.card + u.card = Nat.totient n := by
    simpa [s, t, u, Complex.card_primitiveRoots] using
      (Finset.card_filter_add_card_filter_not (s := s) P)
  have hsumupper :
      (∑ z ∈ s, cyclotomicRootWeight z) ≤
        2 * (Nat.totient n : ℝ) + 7 * (t.card : ℝ) := by
    rw [← hsplit]
    have hcard' : (t.card : ℝ) + u.card = Nat.totient n := by exact_mod_cast hcard
    nlinarith
  have hmu : (ArithmeticFunction.moebius n : ℝ) ≤ 1 := by
    exact_mod_cast (le_trans (le_abs_self (ArithmeticFunction.moebius n))
      ArithmeticFunction.abs_moebius_le_one)
  have hsumlower :
      5 * (Nat.totient n : ℝ) - 4 ≤
        ∑ z ∈ s, cyclotomicRootWeight z := by
    have hlower : 5 * (Nat.totient n : ℝ) - 4 ≤
        5 * (Nat.totient n : ℝ) -
          4 * (ArithmeticFunction.moebius n : ℝ) := by
      linarith
    simpa [s, sum_cyclotomicRootWeight hn] using hlower
  have hφ' : (4 : ℝ) ≤ Nat.totient n := by exact_mod_cast hφ
  rw [ht] at hsumupper
  have hreal : (Nat.totient n : ℝ) ≤
      4 * ((largePrimitiveRoots n).card : ℝ) := by
    nlinarith
  exact_mod_cast hreal

/-- Product formula for the squared distances of primitive roots. -/
theorem prod_cyclotomicRootWeight {n : ℕ} (hn : 0 < n) :
    ∏ z ∈ primitiveRoots n ℂ, cyclotomicRootWeight z =
      (cyclotomicValue n : ℝ) ^ 2 := by
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hprod := congrArg (Polynomial.eval (2 : ℂ))
    (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hprod
  have hnorm := congrArg Complex.normSq hprod
  rw [map_prod] at hnorm
  change Complex.normSq ((Polynomial.cyclotomic n ℂ).eval 2) =
    ∏ z ∈ primitiveRoots n ℂ, cyclotomicRootWeight z at hnorm
  have hcast :
      (Polynomial.cyclotomic n ℂ).eval 2 =
        (((Polynomial.cyclotomic n ℤ).eval 2 : ℤ) : ℂ) := by
    rw [← Polynomial.map_cyclotomic_int n ℂ, Polynomial.eval_map]
    simp
  rw [hcast, Complex.normSq_intCast] at hnorm
  have hpos : 0 ≤ (Polynomial.cyclotomic n ℤ).eval 2 :=
    (Polynomial.cyclotomic_pos' n (by norm_num : (1 : ℤ) < 2)).le
  rw [← hnorm]
  simp [cyclotomicValue, pow_two, Int.natAbs_of_nonneg hpos]

/-- A quantitative lower bound for `Φₙ(2)`: its square is at least a
power of two whose exponent is one quarter of `φ(n)`. -/
theorem pow_card_largePrimitiveRoots_le_cyclotomicValue_sq {n : ℕ}
    (hn : 0 < n) :
    (2 : ℝ) ^ (largePrimitiveRoots n).card ≤ (cyclotomicValue n : ℝ) ^ 2 := by
  classical
  let s := primitiveRoots n ℂ
  let t := largePrimitiveRoots n
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hlarge : (2 : ℝ) ^ t.card ≤ ∏ z ∈ t, cyclotomicRootWeight z := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro _z _hz
      norm_num
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  have hrest :
      (∏ z ∈ t, cyclotomicRootWeight z) ≤
        ∏ z ∈ s, cyclotomicRootWeight z := by
    apply Finset.prod_le_prod_of_subset_of_one_le hts
    · intro z hzt
      exact le_trans zero_le_one
        (cyclotomicRootWeight_bounds hn (hts hzt)).1
    · intro z hzs _hzt
      exact (cyclotomicRootWeight_bounds hn hzs).1
  exact hlarge.trans (hrest.trans_eq (by
    simpa [s] using prod_cyclotomicRootWeight hn))

/-- Logarithmic form of the cyclotomic lower bound. -/
theorem cyclotomicValue_log_lower {n : ℕ} (hn : 0 < n)
    (hφ : 4 ≤ Nat.totient n) :
    (Nat.totient n : ℝ) * Real.log 2 / 8 ≤
      Real.log (cyclotomicValue n : ℝ) := by
  have hpow := pow_card_largePrimitiveRoots_le_cyclotomicValue_sq hn
  have hpowpos : 0 < (2 : ℝ) ^ (largePrimitiveRoots n).card := by positivity
  have hlog := Real.log_le_log hpowpos hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hcard := totient_le_four_mul_card_largePrimitiveRoots hn hφ
  have hcard' : (Nat.totient n : ℝ) ≤ 4 * ((largePrimitiveRoots n).card : ℝ) := by
    exact_mod_cast hcard
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hcard' hlogtwo.le
  norm_num at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 4)
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).2
  nlinarith

/-- For every fixed linear threshold `C`, a uniform Yamada-type
Fermat-quotient estimate forces the greatest prime factor eventually above
`C n`.  This is the complete cyclotomic contradiction argument. -/
theorem eventually_mul_lt_greatestPrimeFactor_of_fermat_quotient_bound
    (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ p : ℕ, p.Prime →
      (padicValNat p (mersenne (p - 1)) : ℝ) * Real.log (p : ℝ) ≤
        K * ((p : ℝ) / Real.log (p : ℝ) + Real.log (p : ℝ)))
    (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * n < greatestPrimeFactor (mersenne n) := by
  let B : ℝ := ((C + 1 : ℕ) : ℝ) * K * (2 * (C : ℝ))
  have hupper := fixedC_cyclotomic_upper_normalized_tendsto C K
  have hupperBound : ∀ᶠ n : ℕ in atTop,
      (((C + 1 : ℕ) : ℝ) *
        (K * (Real.sqrt (n : ℝ) / Real.log 3 +
            (2 * (C : ℝ) * (n : ℝ)) / Real.log (n : ℝ) +
            2 * Real.log (n : ℝ)) + Real.log (n : ℝ))) *
          Real.log (n : ℝ) / (n : ℝ) < B + 1 := by
    exact hupper.eventually (Iio_mem_nhds (by simp [B]))
  have hlowerBound : ∀ᶠ n : ℕ in atTop, B + 1 ≤
      ((Nat.totient n : ℝ) * Real.log 2 / 8) *
        Real.log (n : ℝ) / (n : ℝ) :=
    cyclotomic_lower_normalized_tendsto_atTop.eventually_ge_atTop (B + 1)
  filter_upwards [hupperBound, hlowerBound,
    eventually_gt_atTop (max 9 C)] with n hupperN hlowerN hnlarge
  have hn9 : 9 < n := lt_of_le_of_lt (le_max_left 9 C) hnlarge
  have hCn : C ≤ n := (le_max_right 9 C).trans hnlarge.le
  have hn : 1 < n := by omega
  by_contra hnot
  have hP : greatestPrimeFactor (mersenne n) ≤ C * n := Nat.le_of_not_gt hnot
  have hlower := cyclotomicValue_log_lower (lt_trans zero_lt_one hn)
    (four_le_totient_of_nine_lt hn9)
  have hupper := cyclotomicValue_log_upper_of_fermat_quotient_bound
    hn hCn hP hK hF
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    (Real.log_pos (by exact_mod_cast hn)).le
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hscale : 0 ≤ Real.log (n : ℝ) / (n : ℝ) := div_nonneg hlogn hnR
  have hlowScaled := mul_le_mul_of_nonneg_right hlower hscale
  have huppScaled := mul_le_mul_of_nonneg_right hupper hscale
  have hLU :
      ((Nat.totient n : ℝ) * Real.log 2 / 8) *
          Real.log (n : ℝ) / (n : ℝ) ≤
        (((C + 1 : ℕ) : ℝ) *
          (K * (Real.sqrt (n : ℝ) / Real.log 3 +
              (2 * (C : ℝ) * (n : ℝ)) / Real.log (n : ℝ) +
              2 * Real.log (n : ℝ)) + Real.log (n : ℝ))) *
            Real.log (n : ℝ) / (n : ℝ) := by
    calc
      _ = ((Nat.totient n : ℝ) * Real.log 2 / 8) *
          (Real.log (n : ℝ) / (n : ℝ)) := by ring
      _ ≤ Real.log (cyclotomicValue n : ℝ) *
          (Real.log (n : ℝ) / (n : ℝ)) := hlowScaled
      _ ≤ (((C + 1 : ℕ) : ℝ) *
          (K * (Real.sqrt (n : ℝ) / Real.log 3 +
              (2 * (C : ℝ) * (n : ℝ)) / Real.log (n : ℝ) +
              2 * Real.log (n : ℝ)) + Real.log (n : ℝ))) *
          (Real.log (n : ℝ) / (n : ℝ)) := huppScaled
      _ = _ := by ring
  exact (not_lt_of_ge hLU) (hupperN.trans_le hlowerN)

/-- The literal assertion asked in Erdős Problem 977. -/
def Erdos977Statement : Prop :=
  Tendsto
    (fun n : ℕ => (greatestPrimeFactor (mersenne n) : ℝ) / (n : ℝ))
    atTop atTop

/-- The exact statement of Problem 977 follows from the uniform
Fermat-quotient estimate. -/
theorem erdos_977_of_fermat_quotient_bound
    (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ p : ℕ, p.Prime →
      (padicValNat p (mersenne (p - 1)) : ℝ) * Real.log (p : ℝ) ≤
        K * ((p : ℝ) / Real.log (p : ℝ) + Real.log (p : ℝ))) :
    Erdos977Statement := by
  rw [Erdos977Statement]
  refine tendsto_atTop.mpr fun A => ?_
  obtain ⟨C : ℕ, hAC⟩ := exists_nat_ge A
  filter_upwards
    [eventually_mul_lt_greatestPrimeFactor_of_fermat_quotient_bound K hK hF C,
      eventually_gt_atTop (0 : ℕ)] with n hCn hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hCnR : (C : ℝ) * (n : ℝ) < greatestPrimeFactor (mersenne n) := by
    exact_mod_cast hCn
  have hratio : (C : ℝ) <
      (greatestPrimeFactor (mersenne n) : ℝ) / (n : ℝ) :=
    (lt_div_iff₀ hnR).2 hCnR
  exact hAC.trans hratio.le

/-! ### The interpolation-determinant input

The remaining arithmetic estimate is proved by an integral interpolation
determinant.  The next two lemmas are the archimedean and divisibility sides
of the basic determinant comparison.  They are stated separately because the
matrix used below undergoes several integral row and column operations. -/

/-- Leibniz's formula over an arbitrary finite index type. -/
theorem int_natAbs_det_le_of_entries_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ℕ}
    {A : Matrix ι ι ℤ} (hA : ∀ i j, (A i j).natAbs ≤ B) :
    A.det.natAbs ≤ (Fintype.card ι).factorial * B ^ Fintype.card ι := by
  rw [Matrix.det_apply']
  calc
    (∑ σ : Equiv.Perm ι,
        (↑↑σ.sign : ℤ) * ∏ i, A (σ i) i).natAbs
        ≤ ∑ σ : Equiv.Perm ι,
            ((↑↑σ.sign : ℤ) * ∏ i, A (σ i) i).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, B ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro σ _
      rw [Int.natAbs_mul]
      have hprod : (∏ i, A (σ i) i).natAbs ≤ B ^ Fintype.card ι := by
        change Int.natAbsHom (∏ i, A (σ i) i) ≤ B ^ Fintype.card ι
        rw [map_prod]
        simpa [Finset.prod_const] using
          (Finset.prod_le_prod' (s := Finset.univ) fun i _ => hA (σ i) i)
      simpa using hprod
    _ = (Fintype.card ι).factorial * B ^ Fintype.card ι := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        nsmul_eq_mul, Nat.cast_id]

/-- Leibniz's formula bounds the absolute value of an integral `N × N`
determinant by `N! B^N` when every entry has absolute value at most `B`. -/
theorem int_natAbs_det_le_of_entries {N B : ℕ}
    {A : Matrix (Fin N) (Fin N) ℤ}
    (hA : ∀ i j, (A i j).natAbs ≤ B) :
    A.det.natAbs ≤ N.factorial * B ^ N := by
  rw [Matrix.det_apply']
  calc
    (∑ σ : Equiv.Perm (Fin N),
        (↑↑σ.sign : ℤ) * ∏ i, A (σ i) i).natAbs
        ≤ ∑ σ : Equiv.Perm (Fin N),
            ((↑↑σ.sign : ℤ) * ∏ i, A (σ i) i).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin N), B ^ N := by
      apply Finset.sum_le_sum
      intro σ _
      rw [Int.natAbs_mul]
      have hprod : (∏ i, A (σ i) i).natAbs ≤ B ^ N := by
        change Int.natAbsHom (∏ i, A (σ i) i) ≤ B ^ N
        rw [map_prod]
        simpa [Finset.prod_const, Fintype.card_fin] using
          (Finset.prod_le_prod' (s := Finset.univ) fun i _ => hA (σ i) i)
      simpa using hprod
    _ = N.factorial * B ^ N := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

/-- If a nonzero integer is divisible by `p^e`, its ordinary absolute value
is at least `p^e`.  This is the lower half of every interpolation-determinant
comparison used below. -/
theorem nat_pow_le_natAbs_of_int_pow_dvd {p e : ℕ} {z : ℤ}
    (hz : z ≠ 0) (hd : (p ^ e : ℤ) ∣ z) : p ^ e ≤ z.natAbs := by
  exact_mod_cast Int.natAbs_le_of_dvd_ne_zero hd hz

/-! ### Mahler coefficients for the interpolation determinant -/

variable {R : Type*} [CommRing R]

/-- Forward difference by one as an `R`-linear endomorphism. -/
def forwardDiffLinear : Module.End R (ℕ → R) where
  toFun := fwdDiff 1
  map_add' f g := by
    ext x
    simp only [Pi.add_apply, fwdDiff]
    ring
  map_smul' r f := by
    ext x
    simp [fwdDiff, mul_sub]

@[simp]
theorem forwardDiffLinear_apply (f : ℕ → R) (x : ℕ) :
    forwardDiffLinear f x = f (x + 1) - f x := rfl

theorem forwardDiffLinear_pow_apply (f : ℕ → R) (n x : ℕ) :
    (forwardDiffLinear ^ n) f x = (fwdDiff 1)^[n] f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
      simp only [forwardDiffLinear_apply, fwdDiff]
      rw [ih, ih]

/-- The difference operator obtained after factoring `v ^ x` out of the
forward difference of `P x * v ^ x`. -/
def twistedDiffLinear (v : R) : Module.End R (ℕ → R) :=
  (v - 1) • 1 + v • forwardDiffLinear

@[simp]
theorem twistedDiffLinear_apply (v : R) (P : ℕ → R) (x : ℕ) :
    twistedDiffLinear v P x = (v - 1) * P x + v * (P (x + 1) - P x) := by
  simp [twistedDiffLinear, forwardDiffLinear, fwdDiff]

theorem fwdDiff_mul_pow (v : R) (P : ℕ → R) (x : ℕ) :
    fwdDiff 1 (fun y => P y * v ^ y) x = twistedDiffLinear v P x * v ^ x := by
  simp only [fwdDiff, twistedDiffLinear_apply]
  rw [pow_succ']
  ring

theorem fwdDiff_iter_mul_pow (v : R) (P : ℕ → R) (n x : ℕ) :
    (fwdDiff 1)^[n] (fun y => P y * v ^ y) x =
      (twistedDiffLinear v ^ n) P x * v ^ x := by
  induction n generalizing P x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [show (fwdDiff 1)^[n] (fun y => P y * v ^ y) =
          fun y => (twistedDiffLinear v ^ n) P y * v ^ y from
        funext fun y => ih P y]
      rw [fwdDiff_mul_pow, pow_succ', Module.End.mul_apply]

theorem commute_forwardDiffLinear_smul_one (a : R) :
    Commute (a • (1 : Module.End R (ℕ → R))) forwardDiffLinear := by
  rw [commute_iff_eq]
  ext f x
  simp [forwardDiffLinear, fwdDiff, mul_sub]

theorem twistedDiffLinear_pow (v : R) (n : ℕ) :
    twistedDiffLinear v ^ n =
      ∑ j ∈ range (n + 1),
        (((v - 1) • (1 : Module.End R (ℕ → R))) ^ j *
          ((v • forwardDiffLinear) ^ (n - j))) *
            (n.choose j : Module.End R (ℕ → R)) := by
  let A : Module.End R (ℕ → R) := (v - 1) • 1
  let B : Module.End R (ℕ → R) := v • forwardDiffLinear
  have hAB : Commute A B := by
    rw [commute_iff_eq]
    ext P x
    simp [A, B, forwardDiffLinear, fwdDiff, mul_sub]
    ring
  simpa [twistedDiffLinear, A, B] using hAB.add_pow n

theorem smul_one_pow_apply (a : R) (f : ℕ → R) (n x : ℕ) :
    ((a • (1 : Module.End R (ℕ → R))) ^ n) f x = a ^ n * f x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      change a * (((a • (1 : Module.End R (ℕ → R))) ^ n) f x) = _
      rw [ih]
      rw [pow_succ']
      ring

theorem smul_forwardDiffLinear_pow_apply (a : R) (f : ℕ → R) (n x : ℕ) :
    ((a • forwardDiffLinear) ^ n) f x =
      a ^ n * (fwdDiff 1)^[n] f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      change a * ((((a • forwardDiffLinear) ^ n) f (x + 1)) -
        (((a • forwardDiffLinear) ^ n) f x)) = _
      rw [ih, ih, Function.iterate_succ_apply']
      simp only [fwdDiff]
      rw [pow_succ']
      ring

@[simp]
theorem natCast_end_apply (n : ℕ) (f : ℕ → R) (x : ℕ) :
    ((n : Module.End R (ℕ → R)) f) x = n • f x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      change ((n : Module.End R (ℕ → R)) f) x + f x = (n + 1) • f x
      rw [ih, add_nsmul, one_nsmul]

theorem fwdDiff_iter_mul_pow_eq_sum (v : R) (P : ℕ → R) (n x : ℕ) :
    (fwdDiff 1)^[n] (fun y => P y * v ^ y) x =
      (∑ j ∈ range (n + 1),
          (n.choose j : R) * (v - 1) ^ j * v ^ (n - j) *
            (fwdDiff 1)^[n - j] P x) * v ^ x := by
  rw [fwdDiff_iter_mul_pow, twistedDiffLinear_pow]
  simp only [LinearMap.coe_sum, Finset.sum_apply, Module.End.mul_apply,
    smul_forwardDiffLinear_pow_apply, smul_one_pow_apply]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hcastfun :
      ((n.choose j : Module.End R (ℕ → R)) P) =
        (n.choose j : R) • P := by
    ext y
    simp [nsmul_eq_mul]
  rw [hcastfun, fwdDiff_iter_const_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

section MahlerNorm

variable {S : Type*} [NormedField S]

/-- The degree-`k` polynomial whose value at `x` is `choose (b*x) k`. -/
noncomputable def chooseMulPoly [CharZero S] (b k : ℕ) : S[X] :=
  (k.factorial : S)⁻¹ •
    ((descPochhammer ℤ k).map (Int.castRingHom S)).comp
      (Polynomial.C (b : S) * Polynomial.X)

theorem chooseMulPoly_eval [CharZero S] (b k : ℕ) (x : S) :
    (chooseMulPoly (S := S) b k).eval x = Ring.choose ((b : S) * x) k := by
  rw [chooseMulPoly, Polynomial.eval_smul, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  congr 1
  rw [Polynomial.eval_map]
  have hhom : Int.castRingHom S = (RingHom.smulOneHom : ℤ →+* S) := by
    ext z
    simp
  rw [hhom, Polynomial.eval₂_smulOneHom_eq_smeval]

theorem chooseMulPoly_natDegree_le [CharZero S] (b k : ℕ) :
    (chooseMulPoly (S := S) b k).natDegree ≤ k := by
  calc
    (chooseMulPoly (S := S) b k).natDegree ≤
        (((descPochhammer ℤ k).map (Int.castRingHom S)).comp
          (Polynomial.C (b : S) * Polynomial.X)).natDegree :=
      Polynomial.natDegree_smul_le _ _
    _ ≤ ((descPochhammer ℤ k).map (Int.castRingHom S)).natDegree *
        (Polynomial.C (b : S) * Polynomial.X).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ k * 1 := by
      gcongr
      · exact Polynomial.natDegree_map_le.trans_eq
          (descPochhammer_natDegree ℤ k)
      · exact Polynomial.natDegree_mul_le.trans (by simp)
    _ = k := Nat.mul_one k

theorem fwdDiff_iter_choose_mul_eq_zero [CharZero S]
    (b k m : ℕ) (hkm : k < m) :
    (fwdDiff 1)^[m] (fun x : ℕ => (Nat.choose (b * x) k : S)) = 0 := by
  let Q : S[X] := chooseMulPoly (S := S) b k
  have hdeg : Q.natDegree < m :=
    (chooseMulPoly_natDegree_le (S := S) b k).trans_lt hkm
  have hpoly : (fwdDiff 1)^[m] Q.eval = 0 :=
    Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg
  funext x
  change (fwdDiff 1)^[m] (fun y : ℕ => (Nat.choose (b * y) k : S)) x = 0
  rw [fwdDiff_iter_eq_sum_shift]
  have hpolyx := congrFun hpoly (x : S)
  rw [Pi.zero_apply, fwdDiff_iter_eq_sum_shift] at hpolyx
  simp only [Q, chooseMulPoly_eval, nsmul_one] at hpolyx ⊢
  convert hpolyx using 1
  apply sum_congr rfl
  intro j hj
  congr 1
  rw [← Nat.cast_add, ← Nat.cast_mul, Ring.choose_natCast]
  simp

variable [IsUltrametricDist S]

theorem norm_fwdDiff_iter_natCast_le_one (f : ℕ → ℕ) (m x : ℕ) :
    ‖(fwdDiff 1)^[m] (fun y => (f y : S)) x‖ ≤ 1 := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty
    nonempty_range_add_one ?_
  intro j hj
  rw [← Int.cast_smul_eq_zsmul S, smul_eq_mul, norm_mul]
  calc
    ‖(((-1 : ℤ) ^ (m - j) * m.choose j : ℤ) : S)‖ *
        ‖(f (x + j • 1) : S)‖ ≤ 1 * 1 := by
      gcongr
      · exact IsUltrametricDist.norm_intCast_le_one S _
      · exact IsUltrametricDist.norm_natCast_le_one S _
    _ = 1 := one_mul 1

/-- If `P` has forward-difference degree at most `k`, multiplying it by
`v ^ x` forces the `n`-th Mahler coefficient to contain at least
`n - k` powers of `v - 1`. -/
theorem norm_fwdDiff_iter_mul_pow_le {v : S} {P : ℕ → S} {k n : ℕ}
    {q : ℝ} (hkn : k ≤ n) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hv : ‖v‖ ≤ 1) (hu : ‖v - 1‖ ≤ q)
    (hPnorm : ∀ m x, ‖(fwdDiff 1)^[m] P x‖ ≤ 1)
    (hPzero : ∀ m, k < m → (fwdDiff 1)^[m] P = 0) :
    ‖(fwdDiff 1)^[n] (fun x => P x * v ^ x) 0‖ ≤ q ^ (n - k) := by
  rw [fwdDiff_iter_mul_pow_eq_sum]
  simp only [pow_zero, mul_one]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty nonempty_range_add_one ?_
  intro j hj
  by_cases hsmall : j < n - k
  · have hdeg : k < n - j := by omega
    rw [hPzero (n - j) hdeg, Pi.zero_apply, mul_zero, norm_zero]
    positivity
  · have hjge : n - k ≤ j := Nat.le_of_not_gt hsmall
    have hchoose : ‖(n.choose j : S)‖ ≤ 1 :=
      IsUltrametricDist.norm_natCast_le_one S (n.choose j)
    have huvpow : ‖v - 1‖ ^ j ≤ q ^ j :=
      pow_le_pow_left₀ (norm_nonneg (v - 1)) hu j
    have hqpow : q ^ j ≤ q ^ (n - k) :=
      pow_le_pow_of_le_one hq0 hq1 hjge
    have hvpow : ‖v‖ ^ (n - j) ≤ 1 := pow_le_one₀ (norm_nonneg v) hv
    calc
      ‖(n.choose j : S) * (v - 1) ^ j * v ^ (n - j) *
          (fwdDiff 1)^[n - j] P 0‖ =
          ‖(n.choose j : S)‖ * ‖v - 1‖ ^ j * ‖v‖ ^ (n - j) *
            ‖(fwdDiff 1)^[n - j] P 0‖ := by simp only [norm_mul, norm_pow]
      _ ≤ 1 * q ^ j * 1 * 1 := by
        gcongr
        exact hPnorm (n - j) 0
      _ = q ^ j := by ring
      _ ≤ q ^ (n - k) := hqpow

/-- Specialized Mahler coefficient estimate for the interpolation functions
`x ↦ choose (b*x) k * v^x`. -/
theorem norm_fwdDiff_iter_choose_mul_pow_le [CharZero S]
    {v : S} {b k n : ℕ} {q : ℝ}
    (hkn : k ≤ n) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hv : ‖v‖ ≤ 1) (hu : ‖v - 1‖ ≤ q) :
    ‖(fwdDiff 1)^[n]
      (fun x : ℕ => (Nat.choose (b * x) k : S) * v ^ x) 0‖ ≤
        q ^ (n - k) := by
  apply norm_fwdDiff_iter_mul_pow_le hkn hq0 hq1 hv hu
  · exact norm_fwdDiff_iter_natCast_le_one (S := S)
      (fun x => Nat.choose (b * x) k)
  · intro m hkm
    exact fwdDiff_iter_choose_mul_eq_zero (S := S) b k m hkm

end MahlerNorm

/-! ### Rectangular Newton factorization and determinant bounds -/

theorem det_mul_rectangular_aux {n q : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n q R} {V : Matrix q n R} {p : n → q} (hp : ¬Injective p) :
    (∑ σ : Equiv.Perm n,
      Equiv.Perm.sign σ * ∏ x, C (σ x) (p x) * V (p x) x) = 0 := by
  obtain ⟨i, j, hpij, hij⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
    rw [Injective] at hp
    push Not at hp
    exact hp
  exact
    sum_involution (fun σ _ => σ * Equiv.swap i j)
      (fun σ _ => by
        have hprod : (∏ x, C (σ x) (p x)) =
            ∏ x, C ((σ * Equiv.swap i j) x) (p x) :=
          Fintype.prod_equiv (Equiv.swap i j) _ _
            (by simp [Equiv.apply_swap_eq_self hpij])
        simp [hprod, Equiv.Perm.sign_swap hij, -Equiv.Perm.sign_swap',
          prod_mul_distrib])
      (fun σ _ _ => (not_congr Equiv.mul_swap_eq_iff).mpr hij)
      (fun _ _ => mem_univ _) fun σ _ => Equiv.mul_swap_involutive i j σ

theorem det_mul_rectangular {n q : Type*} [Fintype n] [DecidableEq n]
    [Fintype q] [DecidableEq q] (C : Matrix n q R) (V : Matrix q n R) :
    Matrix.det (C * V) =
      ∑ p : n → q with Injective p,
        ∑ σ : Equiv.Perm n,
          Equiv.Perm.sign σ * ∏ i, C (σ i) (p i) * V (p i) i := by
  calc
    Matrix.det (C * V) =
        ∑ p : n → q, ∑ σ : Equiv.Perm n,
          Equiv.Perm.sign σ * ∏ i, C (σ i) (p i) * V (p i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum,
        Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = ∑ p : n → q with Injective p,
        ∑ σ : Equiv.Perm n,
          Equiv.Perm.sign σ * ∏ i, C (σ i) (p i) * V (p i) i := by
      refine (sum_subset (filter_subset _ _) fun p _ hp =>
        det_mul_rectangular_aux ?_).symm
      simpa only [mem_filter_univ] using hp

theorem sum_range_card_le_sum (s : Finset ℕ) :
    ∑ i ∈ range s.card, i ≤ ∑ i ∈ s, i := by
  classical
  induction hs : s.card using Nat.strong_induction_on generalizing s with
  | h c ih =>
      subst c
      by_cases hsempty : s = ∅
      · simp [hsempty]
      · have hsne : s.Nonempty := nonempty_iff_ne_empty.mpr hsempty
        let a : ℕ := s.max' hsne
        let t : Finset ℕ := s.erase a
        have ha : a ∈ s := by simpa [a] using Finset.max'_mem s hsne
        have hcardt : t.card < s.card := by
          change (s.erase a).card < s.card
          rw [Finset.card_erase_of_mem ha]
          exact Nat.sub_one_lt (Finset.card_pos.mpr hsne).ne'
        have hiht : ∑ i ∈ range t.card, i ≤ ∑ i ∈ t, i :=
          ih t.card hcardt t rfl
        have ht_sub : t ⊆ range a := by
          intro x hxt
          have hxs : x ∈ s := Finset.mem_of_mem_erase hxt
          have hxa : x ≠ a := (Finset.mem_erase.mp hxt).1
          exact Finset.mem_range.mpr (lt_of_le_of_ne (Finset.le_max' s x hxs) hxa)
        have hcard_le : t.card ≤ a := by
          simpa using Finset.card_le_card ht_sub
        have hcards : s.card = t.card + 1 := by
          rw [show t.card = s.card - 1 by simp [t, ha]]
          omega
        calc
          ∑ i ∈ range s.card, i = ∑ i ∈ range (t.card + 1), i := by rw [hcards]
          _ = (∑ i ∈ range t.card, i) + t.card := by rw [sum_range_succ]
          _ ≤ (∑ i ∈ t, i) + a := Nat.add_le_add hiht hcard_le
          _ = ∑ i ∈ s, i := by
            simpa [t] using Finset.sum_erase_add s (fun x => x) ha

theorem sum_fin_val_le_sum_injective {N M : ℕ} (p : Fin N → Fin M)
    (hp : Injective p) :
    ∑ i ∈ range N, i ≤ ∑ i, (p i).val := by
  classical
  let s : Finset ℕ := Finset.univ.image (fun i : Fin N => (p i).val)
  have hval : Injective (fun i : Fin N => (p i).val) :=
    Fin.val_injective.comp hp
  have hcard : s.card = N := by
    simp [s, Finset.card_image_of_injective _ hval]
  have hsum : ∑ x ∈ s, x = ∑ i : Fin N, (p i).val := by
    dsimp [s]
    rw [Finset.sum_image]
    exact hval.injOn
  have hbase := sum_range_card_le_sum s
  rw [hcard, hsum] at hbase
  exact hbase

def newtonCoeffMatrix {N M : ℕ} (f : Fin N → ℕ → R) :
    Matrix (Fin N) (Fin M) R :=
  fun i a => (fwdDiff 1)^[(a : ℕ)] (f i) 0

def newtonChooseMatrix {N M : ℕ} (x : Fin N → ℕ) :
    Matrix (Fin M) (Fin N) R :=
  fun a j => (Nat.choose (x j) (a : ℕ) : R)

theorem newtonCoeffMatrix_mul_chooseMatrix {N M : ℕ}
    (f : Fin N → ℕ → R) (x : Fin N → ℕ)
    (hx : ∀ j, x j < M) :
    (newtonCoeffMatrix (R := R) f : Matrix (Fin N) (Fin M) R) *
      (newtonChooseMatrix (R := R) x : Matrix (Fin M) (Fin N) R) =
      fun i j => f i (x j) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [newtonCoeffMatrix, newtonChooseMatrix]
  change (∑ a : Fin M,
    (fwdDiff 1)^[(a.val)] (f i) 0 * (Nat.choose (x j) a.val : R)) = f i (x j)
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ =>
    (fwdDiff 1)^[a] (f i) 0 * (Nat.choose (x j) a : R))]
  have hsub : range (x j + 1) ⊆ range M :=
    range_mono (Nat.succ_le_iff.mpr (hx j))
  have hsum :
      (∑ a ∈ range M,
        (fwdDiff 1)^[a] (f i) 0 * (Nat.choose (x j) a : R)) =
      ∑ a ∈ range (x j + 1),
        (fwdDiff 1)^[a] (f i) 0 * (Nat.choose (x j) a : R) := by
    symm
    apply sum_subset hsub
    intro a haM ha
    have hxa : x j < a := by
      simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using ha
    rw [Nat.choose_eq_zero_of_lt hxa, Nat.cast_zero, mul_zero]
  rw [hsum]
  simpa [newtonCoeffMatrix, newtonChooseMatrix, nsmul_eq_mul, mul_comm] using
    (shift_eq_sum_fwdDiff_iter (1 : ℕ) (f i) (x j) 0).symm

theorem sum_tsub_le_sum_tsub {N : ℕ} (a b : Fin N → ℕ) :
    (∑ i, a i) - ∑ i, b i ≤ ∑ i, (a i - b i) := by
  classical
  induction (Finset.univ : Finset (Fin N)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [sum_insert hi]
      omega

section DeterminantNorm

variable {S : Type*} [NormedField S] [IsUltrametricDist S]

theorem norm_det_evaluation_le {N M : ℕ}
    (f : Fin N → ℕ → S) (x : Fin N → ℕ) (k : Fin N → ℕ)
    (hx : ∀ j, x j < M) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hcoeff : ∀ i (a : Fin M),
      ‖(fwdDiff 1)^[(a : ℕ)] (f i) 0‖ ≤ q ^ ((a : ℕ) - k i)) :
    ‖Matrix.det (fun i j => f i (x j))‖ ≤
      q ^ ((∑ a ∈ range N, a) - ∑ i, k i) := by
  rw [← newtonCoeffMatrix_mul_chooseMatrix (R := S) f x hx,
    det_mul_rectangular]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (pow_nonneg hq0 _) ?_
  intro p hpfilter
  have hp : Injective p := (mem_filter.mp hpfilter).2
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (pow_nonneg hq0 _) ?_
  intro σ hσ
  have hpsum : (∑ a ∈ range N, a) ≤ ∑ i, ((p i).val) :=
    sum_fin_val_le_sum_injective p hp
  have hksigma : (∑ i, k (σ i)) = ∑ i, k i := by
    simpa using Equiv.sum_comp σ k
  have hexponent :
      (∑ a ∈ range N, a) - ∑ i, k i ≤
        ∑ i, ((p i).val - k (σ i)) := by
    calc
      (∑ a ∈ range N, a) - ∑ i, k i ≤
          (∑ i, (p i).val) - ∑ i, k i :=
        Nat.sub_le_sub_right hpsum _
      _ = (∑ i, (p i).val) - ∑ i, k (σ i) := by rw [hksigma]
      _ ≤ ∑ i, ((p i).val - k (σ i)) :=
        sum_tsub_le_sum_tsub (fun i => (p i).val) (fun i => k (σ i))
  rw [norm_mul, norm_prod]
  calc
    ‖(Equiv.Perm.sign σ : S)‖ *
        ∏ i, ‖newtonCoeffMatrix f (σ i) (p i) *
          newtonChooseMatrix x (p i) i‖ ≤
        1 * ∏ i, q ^ ((p i).val - k (σ i)) := by
      gcongr with i
      · exact IsUltrametricDist.norm_intCast_le_one S _
      · rw [norm_mul]
        calc
          ‖newtonCoeffMatrix f (σ i) (p i)‖ *
              ‖newtonChooseMatrix x (p i) i‖ ≤
              q ^ ((p i).val - k (σ i)) * 1 := by
            gcongr
            · exact hcoeff (σ i) (p i)
            · exact IsUltrametricDist.norm_natCast_le_one S _
          _ = q ^ ((p i).val - k (σ i)) := mul_one _
    _ = q ^ (∑ i, ((p i).val - k (σ i))) := by
      rw [one_mul, Finset.prod_pow_eq_pow_sum]
    _ ≤ q ^ ((∑ a ∈ range N, a) - ∑ i, k i) :=
      pow_le_pow_of_le_one hq0 hq1 hexponent

/-- All forward differences of an ultrametrically bounded sequence satisfy
the same bound. -/
theorem norm_fwdDiff_iter_of_forall_norm_le
    {T : Type*} [NormedField T] [IsUltrametricDist T]
    {f : ℕ → T} {B : ℝ} (_hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B)
    (n x : ℕ) : ‖(fwdDiff 1)^[n] f x‖ ≤ B := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty
    nonempty_range_add_one ?_
  intro j hj
  rw [← Int.cast_smul_eq_zsmul T, smul_eq_mul, norm_mul]
  calc
    ‖(((-1 : ℤ) ^ (n - j) * n.choose j : ℤ) : T)‖ *
        ‖f (x + j • 1)‖ ≤ 1 * B := by
      gcongr
      exact IsUltrametricDist.norm_intCast_le_one T _
      exact hf _
    _ = B := one_mul B

/-- The Mahler estimate also covers the coefficients below the binomial
degree, where the claimed exponent is zero. -/
theorem norm_fwdDiff_iter_choose_mul_pow_le_all
    {T : Type*} [NormedField T] [IsUltrametricDist T] [CharZero T]
    {v : T} {b k n : ℕ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hv : ‖v‖ ≤ 1) (hu : ‖v - 1‖ ≤ q) :
    ‖(fwdDiff 1)^[n]
      (fun x : ℕ => (Nat.choose (b * x) k : T) * v ^ x) 0‖ ≤
        q ^ (n - k) := by
  by_cases hkn : k ≤ n
  · exact norm_fwdDiff_iter_choose_mul_pow_le hkn hq0 hq1 hv hu
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hkn), pow_zero]
    apply norm_fwdDiff_iter_of_forall_norm_le (B := 1) zero_le_one
    intro x
    rw [norm_mul, norm_pow]
    calc
      ‖(Nat.choose (b * x) k : T)‖ * ‖v‖ ^ x ≤ 1 * 1 := by
        gcongr
        · exact IsUltrametricDist.norm_natCast_le_one T _
        · exact pow_le_one₀ (norm_nonneg v) hv
      _ = 1 := mul_one 1

/-- A perturbation of every sampled value by `q^M` does not affect the
Newton-determinant exponent, because all sampled nodes lie below `M`.
This packages the high-valuation error rows in the interpolation argument. -/
theorem norm_det_perturbed_evaluation_le
    {T : Type*} [NormedField T] [IsUltrametricDist T]
    {N M : ℕ} (A : Matrix (Fin N) (Fin N) T)
    (f : Fin N → ℕ → T) (x : Fin N → ℕ) (k : Fin N → ℕ)
    (hN : 0 < N) (hxM : ∀ j, x j < M) (hxinj : Injective x)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hcoeff : ∀ i (a : Fin M),
      ‖(fwdDiff 1)^[(a : ℕ)] (f i) 0‖ ≤ q ^ ((a : ℕ) - k i))
    (herr : ∀ i j, ‖A i j - f i (x j)‖ ≤ q ^ M) :
    ‖Matrix.det A‖ ≤
      q ^ ((∑ a ∈ range N, a) - ∑ i, k i) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  let e : Fin N → ℕ → T := fun i n =>
    if h : n ∈ Set.range x then
      A i (Function.invFun x n) - f i n
    else 0
  let F : Fin N → ℕ → T := fun i n => f i n + e i n
  have heval : ∀ i j, F i (x j) = A i j := by
    intro i j
    have hrange : x j ∈ Set.range x := ⟨j, rfl⟩
    simp only [F, e, hrange, dif_pos]
    rw [Function.leftInverse_invFun hxinj j]
    ring
  have enorm : ∀ i n, ‖e i n‖ ≤ q ^ M := by
    intro i n
    by_cases hn : n ∈ Set.range x
    · obtain ⟨j, rfl⟩ := hn
      simpa [e, Function.leftInverse_invFun hxinj j] using herr i j
    · rw [show e i n = 0 by simp only [e, dif_neg hn]]
      exact (norm_zero : ‖(0 : T)‖ = 0) ▸ pow_nonneg hq0 _
  have ecoeff : ∀ i (a : Fin M),
      ‖(fwdDiff 1)^[(a : ℕ)] (e i) 0‖ ≤ q ^ ((a : ℕ) - k i) := by
    intro i a
    have he := norm_fwdDiff_iter_of_forall_norm_le
      (B := q ^ M) (pow_nonneg hq0 _) (enorm i) (a : ℕ) 0
    exact he.trans (pow_le_pow_of_le_one hq0 hq1 (by omega))
  have hAF : A = fun i j => F i (x j) := by
    ext i j
    exact (heval i j).symm
  rw [hAF]
  apply norm_det_evaluation_le F x k hxM hq0 hq1
  intro i a
  change ‖(fwdDiff 1)^[(a : ℕ)] (fun n => f i n + e i n) 0‖ ≤ _
  rw [show (fun n => f i n + e i n) = f i + e i by rfl,
    fwdDiff_iter_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hcoeff i a) (ecoeff i a))

/-- If the auxiliary columns carrying the error all have weight `E ≥ N`,
then any injective choice of `N` Newton-or-error columns has total weight at
least `0 + ⋯ + (N-1)`. -/
theorem sum_range_le_sum_sum_weight {N M E : ℕ} (hE : N ≤ E)
    (p : Fin N → Fin M ⊕ Fin N) (hp : Injective p) :
    (∑ a ∈ range N, a) ≤
      ∑ i, Sum.elim (fun a : Fin M => a.1) (fun _ : Fin N => E) (p i) := by
  classical
  let w : Fin M ⊕ Fin N → ℕ :=
    Sum.elim (fun a : Fin M => a.1) (fun _ : Fin N => E)
  let s : Finset (Fin N) := univ.filter fun i => (p i).isLeft
  have hwinj : Set.InjOn (fun i => w (p i)) s := by
    intro i hi j hj hij
    simp only [s, mem_filter, mem_univ, true_and] at hi hj
    cases hpi : p i with
    | inl ai =>
        cases hpj : p j with
        | inl aj =>
            apply hp
            rw [hpi, hpj]
            congr 1
            apply Fin.ext
            simpa [w, hpi, hpj] using hij
        | inr aj => simp [hpj] at hj
    | inr ai => simp [hpi] at hi
  let vals : Finset ℕ := s.image fun i => w (p i)
  have hcardvals : vals.card = s.card := by
    simp [vals, Finset.card_image_iff.mpr hwinj]
  have hsumvals : ∑ a ∈ vals, a = ∑ i ∈ s, w (p i) := by
    rw [show vals = s.image (fun i => w (p i)) by rfl, sum_image hwinj]
  have hleft : (∑ a ∈ range s.card, a) ≤ ∑ i ∈ s, w (p i) := by
    have h := sum_range_card_le_sum vals
    rwa [hcardvals, hsumvals] at h
  have hsle : s.card ≤ N := by simpa using s.card_le_univ
  have htail : (∑ a ∈ Finset.Ico s.card N, a) ≤ (N - s.card) * E := by
    calc
      (∑ a ∈ Finset.Ico s.card N, a) ≤ (Finset.Ico s.card N).card * E := by
        exact sum_le_card_nsmul _ _ _ fun a ha =>
          (Finset.mem_Ico.mp ha).2.le.trans hE
      _ = (N - s.card) * E := by rw [Nat.card_Ico]
  have hright : ∑ i ∈ univ.filter (fun i => ¬(p i).isLeft), w (p i) =
      (N - s.card) * E := by
    have hcard : (univ.filter (fun i => ¬(p i).isLeft)).card = N - s.card := by
      rw [show s = univ.filter (fun i => (p i).isLeft) by rfl]
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (univ : Finset (Fin N))) (fun i => (p i).isLeft)
      simp only [Finset.card_univ, Fintype.card_fin, Sum.not_isLeft] at hpart ⊢
      omega
    calc
      ∑ i ∈ univ.filter (fun i => ¬(p i).isLeft), w (p i) =
          ∑ _i ∈ univ.filter (fun i => ¬(p i).isLeft), E := by
        apply sum_congr rfl
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        cases hpi : p i with
        | inl ai => simp [hpi] at hi
        | inr ai => simp [w, hpi]
      _ = (univ.filter (fun i => ¬(p i).isLeft)).card * E := by simp
      _ = (N - s.card) * E := by rw [hcard]
  rw [← sum_range_add_sum_Ico (fun a => a) hsle]
  calc
    (∑ a ∈ range s.card, a) + ∑ a ∈ Ico s.card N, a ≤
        (∑ i ∈ s, w (p i)) + (N - s.card) * E := add_le_add hleft htail
    _ = (∑ i ∈ univ.filter (fun i => (p i).isLeft), w (p i)) +
        ∑ i ∈ univ.filter (fun i => ¬(p i).isLeft), w (p i) := by
      rw [show s = univ.filter (fun i => (p i).isLeft) by rfl, hright]
    _ = ∑ i, w (p i) := by
      exact Finset.sum_filter_add_sum_filter_not
        (s := (univ : Finset (Fin N)))
        (p := fun i => (p i).isLeft) (f := fun i => w (p i))

/-- A sampled error of norm `q^E`, with `E ≥ N`, may be adjoined as an
extra Newton column of weight `E`.  Cauchy--Binet then retains the full
determinant exponent even when the interpolation nodes lie above `E`. -/
theorem norm_det_perturbed_evaluation_le_of_exponent
    {T : Type*} [NormedField T] [IsUltrametricDist T]
    {N M E : ℕ} (A : Matrix (Fin N) (Fin N) T)
    (f : Fin N → ℕ → T) (x : Fin N → ℕ) (k : Fin N → ℕ)
    (hxM : ∀ j, x j < M) (hE : N ≤ E)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hcoeff : ∀ i (a : Fin M),
      ‖(fwdDiff 1)^[(a : ℕ)] (f i) 0‖ ≤ q ^ ((a : ℕ) - k i))
    (herr : ∀ i j, ‖A i j - f i (x j)‖ ≤ q ^ E) :
    ‖Matrix.det A‖ ≤
      q ^ ((∑ a ∈ range N, a) - ∑ i, k i) := by
  classical
  let C : Matrix (Fin N) (Fin M ⊕ Fin N) T := fun i a =>
    match a with
    | Sum.inl a => (fwdDiff 1)^[(a : ℕ)] (f i) 0
    | Sum.inr j => A i j - f i (x j)
  let V : Matrix (Fin M ⊕ Fin N) (Fin N) T := fun a j =>
    match a with
    | Sum.inl a => (Nat.choose (x j) (a : ℕ) : T)
    | Sum.inr j' => if j' = j then 1 else 0
  have hmul : C * V = A := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    have hnewton :
        (∑ a : Fin M, (fwdDiff 1)^[(a : ℕ)] (f i) 0 *
          (Nat.choose (x j) (a : ℕ) : T)) = f i (x j) := by
      have hmat := congrArg (fun B : Matrix (Fin N) (Fin N) T => B i j)
        (newtonCoeffMatrix_mul_chooseMatrix (R := T) f x hxM)
      simpa [Matrix.mul_apply, newtonCoeffMatrix, newtonChooseMatrix] using hmat
    simp only [C, V]
    rw [hnewton]
    simp
  rw [← hmul, det_mul_rectangular]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (pow_nonneg hq0 _) ?_
  intro p hpfilter
  have hp : Injective p := (mem_filter.mp hpfilter).2
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (pow_nonneg hq0 _) ?_
  intro σ hσ
  let w : Fin M ⊕ Fin N → ℕ :=
    Sum.elim (fun a : Fin M => a.1) (fun _ : Fin N => E)
  have hpsum : (∑ a ∈ range N, a) ≤ ∑ i, w (p i) :=
    sum_range_le_sum_sum_weight hE p hp
  have hksigma : (∑ i, k (σ i)) = ∑ i, k i := by
    simpa using Equiv.sum_comp σ k
  have hexponent :
      (∑ a ∈ range N, a) - ∑ i, k i ≤
        ∑ i, (w (p i) - k (σ i)) := by
    calc
      (∑ a ∈ range N, a) - ∑ i, k i ≤
          (∑ i, w (p i)) - ∑ i, k i :=
        Nat.sub_le_sub_right hpsum _
      _ = (∑ i, w (p i)) - ∑ i, k (σ i) := by rw [hksigma]
      _ ≤ ∑ i, (w (p i) - k (σ i)) :=
        sum_tsub_le_sum_tsub (fun i => w (p i)) (fun i => k (σ i))
  rw [norm_mul, norm_prod]
  calc
    ‖(Equiv.Perm.sign σ : T)‖ *
        ∏ i, ‖C (σ i) (p i) * V (p i) i‖ ≤
        1 * ∏ i, q ^ (w (p i) - k (σ i)) := by
      gcongr with i
      · exact IsUltrametricDist.norm_intCast_le_one T _
      · rw [norm_mul]
        calc
          ‖C (σ i) (p i)‖ * ‖V (p i) i‖ ≤
              q ^ (w (p i) - k (σ i)) * 1 := by
            gcongr
            · cases hpi : p i with
              | inl a =>
                  change ‖(fwdDiff 1)^[(a : ℕ)] (f (σ i)) 0‖ ≤
                    q ^ ((a : ℕ) - k (σ i))
                  exact hcoeff (σ i) a
              | inr j =>
                  change ‖A (σ i) j - f (σ i) (x j)‖ ≤
                    q ^ (E - k (σ i))
                  calc
                    ‖A (σ i) j - f (σ i) (x j)‖ ≤ q ^ E := herr (σ i) j
                    _ ≤ q ^ (E - k (σ i)) :=
                      pow_le_pow_of_le_one hq0 hq1 (Nat.sub_le E _)
            · cases hpi : p i with
              | inl a =>
                  change ‖(Nat.choose (x i) (a : ℕ) : T)‖ ≤ 1
                  exact
                    IsUltrametricDist.norm_natCast_le_one T
                      (Nat.choose (x i) (a : ℕ))
              | inr j =>
                  change ‖if j = i then (1 : T) else 0‖ ≤ 1
                  split <;> simp
          _ = q ^ (w (p i) - k (σ i)) := mul_one _
    _ = q ^ (∑ i, (w (p i) - k (σ i))) := by
      rw [one_mul, Finset.prod_pow_eq_pow_sum]
    _ ≤ q ^ ((∑ a ∈ range N, a) - ∑ i, k i) :=
      pow_le_pow_of_le_one hq0 hq1 hexponent

end DeterminantNorm

/-- The interpolation row with index `j` has level `⌊j / K⌋`.
For `N = K L`, every level from `0` through `L - 1` occurs `K` times. -/
def interpolationLevel (K : ℕ) {N : ℕ} (j : Fin N) : ℕ := j.1 / K

theorem interpolationLevel_le {K L N : ℕ} (hK : 0 < K)
    (hN : N = K * L) (j : Fin N) :
    interpolationLevel K j ≤ L - 1 := by
  have hj : j.1 < L * K := by simpa [hN, Nat.mul_comm] using j.2
  have hjdiv : j.1 / K < L := (Nat.div_lt_iff_lt_mul hK).2 hj
  simpa [interpolationLevel] using Nat.le_sub_one_of_lt hjdiv

/-- A coarse integral form of the balancing estimate for interpolation
levels.  It is enough for the later determinant height bound and, unlike the
sharper quarter-width version, needs no ordering hypothesis on the grid
coordinates. -/
theorem interpolation_weight_deviation_bounds {K L R N : ℕ}
    (hK : 0 < K) (hN : N = K * L)
    (r : Fin N → ℕ) (hr : ∀ j, r j < R) :
    2 * (∑ j, interpolationLevel K j * r j) ≤
        (L - 1) * (∑ j, r j) + N * (L - 1) * (R - 1) ∧
      (L - 1) * (∑ j, r j) ≤
        2 * (∑ j, interpolationLevel K j * r j) +
          N * (L - 1) * (R - 1) := by
  have hlevel : ∀ j : Fin N, interpolationLevel K j ≤ L - 1 :=
    fun j => interpolationLevel_le hK hN j
  constructor
  · calc
      2 * (∑ j, interpolationLevel K j * r j) =
          ∑ j, 2 * (interpolationLevel K j * r j) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ j, ((L - 1) * r j + (L - 1) * (R - 1)) := by
        apply Finset.sum_le_sum
        intro j _
        have hjr : r j ≤ R - 1 := Nat.le_sub_one_of_lt (hr j)
        nlinarith [hlevel j]
      _ = (L - 1) * (∑ j, r j) + N * (L - 1) * (R - 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [Fintype.card_fin]
        ring
  · calc
      (L - 1) * (∑ j, r j) = ∑ j, (L - 1) * r j := by
        rw [Finset.mul_sum]
      _ ≤ ∑ j, (2 * (interpolationLevel K j * r j) +
          (L - 1) * (R - 1)) := by
        apply Finset.sum_le_sum
        intro j _
        have hjr : r j ≤ R - 1 := Nat.le_sub_one_of_lt (hr j)
        nlinarith
      _ = 2 * (∑ j, interpolationLevel K j * r j) +
          N * (L - 1) * (R - 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [Fintype.card_fin]
        ring

/-- Replacing the monomial basis `1,t,…` by the integer-valued binomial
basis multiplies the evaluation determinant by the product of the row
factorials.  This is the exact denominator bookkeeping used in the
interpolation determinant. -/
theorem vandermonde_det_eq_factorials_mul_choose_det {N : ℕ}
    (v : Fin N → ℕ) :
    (Matrix.vandermonde fun i : Fin N => (v i : ℤ)).det =
      (∏ k : Fin N, (Nat.factorial k : ℤ)) *
        (Matrix.of fun i j : Fin N => (Nat.choose (v i) j : ℤ)).det := by
  rw [Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun i : Fin N => (v i : ℤ))
    (fun k => descPochhammer ℤ k)
    (fun k => descPochhammer_natDegree ℤ k)
    (fun k => monic_descPochhammer ℤ k)]
  convert! Matrix.det_mul_row
    (fun k : Fin N => (Nat.factorial k : ℤ))
    (Matrix.of fun i j : Fin N => (Nat.choose (v i) j : ℤ))
  · rw [Matrix.of_apply, descPochhammer_eval_eq_descFactorial]
    congr
    exact Nat.descFactorial_eq_factorial_mul_choose _ _

/-- Translating all nonnegative interpolation nodes by the same amount does
not change the determinant in the binomial basis.  This is the integral
version of the row operation used to center Yamada's determinant. -/
theorem choose_evaluation_det_sub_const {N q : ℕ} (v : Fin N → ℕ)
    (hq : ∀ i, q ≤ v i) :
    (Matrix.of fun i j : Fin N => (Nat.choose (v i - q) j : ℤ)).det =
      (Matrix.of fun i j : Fin N => (Nat.choose (v i) j : ℤ)).det := by
  let F : ℤ := ∏ k : Fin N, (Nat.factorial k : ℤ)
  have hF : F ≠ 0 := by
    dsimp [F]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => by
      exact_mod_cast Nat.factorial_ne_zero k.1
  apply mul_left_cancel₀ hF
  have hsub := Matrix.det_vandermonde_sub
    (R := ℤ) (fun i : Fin N => (v i : ℤ)) (q : ℤ)
  rw [show F * (Matrix.of fun i j : Fin N =>
        (Nat.choose (v i - q) j : ℤ)).det =
      (Matrix.vandermonde fun i : Fin N => ((v i - q : ℕ) : ℤ)).det by
        symm
        exact vandermonde_det_eq_factorials_mul_choose_det
          (fun i => v i - q),
    show F * (Matrix.of fun i j : Fin N =>
        (Nat.choose (v i) j : ℤ)).det =
      (Matrix.vandermonde fun i : Fin N => (v i : ℤ)).det by
        symm
        exact vandermonde_det_eq_factorials_mul_choose_det v]
  convert hsub using 2
  funext i
  ext j
  simp [Matrix.vandermonde, Nat.cast_sub (hq i)]

/-! ### Root-of-unity separation in the `p`-adic interpolation disk -/

/-- Every integer prime to `p` has a `(p-1)`st root-of-unity lift in
`Z_p` lying in its residue disk.  This is the precise Teichmüller-lift fact
needed below, obtained directly from Mathlib's Hensel lemma. -/
theorem exists_padicInt_rootOfUnity_close_natCast {p a : ℕ}
    [Fact p.Prime] (ha : ¬ p ∣ a) :
    ∃ w : ℤ_[p], w ^ (p - 1) = 1 ∧ ‖w - (a : ℤ_[p])‖ < 1 := by
  have hp : p.Prime := Fact.out
  let F : Polynomial ℤ_[p] := Polynomial.X ^ (p - 1) - 1
  have ha0 : a ≠ 0 := by
    intro haz
    subst a
    exact ha (by simp)
  have hone : 1 ≤ a ^ (p - 1) := one_le_pow₀ (Nat.pos_of_ne_zero ha0)
  have hfermat : p ∣ a ^ (p - 1) - 1 := by
    have hza : (a : ZMod p) ≠ 0 := by
      exact mt (CharP.cast_eq_zero_iff (ZMod p) p a).mp ha
    have hz : (a : ZMod p) ^ (p - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hza
    have hz' : ((1 : ℕ) : ZMod p) = ((a ^ (p - 1) : ℕ) : ZMod p) := by
      simpa only [Nat.cast_one, Nat.cast_pow] using hz.symm
    have hmod : 1 ≡ a ^ (p - 1) [MOD p] :=
      (ZMod.natCast_eq_natCast_iff 1 (a ^ (p - 1)) p).mp hz'
    exact (Nat.modEq_iff_dvd' hone).mp hmod
  have hFnorm : ‖F.aeval (a : ℤ_[p])‖ < 1 := by
    simp only [F, Polynomial.aeval_def, Polynomial.eval₂_sub,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one]
    have hcast : ((a ^ (p - 1) - 1 : ℕ) : ℤ_[p]) =
        (a : ℤ_[p]) ^ (p - 1) - 1 := by
      simpa only [Nat.cast_pow, Nat.cast_one] using
        (@Nat.cast_sub ℤ_[p] _ 1 (a ^ (p - 1)) hone)
    rw [← hcast]
    exact PadicInt.norm_natCast_lt_one_iff.mpr hfermat
  have hderiv : ‖F.derivative.aeval (a : ℤ_[p])‖ = 1 := by
    have haNorm : ‖(a : ℤ_[p])‖ = 1 :=
      PadicInt.norm_natCast_eq_one_iff.mpr (hp.coprime_iff_not_dvd.mpr ha)
    simp only [F, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_one, sub_zero, map_mul, Polynomial.aeval_def,
      Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      norm_mul, norm_pow]
    rw [haNorm]
    simp
  obtain ⟨w, hw, hwa, _⟩ :=
    hensels_lemma (F := F) (a := (a : ℤ_[p])) (by
      rw [hderiv, one_pow]
      exact hFnorm)
  refine ⟨w, ?_, ?_⟩
  · simp only [F, Polynomial.aeval_def, Polynomial.eval₂_sub,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one] at hw
    exact sub_eq_zero.mp hw
  · rw [hderiv] at hwa
    exact hwa

/-- Two `(p-1)`st roots of unity in the same open residue disk coincide. -/
theorem padicInt_rootOfUnity_eq_of_norm_sub_lt_one {p : ℕ}
    [Fact p.Prime] {x y : ℤ_[p]}
    (hx : x ^ (p - 1) = 1) (hy : y ^ (p - 1) = 1)
    (hxy : ‖x - y‖ < 1) : x = y := by
  have hp : p.Prime := Fact.out
  have hg : p - 1 ≠ 0 := (Nat.sub_pos_of_lt hp.one_lt).ne'
  have hxNorm : ‖x‖ = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg x) hg]
    rw [← norm_pow, hx, norm_one]
  let F : Polynomial ℤ_[p] := Polynomial.X ^ (p - 1) - 1
  have hFx : F.aeval x = 0 := by
    simp only [F, Polynomial.aeval_def, Polynomial.eval₂_sub,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one]
    exact sub_eq_zero.mpr hx
  have hFy : F.aeval y = 0 := by
    simp only [F, Polynomial.aeval_def, Polynomial.eval₂_sub,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one]
    exact sub_eq_zero.mpr hy
  have hderiv : ‖F.derivative.aeval x‖ = 1 := by
    simp only [F, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_one, sub_zero, map_mul, Polynomial.aeval_def,
      Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      norm_mul, norm_pow]
    rw [hxNorm]
    simp
  obtain ⟨z, _hz, _hzx, _hzd, huniq⟩ :=
    hensels_lemma (F := F) (a := x)
      (by rw [hFx, norm_zero, hderiv]; norm_num)
  have hxz : x = z := huniq x hFx (by rw [hderiv]; simp)
  have hyz : y = z := huniq y hFy (by
    rw [hderiv]
    simpa only [norm_sub_rev] using hxy)
  exact hxz.trans hyz.symm

/-- An open `p`-adic residue disk is stable under taking natural powers. -/
theorem padicInt_norm_pow_sub_pow_lt_one {p n : ℕ} [Fact p.Prime]
    {x y : ℤ_[p]} (hxy : ‖x - y‖ < 1) : ‖x ^ n - y ^ n‖ < 1 := by
  apply (PadicInt.norm_lt_one_iff_dvd (x ^ n - y ^ n)).2
  exact ((PadicInt.norm_lt_one_iff_dvd (x - y)).1 hxy).trans
    (sub_dvd_pow_sub_pow x y n)

/-- Open residue disks are stable under multiplication. -/
theorem padicInt_norm_mul_sub_mul_lt_one {p : ℕ} [Fact p.Prime]
    {x y a b : ℤ_[p]} (hxa : ‖x - a‖ < 1) (hyb : ‖y - b‖ < 1) :
    ‖x * y - a * b‖ < 1 := by
  obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd (x - a)).1 hxa
  obtain ⟨d, hd⟩ := (PadicInt.norm_lt_one_iff_dvd (y - b)).1 hyb
  apply (PadicInt.norm_lt_one_iff_dvd (x * y - a * b)).2
  refine ⟨x * d + c * b, ?_⟩
  have hx : x = (p : ℤ_[p]) * c + a := sub_eq_iff_eq_add.mp hc
  have hy : y = (p : ℤ_[p]) * d + b := sub_eq_iff_eq_add.mp hd
  rw [hx, hy]
  ring

/-- Equality after reduction to `ZMod p` puts two natural casts in the same
open disk of `Z_p`. -/
theorem padicInt_norm_natCast_sub_lt_one_of_zmod_eq {p m n : ℕ}
    [Fact p.Prime] (h : (m : ZMod p) = (n : ZMod p)) :
    ‖(m : ℤ_[p]) - (n : ℤ_[p])‖ < 1 := by
  apply (PadicInt.norm_lt_one_iff_dvd
    ((m : ℤ_[p]) - (n : ℤ_[p]))).2
  rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker]
  simpa using sub_eq_zero.mpr h

/-- On one `ZMod p` interpolation fiber the Teichmüller part of
`6^r 3^s` is constant. -/
theorem padicInt_root_factor_eq_of_yamadaGridValue_eq
    {p : ℕ} [Fact p.Prime] {w₂ w₃ : ℤ_[p]}
    (hw₂ : w₂ ^ (p - 1) = 1) (hw₃ : w₃ ^ (p - 1) = 1)
    (hw₂c : ‖w₂ - (2 : ℤ_[p])‖ < 1)
    (hw₃c : ‖w₃ - (3 : ℤ_[p])‖ < 1)
    {r₁ s₁ r₂ s₂ : ℕ}
    (hmod : (6 : ZMod p) ^ r₁ * (3 : ZMod p) ^ s₁ =
      (6 : ZMod p) ^ r₂ * (3 : ZMod p) ^ s₂) :
    (w₂ * w₃) ^ r₁ * w₃ ^ s₁ =
      (w₂ * w₃) ^ r₂ * w₃ ^ s₂ := by
  have hroot (r s : ℕ) :
      (((w₂ * w₃) ^ r * w₃ ^ s) ^ (p - 1)) = 1 := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm r (p - 1),
      mul_comm s (p - 1), pow_mul, pow_mul, mul_pow, hw₂, hw₃]
    simp
  have hw₆c : ‖w₂ * w₃ - (6 : ℤ_[p])‖ < 1 := by
    convert padicInt_norm_mul_sub_mul_lt_one hw₂c hw₃c using 1 <;> norm_num
  have hclose (r s : ℕ) :
      ‖(w₂ * w₃) ^ r * w₃ ^ s -
        ((6 ^ r * 3 ^ s : ℕ) : ℤ_[p])‖ < 1 := by
    have hr := padicInt_norm_pow_sub_pow_lt_one (n := r) hw₆c
    have hs := padicInt_norm_pow_sub_pow_lt_one (n := s) hw₃c
    convert padicInt_norm_mul_sub_mul_lt_one hr hs using 1 <;> norm_num
  have hnat :
      ‖((6 ^ r₁ * 3 ^ s₁ : ℕ) : ℤ_[p]) -
        ((6 ^ r₂ * 3 ^ s₂ : ℕ) : ℤ_[p])‖ < 1 := by
    apply padicInt_norm_natCast_sub_lt_one_of_zmod_eq
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hmod
  have hdist :
      ‖((w₂ * w₃) ^ r₁ * w₃ ^ s₁) -
        ((w₂ * w₃) ^ r₂ * w₃ ^ s₂)‖ < 1 := by
    let A : ℤ_[p] := (w₂ * w₃) ^ r₁ * w₃ ^ s₁
    let B : ℤ_[p] := ((6 ^ r₁ * 3 ^ s₁ : ℕ) : ℤ_[p])
    let C : ℤ_[p] := ((6 ^ r₂ * 3 ^ s₂ : ℕ) : ℤ_[p])
    let D : ℤ_[p] := (w₂ * w₃) ^ r₂ * w₃ ^ s₂
    have hAB : ‖A - B‖ < 1 := hclose r₁ s₁
    have hBC : ‖B - C‖ < 1 := hnat
    have hCD : ‖C - D‖ < 1 := by
      simpa only [norm_sub_rev] using hclose r₂ s₂
    change ‖A - D‖ < 1
    have heq : A - D = (A - B) + ((B - C) + (C - D)) := by ring
    rw [heq]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt hAB ((IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt hBC hCD)))
  exact padicInt_rootOfUnity_eq_of_norm_sub_lt_one
    (hroot r₁ s₁) (hroot r₂ s₂) hdist

/-- Powers of a closed unit stay no farther from one than the unit itself
in any ultrametric field. -/
theorem norm_pow_sub_one_le
    {T : Type*} [NormedField T] [IsUltrametricDist T]
    {u : T} {q : ℝ} (hq0 : 0 ≤ q) (huNorm : ‖u‖ ≤ 1)
    (hu : ‖u - 1‖ ≤ q) (n : ℕ) : ‖u ^ n - 1‖ ≤ q := by
  induction n with
  | zero => simp [hq0]
  | succ n ih =>
      have heq : u ^ (n + 1) - 1 = u ^ n * (u - 1) + (u ^ n - 1) := by
        rw [pow_succ]
        ring
      rw [heq]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      rw [norm_mul, norm_pow]
      exact (mul_le_mul (pow_le_one₀ (norm_nonneg u) huNorm) hu
        (norm_nonneg _) (by positivity)).trans (one_mul q).le

/-- The `p`-adic LTE identity for a principal unit and an exponent prime to
`p`, proved by showing that its geometric factor has norm one. -/
theorem padic_norm_pow_sub_one_eq {p n : ℕ} [Fact p.Prime]
    {u : ℚ_[p]} (hn : ¬ p ∣ n) (huNorm : ‖u‖ ≤ 1)
    (hu : ‖u - 1‖ < 1) : ‖u ^ n - 1‖ = ‖u - 1‖ := by
  let q : ℝ := (p : ℝ)⁻¹
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp1)
  have huq : ‖u - 1‖ ≤ q := by
    have h := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one (u - 1) 0).1 (by
      simpa using hu)
    simpa [q, zpow_neg, zpow_one] using h
  let G : ℚ_[p] := ∑ i ∈ range n, u ^ i
  have hGclose : ‖G - (n : ℚ_[p])‖ ≤ q := by
    have heq : G - (n : ℚ_[p]) = ∑ i ∈ range n, (u ^ i - 1) := by
      simp only [G, sum_sub_distrib]
      simp
    rw [heq]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hq0 ?_
    intro i hi
    exact norm_pow_sub_one_le hq0 huNorm huq i
  have hnNorm : ‖(n : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (hp.coprime_iff_not_dvd.mpr hn)
  have hGNorm : ‖G‖ = 1 := by
    rw [← hnNorm]
    exact Padic.norm_eq_of_norm_sub_lt_right
      (hGclose.trans_lt (by simpa [hnNorm] using hq1))
  have hfactor : (u - 1) * G = u ^ n - 1 := by
    simpa [G] using mul_geom_sum u n
  rw [← hfactor, norm_mul, hGNorm, mul_one]

/-- Dividing an integral unit by its root-of-unity lift produces a principal
unit of norm one, at distance at most `p⁻¹` from one. -/
theorem padic_principalUnit_properties {p a : ℕ} [Fact p.Prime]
    (ha : ¬ p ∣ a) {w : ℤ_[p]}
    (hw : w ^ (p - 1) = 1) (hwc : ‖w - (a : ℤ_[p])‖ < 1) :
    let u : ℚ_[p] := (a : ℚ_[p]) / (w : ℚ_[p])
    ‖u‖ = 1 ∧ ‖u - 1‖ < 1 ∧ ‖u - 1‖ ≤ (p : ℝ)⁻¹ := by
  have hp : p.Prime := Fact.out
  have hg : p - 1 ≠ 0 := (Nat.sub_pos_of_lt hp.one_lt).ne'
  have hwNorm : ‖w‖ = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg w) hg]
    rw [← norm_pow, hw, norm_one]
  have hwQNorm : ‖(w : ℚ_[p])‖ = 1 := by simpa using hwNorm
  have haNorm : ‖(a : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (hp.coprime_iff_not_dvd.mpr ha)
  let u : ℚ_[p] := (a : ℚ_[p]) / (w : ℚ_[p])
  have huNorm : ‖u‖ = 1 := by simp [u, haNorm, hwQNorm]
  have huclose : ‖u - 1‖ < 1 := by
    have hcoe : ‖((w - a : ℤ_[p]) : ℚ_[p])‖ < 1 := by
      rw [PadicInt.padic_norm_e_of_padicInt]
      exact hwc
    have hwneQ : (w : ℚ_[p]) ≠ 0 := by
      apply (norm_ne_zero_iff).mp
      rw [hwQNorm]
      norm_num
    have hcoea : (((a : ℕ) : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) :=
      PadicInt.coe_natCast a
    have hsub : ((w - a : ℤ_[p]) : ℚ_[p]) =
        (w : ℚ_[p]) - (a : ℚ_[p]) := by
      change (w : ℚ_[p]) - (((a : ℕ) : ℤ_[p]) : ℚ_[p]) = _
      rw [hcoea]
    have hform : u - 1 =
        -((w - a : ℤ_[p]) : ℚ_[p]) / (w : ℚ_[p]) := by
      calc
        u - 1 = ((a : ℚ_[p]) - (w : ℚ_[p])) / (w : ℚ_[p]) := by
          dsimp [u]
          field_simp [hwneQ]
        _ = -((w : ℚ_[p]) - (a : ℚ_[p])) / (w : ℚ_[p]) := by ring
        _ = -((w - a : ℤ_[p]) : ℚ_[p]) / (w : ℚ_[p]) := by rw [hsub]
    rw [hform, norm_div, norm_neg, hwQNorm, div_one]
    exact hcoe
  refine ⟨huNorm, huclose, ?_⟩
  have h := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one (u - 1) 0).1 (by
    simpa using huclose)
  simpa [zpow_neg, zpow_one] using h

/-- For the lift of `2`, the principal-unit distance is exactly controlled
by the Fermat-quotient valuation. -/
theorem padic_principalUnit_two_high {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {w : ℤ_[p]}
    (hw : w ^ (p - 1) = 1) (hwc : ‖w - (2 : ℤ_[p])‖ < 1) :
    let u : ℚ_[p] := (2 : ℚ_[p]) / (w : ℚ_[p])
    ‖u‖ = 1 ∧ ‖u - 1‖ < 1 ∧
      ‖u - 1‖ ≤ (p : ℝ) ^ (-(padicValNat p (mersenne (p - 1)) : ℤ)) := by
  have hp : p.Prime := Fact.out
  have h2not : ¬ p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hbasic := padic_principalUnit_properties h2not hw hwc
  let u : ℚ_[p] := (2 : ℚ_[p]) / (w : ℚ_[p])
  have huNorm : ‖u‖ = 1 := hbasic.1
  have huclose : ‖u - 1‖ < 1 := hbasic.2.1
  have hpnotg : ¬ p ∣ p - 1 := by
    intro h
    exact (not_le_of_gt (Nat.sub_lt hp.pos zero_lt_one))
      (Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) h)
  have hupow : u ^ (p - 1) - 1 = (mersenne (p - 1) : ℚ_[p]) := by
    have hwQ : ((w : ℚ_[p]) ^ (p - 1)) = 1 := by
      have h := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hw
      simpa using h
    have hone : 1 ≤ 2 ^ (p - 1) := one_le_pow₀ (by norm_num)
    have hcast : ((2 ^ (p - 1) - 1 : ℕ) : ℚ_[p]) =
        (2 : ℚ_[p]) ^ (p - 1) - 1 := by
      simpa only [Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] using
        (@Nat.cast_sub ℚ_[p] _ 1 (2 ^ (p - 1)) hone)
    dsimp [u]
    rw [div_pow, hwQ, div_one]
    exact hcast.symm
  have hval : ‖u - 1‖ = ‖(mersenne (p - 1) : ℚ_[p])‖ := by
    rw [← hupow, padic_norm_pow_sub_one_eq hpnotg huNorm.le huclose]
  refine ⟨huNorm, huclose, ?_⟩
  rw [hval]
  have hdNat : p ^ padicValNat p (mersenne (p - 1)) ∣
      mersenne (p - 1) := pow_padicValNat_dvd
  have hdInt : (p ^ padicValNat p (mersenne (p - 1)) : ℤ) ∣
      (mersenne (p - 1) : ℕ) := by exact_mod_cast hdNat
  exact (Padic.norm_int_le_pow_iff_dvd
    (mersenne (p - 1) : ℤ) (padicValNat p (mersenne (p - 1)))).2 hdInt

/-- The normalized determinant estimate underlying the specialized
`p`-adic interpolation argument.  The factor involving `u₂` is treated as a
uniform perturbation, while the functions involving `u₃` are expanded in the
Mahler basis. -/
theorem norm_yamadaNormalizedMatrix_le
    {p N M b : ℕ} [Fact p.Prime]
    (hN : 0 < N) (k l : Fin N → ℕ) (r s : Fin N → ℕ)
    (x : Fin N → ℕ) (_hx : ∀ j, x j = r j + s j)
    (hxM : ∀ j, x j < M) (hxinj : Injective x)
    (u₂ u₃ : ℚ_[p]) (hu₂Norm : ‖u₂‖ = 1) (hu₃Norm : ‖u₃‖ = 1)
    (hu₂ : ‖u₂ - 1‖ ≤ ((p : ℝ)⁻¹) ^ M)
    (hu₃ : ‖u₃ - 1‖ ≤ (p : ℝ)⁻¹) :
    ‖Matrix.det (fun i j : Fin N =>
      (Nat.choose (b * x j) (k i) : ℚ_[p]) *
        (u₃ ^ (l i)) ^ (x j) * u₂ ^ (l i * r j))‖ ≤
      ((p : ℝ)⁻¹) ^ ((∑ a ∈ range N, a) - ∑ i, k i) := by
  let q : ℝ := (p : ℝ)⁻¹
  have hpR : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := (inv_lt_one_of_one_lt₀ hpR).le
  let A : Matrix (Fin N) (Fin N) ℚ_[p] := fun i j =>
    (Nat.choose (b * x j) (k i) : ℚ_[p]) *
      (u₃ ^ (l i)) ^ (x j) * u₂ ^ (l i * r j)
  let f : Fin N → ℕ → ℚ_[p] := fun i n =>
    (Nat.choose (b * n) (k i) : ℚ_[p]) * (u₃ ^ (l i)) ^ n
  apply norm_det_perturbed_evaluation_le A f x k hN hxM hxinj hq0 hq1
  · intro i a
    apply norm_fwdDiff_iter_choose_mul_pow_le_all hq0 hq1
    · rw [norm_pow, hu₃Norm, one_pow]
    · exact norm_pow_sub_one_le hq0 hu₃Norm.le hu₃ (l i)
  · intro i j
    have herrPow : ‖u₂ ^ (l i * r j) - 1‖ ≤ q ^ M :=
      norm_pow_sub_one_le (pow_nonneg hq0 _) hu₂Norm.le hu₂ _
    have hbase :
        ‖(Nat.choose (b * x j) (k i) : ℚ_[p]) *
          (u₃ ^ l i) ^ x j‖ ≤ 1 := by
      rw [norm_mul, norm_pow, norm_pow, hu₃Norm, one_pow, one_pow]
      simpa using IsUltrametricDist.norm_natCast_le_one ℚ_[p]
        (Nat.choose (b * x j) (k i))
    have heq : A i j - f i (x j) =
        ((Nat.choose (b * x j) (k i) : ℚ_[p]) *
          (u₃ ^ l i) ^ x j) * (u₂ ^ (l i * r j) - 1) := by
      simp only [A, f]
      ring
    rw [heq, norm_mul]
    exact (mul_le_mul hbase herrPow (norm_nonneg _) (by positivity)).trans
      (one_mul (q ^ M)).le

/-- The form used in the Fermat-quotient application: the nodes need only
be bounded by `M`, while the high principal unit is `q^E`-close to one with
`E ≥ N`. -/
theorem norm_yamadaNormalizedMatrix_le_of_exponent
    {p N M E b : ℕ} [Fact p.Prime]
    (k l : Fin N → ℕ) (r : Fin N → ℕ) (x : Fin N → ℕ)
    (hxM : ∀ j, x j < M) (hE : N ≤ E)
    (u₂ u₃ : ℚ_[p]) (hu₂Norm : ‖u₂‖ = 1) (hu₃Norm : ‖u₃‖ = 1)
    (hu₂ : ‖u₂ - 1‖ ≤ ((p : ℝ)⁻¹) ^ E)
    (hu₃ : ‖u₃ - 1‖ ≤ (p : ℝ)⁻¹) :
    ‖Matrix.det (fun i j : Fin N =>
      (Nat.choose (b * x j) (k i) : ℚ_[p]) *
        (u₃ ^ (l i)) ^ (x j) * u₂ ^ (l i * r j))‖ ≤
      ((p : ℝ)⁻¹) ^ ((∑ a ∈ range N, a) - ∑ i, k i) := by
  let q : ℝ := (p : ℝ)⁻¹
  have hpR : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := (inv_lt_one_of_one_lt₀ hpR).le
  let A : Matrix (Fin N) (Fin N) ℚ_[p] := fun i j =>
    (Nat.choose (b * x j) (k i) : ℚ_[p]) *
      (u₃ ^ (l i)) ^ (x j) * u₂ ^ (l i * r j)
  let f : Fin N → ℕ → ℚ_[p] := fun i n =>
    (Nat.choose (b * n) (k i) : ℚ_[p]) * (u₃ ^ (l i)) ^ n
  apply norm_det_perturbed_evaluation_le_of_exponent A f x k hxM hE hq0 hq1
  · intro i a
    apply norm_fwdDiff_iter_choose_mul_pow_le_all hq0 hq1
    · rw [norm_pow, hu₃Norm, one_pow]
    · exact norm_pow_sub_one_le hq0 hu₃Norm.le hu₃ (l i)
  · intro i j
    have herrPow : ‖u₂ ^ (l i * r j) - 1‖ ≤ q ^ E :=
      norm_pow_sub_one_le (pow_nonneg hq0 _) hu₂Norm.le hu₂ _
    have hbase :
        ‖(Nat.choose (b * x j) (k i) : ℚ_[p]) *
          (u₃ ^ l i) ^ x j‖ ≤ 1 := by
      rw [norm_mul, norm_pow, norm_pow, hu₃Norm, one_pow, one_pow]
      simpa using IsUltrametricDist.norm_natCast_le_one ℚ_[p]
        (Nat.choose (b * x j) (k i))
    have heq : A i j - f i (x j) =
        ((Nat.choose (b * x j) (k i) : ℚ_[p]) *
          (u₃ ^ l i) ^ x j) * (u₂ ^ (l i * r j) - 1) := by
      simp only [A, f]
      ring
    rw [heq, norm_mul]
    exact (mul_le_mul hbase herrPow (norm_nonneg _) (by positivity)).trans
      (one_mul (q ^ E)).le

/-- Specialized `p`-adic determinant estimate for the integral functions
`choose (b(r+s)) k · 6^(lr) · 3^(ls)` on one residue fiber.  Teichmüller
factors are constant on the fiber; after removing their unit row factors,
the preceding normalized estimate applies. -/
theorem norm_yamada_evaluation_le
    {p N M E b : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hN : 0 < N)
    (k l : Fin N → ℕ) (r s : Fin N → ℕ) (x : Fin N → ℕ)
    (hx : ∀ j, x j = r j + s j) (hxM : ∀ j, x j < M)
    (hE : N ≤ E) (hEval : E ≤ padicValNat p (mersenne (p - 1)))
    (hfiber : ∀ i j,
      (6 : ZMod p) ^ (r i) * (3 : ZMod p) ^ (s i) =
        (6 : ZMod p) ^ (r j) * (3 : ZMod p) ^ (s j)) :
    ‖Matrix.det (fun i j : Fin N =>
      (Nat.choose (b * x j) (k i) : ℚ_[p]) *
        (6 : ℚ_[p]) ^ (l i * r j) * (3 : ℚ_[p]) ^ (l i * s j))‖ ≤
      ((p : ℝ)⁻¹) ^ ((∑ a ∈ range N, a) - ∑ i, k i) := by
  have hp : p.Prime := Fact.out
  have h2not : ¬ p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have h3not : ¬ p ∣ 3 := by
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  obtain ⟨w₂, hw₂, hw₂c⟩ :=
    exists_padicInt_rootOfUnity_close_natCast (p := p) h2not
  obtain ⟨w₃, hw₃, hw₃c⟩ :=
    exists_padicInt_rootOfUnity_close_natCast (p := p) h3not
  let u₂ : ℚ_[p] := (2 : ℚ_[p]) / (w₂ : ℚ_[p])
  let u₃ : ℚ_[p] := (3 : ℚ_[p]) / (w₃ : ℚ_[p])
  have hu₂data := padic_principalUnit_two_high hp2 hw₂ hw₂c
  have hu₃data := padic_principalUnit_properties h3not hw₃ hw₃c
  have hu₂Norm : ‖u₂‖ = 1 := by simpa [u₂] using hu₂data.1
  have hu₃Norm : ‖u₃‖ = 1 := by simpa [u₃] using hu₃data.1
  have hu₃ : ‖u₃ - 1‖ ≤ (p : ℝ)⁻¹ := by simpa [u₃] using hu₃data.2.2
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hq1 : (p : ℝ)⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hpR).le
  have hu₂base : ‖u₂ - 1‖ ≤ ((p : ℝ)⁻¹) ^
      padicValNat p (mersenne (p - 1)) := by
    have h := hu₂data.2.2
    simpa [u₂, zpow_neg, zpow_natCast] using h
  have hu₂ : ‖u₂ - 1‖ ≤ ((p : ℝ)⁻¹) ^ E :=
    hu₂base.trans (pow_le_pow_of_le_one hq0 hq1 hEval)
  let j₀ : Fin N := ⟨0, hN⟩
  let ρz : ℤ_[p] := (w₂ * w₃) ^ (r j₀) * w₃ ^ (s j₀)
  let ρ : ℚ_[p] := (ρz : ℚ_[p])
  have hrootz : ∀ j, (w₂ * w₃) ^ (r j) * w₃ ^ (s j) = ρz := by
    intro j
    exact padicInt_root_factor_eq_of_yamadaGridValue_eq
      hw₂ hw₃ hw₂c hw₃c (hfiber j j₀)
  have hw₂Norm : ‖(w₂ : ℚ_[p])‖ = 1 := by
    have hg : p - 1 ≠ 0 := (Nat.sub_pos_of_lt hp.one_lt).ne'
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg (w₂ : ℚ_[p])) hg]
    rw [← norm_pow]
    have hcast := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hw₂
    simpa using congrArg norm hcast
  have hw₃Norm : ‖(w₃ : ℚ_[p])‖ = 1 := by
    have hg : p - 1 ≠ 0 := (Nat.sub_pos_of_lt hp.one_lt).ne'
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg (w₃ : ℚ_[p])) hg]
    rw [← norm_pow]
    have hcast := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hw₃
    simpa using congrArg norm hcast
  have hρzpow : ρz ^ (p - 1) = 1 := by
    dsimp only [ρz]
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (r j₀) (p - 1),
      mul_comm (s j₀) (p - 1), pow_mul, pow_mul, mul_pow, hw₂, hw₃]
    simp
  have hρpow : ρ ^ (p - 1) = 1 := by
    have hcast := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hρzpow
    simpa [ρ] using hcast
  have hρNorm : ‖ρ‖ = 1 := by
    have hg : p - 1 ≠ 0 := (Nat.sub_pos_of_lt hp.one_lt).ne'
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg ρ) hg]
    rw [← norm_pow, hρpow, norm_one]
  have hw₂ne : (w₂ : ℚ_[p]) ≠ 0 := (norm_ne_zero_iff.mp (by simp [hw₂Norm]))
  have hw₃ne : (w₃ : ℚ_[p]) ≠ 0 := (norm_ne_zero_iff.mp (by simp [hw₃Norm]))
  have htwo : (2 : ℚ_[p]) = (w₂ : ℚ_[p]) * u₂ := by
    dsimp [u₂]
    field_simp
  have hthree : (3 : ℚ_[p]) = (w₃ : ℚ_[p]) * u₃ := by
    dsimp [u₃]
    field_simp
  have hdecomp : ∀ j,
      (6 : ℚ_[p]) ^ (r j) * (3 : ℚ_[p]) ^ (s j) =
        ρ * u₃ ^ (x j) * u₂ ^ (r j) := by
    intro j
    have hrootQ :
        (w₂ : ℚ_[p]) ^ r j * (w₃ : ℚ_[p]) ^ r j *
            (w₃ : ℚ_[p]) ^ s j = ρ := by
      have hc := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) (hrootz j)
      simpa [ρ, map_mul, map_pow, mul_pow, mul_assoc] using hc
    have hxj := hx j
    calc
      (6 : ℚ_[p]) ^ r j * (3 : ℚ_[p]) ^ s j =
          (2 : ℚ_[p]) ^ r j * (3 : ℚ_[p]) ^ (r j + s j) := by
        rw [pow_add, show (6 : ℚ_[p]) = 2 * 3 by norm_num, mul_pow]
        ring
      _ = ((w₂ : ℚ_[p]) * u₂) ^ r j *
          (((w₃ : ℚ_[p]) * u₃) ^ (r j + s j)) := by rw [← htwo, ← hthree]
      _ = ((w₂ : ℚ_[p]) ^ r j * (w₃ : ℚ_[p]) ^ r j *
            (w₃ : ℚ_[p]) ^ s j) *
          u₃ ^ (r j + s j) * u₂ ^ r j := by
        simp only [mul_pow]
        rw [pow_add]
        ring
      _ = ρ * u₃ ^ (x j) * u₂ ^ (r j) := by rw [hrootQ, hxj]
  let A : Matrix (Fin N) (Fin N) ℚ_[p] := fun i j =>
    (Nat.choose (b * x j) (k i) : ℚ_[p]) *
      (u₃ ^ (l i)) ^ (x j) * u₂ ^ (l i * r j)
  let B : Matrix (Fin N) (Fin N) ℚ_[p] := fun i j =>
    (Nat.choose (b * x j) (k i) : ℚ_[p]) *
      (6 : ℚ_[p]) ^ (l i * r j) * (3 : ℚ_[p]) ^ (l i * s j)
  have hBA : B = Matrix.diagonal (fun i => ρ ^ (l i)) * A := by
    ext i j
    rw [Matrix.diagonal_mul]
    simp only [B, A]
    have hd := congrArg (fun z : ℚ_[p] => z ^ (l i)) (hdecomp j)
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul] at hd
    rw [Nat.mul_comm (l i) (r j), Nat.mul_comm (l i) (s j)]
    calc
      (Nat.choose (b * x j) (k i) : ℚ_[p]) *
            6 ^ (r j * l i) * 3 ^ (s j * l i) =
          (Nat.choose (b * x j) (k i) : ℚ_[p]) *
            (6 ^ (r j * l i) * 3 ^ (s j * l i)) := by ring
      _ = (Nat.choose (b * x j) (k i) : ℚ_[p]) *
          ((ρ * u₃ ^ x j) ^ l i * (u₂ ^ r j) ^ l i) := by rw [hd]
      _ = ρ ^ l i * ((Nat.choose (b * x j) (k i) : ℚ_[p]) *
          (u₃ ^ l i) ^ x j * u₂ ^ (r j * l i)) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
        ring
  have hnormBA : ‖Matrix.det B‖ = ‖Matrix.det A‖ := by
    rw [hBA, Matrix.det_mul, Matrix.det_diagonal, norm_mul, norm_prod]
    simp [hρNorm]
  rw [show (fun i j : Fin N =>
      (Nat.choose (b * x j) (k i) : ℚ_[p]) *
        (6 : ℚ_[p]) ^ (l i * r j) * (3 : ℚ_[p]) ^ (l i * s j)) = B by rfl,
    hnormBA]
  exact norm_yamadaNormalizedMatrix_le_of_exponent
    k l r x hxM hE u₂ u₃ hu₂Norm hu₃Norm hu₂ hu₃

/-- The integral interpolation matrix used for the specialization
`(α₁, α₂) = (6,3)`.  Its row `(k,l)` is the function
`(r,s) ↦ choose (b(r+s)) k · 6^(lr) · 3^(ls)`. -/
def yamadaInterpolationMatrix (b K L : ℕ)
    (z : (Fin K × Fin L) → ℕ × ℕ) :
    Matrix (Fin K × Fin L) (Fin K × Fin L) ℤ :=
  fun i j => ((Nat.choose (b * (z j).1 + b * (z j).2) i.1.1 *
    6 ^ (i.2.1 * (z j).1) * 3 ^ (i.2.1 * (z j).2) : ℕ) : ℤ)

/-- Uniform archimedean height bound for every entry of the specialized
interpolation matrix on the rectangle `[0,R) × [0,S)`. -/
theorem yamadaInterpolationMatrix_entry_natAbs_le
    {b K L R S : ℕ} {z : (Fin K × Fin L) → ℕ × ℕ}
    (hr : ∀ j, (z j).1 < R) (hs : ∀ j, (z j).2 < S)
    (i j : Fin K × Fin L) :
    (yamadaInterpolationMatrix b K L z i j).natAbs ≤
      (b * (R + S) + 1) ^ K * 6 ^ (L * R) * 3 ^ (L * S) := by
  let t := b * (z j).1 + b * (z j).2
  let T := b * (R + S) + 1
  have ht : t ≤ b * (R + S) := by
    dsimp [t]
    nlinarith [Nat.mul_le_mul_left b (Nat.add_le_add (Nat.le_of_lt (hr j))
      (Nat.le_of_lt (hs j)))]
  have hchoose : Nat.choose t i.1.1 ≤ T ^ K := by
    calc
      Nat.choose t i.1.1 ≤ t ^ i.1.1 := Nat.choose_le_pow _ _
      _ ≤ T ^ i.1.1 := pow_le_pow_left' (by dsimp [T]; omega) _
      _ ≤ T ^ K := pow_le_pow_right' (by dsimp [T]; omega) i.1.2.le
  have hrpow : 6 ^ (i.2.1 * (z j).1) ≤ 6 ^ (L * R) := by
    exact pow_le_pow_right' (by norm_num)
      (Nat.mul_le_mul i.2.2.le (Nat.le_of_lt (hr j)))
  have hspow : 3 ^ (i.2.1 * (z j).2) ≤ 3 ^ (L * S) := by
    exact pow_le_pow_right' (by norm_num)
      (Nat.mul_le_mul i.2.2.le (Nat.le_of_lt (hs j)))
  change Nat.choose t i.1.1 * 6 ^ (i.2.1 * (z j).1) *
      3 ^ (i.2.1 * (z j).2) ≤ _
  exact Nat.mul_le_mul (Nat.mul_le_mul hchoose hrpow) hspow

/-- The two integer bases used in Yamada's specialization are
multiplicatively independent already on nonnegative exponents. -/
theorem six_pow_mul_three_pow_injective :
    Function.Injective (fun z : ℕ × ℕ => 6 ^ z.1 * 3 ^ z.2) := by
  intro a b hab
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := congrArg (padicValNat 2) hab
  simp [padicValNat.mul, padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd] at h2
  have hr : a.1 = b.1 := by omega
  change 6 ^ a.1 * 3 ^ a.2 = 6 ^ b.1 * 3 ^ b.2 at hab
  rw [hr] at hab
  have hsPow : 3 ^ a.2 = 3 ^ b.2 := by
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 6 ^ b.1) hab
  exact Prod.ext hr
    (pow_right_injective₀ (by norm_num : 0 < (3 : ℕ)) (by norm_num) hsPow)

/-- The reduction modulo `p` of the interpolation-grid monomial
`6^r 3^s`. -/
def yamadaGridValue (p R S : ℕ) (z : Fin R × Fin S) : ZMod p :=
  (6 : ZMod p) ^ z.1.1 * (3 : ZMod p) ^ z.2.1

/-- A rectangular grid of area at least `p L` contains `L` points on
which `6^r 3^s` has one fixed residue modulo `p`. -/
theorem exists_large_yamadaGridValue_fiber {p R S L : ℕ}
    (hp : p.Prime) (harea : p * L ≤ R * S) :
    ∃ c : ZMod p,
      L ≤ (Finset.univ.filter fun z : Fin R × Fin S =>
        yamadaGridValue p R S z = c).card := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have harea' : Fintype.card (ZMod p) * L ≤
      Fintype.card (Fin R × Fin S) := by
    simpa [ZMod.card, Fintype.card_prod, Fintype.card_fin] using harea
  exact Fintype.exists_le_card_fiber_of_mul_le_card
    (yamadaGridValue p R S) harea'

/-- Two different points of a fixed residue fiber having the same value of
`r+s` force the multiplicative order of `2` modulo `p` to divide one of the
two nonzero coordinate differences.  This is Yamada's degenerate-grid
alternative, stated without choosing discrete logarithms. -/
theorem orderOf_two_dvd_coordinate_difference_of_grid_collision
    {p r₁ s₁ r₂ s₂ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hne : (r₁, s₁) ≠ (r₂, s₂)) (hsum : r₁ + s₁ = r₂ + s₂)
    (hmod : (6 : ZMod p) ^ r₁ * (3 : ZMod p) ^ s₁ =
      (6 : ZMod p) ^ r₂ * (3 : ZMod p) ^ s₂) :
    ∃ d : ℕ, 0 < d ∧ (d = r₁ - r₂ ∨ d = r₂ - r₁) ∧
      orderOf (2 : ZMod p) ∣ d := by
  letI : Fact p.Prime := ⟨hp⟩
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    apply hp3
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
      ((CharP.cast_eq_zero_iff (ZMod p) p 3).mp h)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    apply hp2
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp h)
  rcases lt_trichotomy r₁ r₂ with hlt | heq | hgt
  ·
    let d := r₂ - r₁
    have hd : 0 < d := Nat.sub_pos_of_lt hlt
    have hr : r₂ = r₁ + d := by omega
    have hs : s₁ = s₂ + d := by omega
    rw [hr, hs, pow_add, pow_add] at hmod
    have hcommon : (6 : ZMod p) ^ r₁ * (3 : ZMod p) ^ s₂ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by
        simpa [show (6 : ZMod p) = 2 * 3 by norm_num] using mul_ne_zero h2 h3))
        (pow_ne_zero _ h3)
    have hdEq : (3 : ZMod p) ^ d = (6 : ZMod p) ^ d := by
      apply mul_left_cancel₀ hcommon
      calc
        ((6 : ZMod p) ^ r₁ * 3 ^ s₂) * 3 ^ d =
            6 ^ r₁ * (3 ^ s₂ * 3 ^ d) := by ring
        _ = (6 ^ r₁ * 6 ^ d) * 3 ^ s₂ := hmod
        _ = (6 ^ r₁ * 3 ^ s₂) * 6 ^ d := by ring
    have hpow : (2 : ZMod p) ^ d = 1 := by
      apply mul_right_cancel₀ (pow_ne_zero _ h3)
      simpa [show (6 : ZMod p) = 2 * 3 by norm_num, mul_pow,
        mul_assoc, mul_left_comm, mul_comm] using hdEq.symm
    exact ⟨d, hd, Or.inr rfl, orderOf_dvd_iff_pow_eq_one.mpr hpow⟩
  · exfalso
    apply hne
    apply Prod.ext heq
    omega
  ·
    let d := r₁ - r₂
    have hd : 0 < d := Nat.sub_pos_of_lt hgt
    have hr : r₁ = r₂ + d := by omega
    have hs : s₂ = s₁ + d := by omega
    rw [hr, hs, pow_add, pow_add] at hmod
    have hcommon : (6 : ZMod p) ^ r₂ * (3 : ZMod p) ^ s₁ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by
        simpa [show (6 : ZMod p) = 2 * 3 by norm_num] using mul_ne_zero h2 h3))
        (pow_ne_zero _ h3)
    have hdEq : (3 : ZMod p) ^ d = (6 : ZMod p) ^ d := by
      apply mul_left_cancel₀ hcommon
      calc
        ((6 : ZMod p) ^ r₂ * 3 ^ s₁) * 3 ^ d =
            6 ^ r₂ * (3 ^ s₁ * 3 ^ d) := by ring
        _ = (6 ^ r₂ * 6 ^ d) * 3 ^ s₁ := hmod.symm
        _ = (6 ^ r₂ * 3 ^ s₁) * 6 ^ d := by ring
    have hpow : (2 : ZMod p) ^ d = 1 := by
      apply mul_right_cancel₀ (pow_ne_zero _ h3)
      simpa [show (6 : ZMod p) = 2 * 3 by norm_num, mul_pow,
        mul_assoc, mul_left_comm, mul_comm] using hdEq.symm
    exact ⟨d, hd, Or.inl rfl, orderOf_dvd_iff_pow_eq_one.mpr hpow⟩

/-- In an `R × S` interpolation grid, a collision of the transverse
coordinate inside one residue fiber makes the order of `2` strictly smaller
than `R`. -/
theorem orderOf_two_lt_of_yamadaGridValue_sum_collision
    {p R S : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {z₁ z₂ : Fin R × Fin S} (hne : z₁ ≠ z₂)
    (hsum : z₁.1.1 + z₁.2.1 = z₂.1.1 + z₂.2.1)
    (hvalue : yamadaGridValue p R S z₁ = yamadaGridValue p R S z₂) :
    orderOf (2 : ZMod p) < R := by
  obtain ⟨d, hd, hdiff, hdvd⟩ :=
    orderOf_two_dvd_coordinate_difference_of_grid_collision hp hp2 hp3
      (by
        intro h
        apply hne
        apply Prod.ext
        · exact Fin.ext (congrArg Prod.fst h)
        · exact Fin.ext (congrArg Prod.snd h))
      hsum (by simpa [yamadaGridValue] using hvalue)
  have hdR : d < R := by
    rcases hdiff with hdiff | hdiff
    · rw [hdiff]
      omega
    · rw [hdiff]
      omega
  exact lt_of_le_of_lt (Nat.le_of_dvd hd hdvd) hdR

/-- On a fixed residue fiber of the interpolation grid, either the transverse
coordinate `r+s` separates all points, or the multiplicative order of `2`
modulo `p` is already smaller than the width of the grid. -/
theorem yamadaGridValue_fiber_sum_injective_or_order_lt
    {p R S : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (c : ZMod p) :
    Function.Injective
        (fun z : {z : Fin R × Fin S // yamadaGridValue p R S z = c} =>
          z.1.1.1 + z.1.2.1) ∨
      orderOf (2 : ZMod p) < R := by
  let f : {z : Fin R × Fin S // yamadaGridValue p R S z = c} → ℕ :=
    fun z => z.1.1.1 + z.1.2.1
  by_cases hinj : Function.Injective f
  · exact Or.inl hinj
  · right
    obtain ⟨z₁, z₂, hsum, hne⟩ := Function.not_injective_iff.mp hinj
    apply orderOf_two_lt_of_yamadaGridValue_sum_collision hp hp2 hp3
    · intro hval
      apply hne
      exact Subtype.ext hval
    · exact hsum
    · exact z₁.property.trans z₂.property.symm

/-- The pigeonhole and degeneracy alternatives combined: a sufficiently
large grid has a fiber of cardinality at least `L`, and on that very fiber
the transverse coordinate is injective unless `2` has short order modulo
`p`. -/
theorem exists_large_yamadaGridValue_fiber_with_dichotomy
    {p R S L : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (harea : p * L ≤ R * S) :
    ∃ c : ZMod p,
      L ≤ (Finset.univ.filter fun z : Fin R × Fin S =>
        yamadaGridValue p R S z = c).card ∧
      (Function.Injective
          (fun z : {z : Fin R × Fin S // yamadaGridValue p R S z = c} =>
            z.1.1.1 + z.1.2.1) ∨
        orderOf (2 : ZMod p) < R) := by
  obtain ⟨c, hc⟩ := exists_large_yamadaGridValue_fiber hp harea
  exact ⟨c, hc,
    yamadaGridValue_fiber_sum_injective_or_order_lt hp hp2 hp3 c⟩

/-- Yamada's explicit estimate (with the harmless floor removed) implies the
uniform linear-logarithmic form used by the cyclotomic argument. -/
theorem fermat_quotient_linear_log_bound_of_yamada
    (hY : ∀ p : ℕ, p.Prime →
      (padicValNat p (mersenne (p - 1)) : ℝ) ≤
        283 * ((p - 1 : ℕ) : ℝ) * Real.log 3 * Real.log 6 /
            (Real.log (p : ℝ) * Real.log (p : ℝ)) + 4) :
    ∀ p : ℕ, p.Prime →
      (padicValNat p (mersenne (p - 1)) : ℝ) * Real.log (p : ℝ) ≤
        10000 * ((p : ℝ) / Real.log (p : ℝ) + Real.log (p : ℝ)) := by
  intro p hp
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hlog3pos : 0 ≤ Real.log (3 : ℝ) := (Real.log_pos (by norm_num)).le
  have hlog6pos : 0 ≤ Real.log (6 : ℝ) := (Real.log_pos (by norm_num)).le
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hlog6 : Real.log (6 : ℝ) ≤ 5 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)]
  have hlogs : Real.log (3 : ℝ) * Real.log (6 : ℝ) ≤ 10 :=
    (mul_le_mul hlog3 hlog6 hlog6pos (by norm_num)).trans_eq (by norm_num)
  have hpred : (((p - 1 : ℕ) : ℝ)) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hnum :
      283 * (((p - 1 : ℕ) : ℝ)) * Real.log 3 * Real.log 6 ≤
        10000 * (p : ℝ) := by
    have hnonneg : 0 ≤ 283 * (((p - 1 : ℕ) : ℝ)) := by positivity
    calc
      283 * (((p - 1 : ℕ) : ℝ)) * Real.log 3 * Real.log 6 =
          (283 * (((p - 1 : ℕ) : ℝ))) * (Real.log 3 * Real.log 6) := by ring
      _ ≤ (283 * (((p - 1 : ℕ) : ℝ))) * 10 :=
        mul_le_mul_of_nonneg_left hlogs hnonneg
      _ ≤ 10000 * (p : ℝ) := by nlinarith
  have hmain := mul_le_mul_of_nonneg_right (hY p hp) hlogp.le
  have hfirst :
      (283 * (((p - 1 : ℕ) : ℝ)) * Real.log 3 * Real.log 6 /
          (Real.log (p : ℝ) * Real.log (p : ℝ))) * Real.log (p : ℝ) ≤
        10000 * ((p : ℝ) / Real.log (p : ℝ)) := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    field_simp [hlogp.ne']
    nlinarith
  calc
    (padicValNat p (mersenne (p - 1)) : ℝ) * Real.log (p : ℝ) ≤
        (283 * (((p - 1 : ℕ) : ℝ)) * Real.log 3 * Real.log 6 /
          (Real.log (p : ℝ) * Real.log (p : ℝ)) + 4) *
            Real.log (p : ℝ) := hmain
    _ = (283 * (((p - 1 : ℕ) : ℝ)) * Real.log 3 * Real.log 6 /
          (Real.log (p : ℝ) * Real.log (p : ℝ))) * Real.log (p : ℝ) +
        4 * Real.log (p : ℝ) := by ring
    _ ≤ 10000 * ((p : ℝ) / Real.log (p : ℝ)) +
        10000 * Real.log (p : ℝ) := by
      exact add_le_add hfirst (mul_le_mul_of_nonneg_right (by norm_num) hlogp.le)
    _ = 10000 * ((p : ℝ) / Real.log (p : ℝ) + Real.log (p : ℝ)) := by ring

/-- For an odd prime, passing from the multiplicative order of `2` modulo
`p` to the exponent `p - 1` introduces no further `p`-adic valuation.  This
is the LTE step used in the degenerate alternative of Yamada's interpolation
argument. -/
theorem fermat_quotient_padicVal_eq_orderOf {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    padicValNat p (mersenne (p - 1)) =
      padicValNat p (mersenne (orderOf (2 : ZMod p))) := by
  letI : Fact p.Prime := ⟨hp⟩
  let d := orderOf (2 : ZMod p)
  have hdp : d ∣ p - 1 := orderOf_two_dvd_prime_sub_one hp hp2
  have hp1pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdp hp1pos
  have hqpos : 0 < (p - 1) / d :=
    Nat.div_pos (Nat.le_of_dvd hp1pos hdp) hdpos
  have hq_lt_p : (p - 1) / d < p := by
    exact lt_of_le_of_lt (Nat.div_le_self (p - 1) d)
      (Nat.sub_lt hp.pos zero_lt_one)
  have hpnotq : ¬p ∣ (p - 1) / d := by
    intro hpdq
    exact (not_le_of_gt hq_lt_p) (Nat.le_of_dvd hqpos hpdq)
  have hpd_mersenne : p ∣ mersenne d := by
    have hz : ((2 ^ d : ℕ) : ZMod p) = (1 : ZMod p) := by
      simpa [d] using pow_orderOf_eq_one (2 : ZMod p)
    have hz' : ((1 : ℕ) : ZMod p) = ((2 ^ d : ℕ) : ZMod p) := by
      simpa only [Nat.cast_one] using hz.symm
    have hmod : 1 ≡ 2 ^ d [MOD p] :=
      (ZMod.natCast_eq_natCast_iff 1 (2 ^ d) p).mp hz'
    exact (Nat.modEq_iff_dvd' (one_le_pow₀ (by norm_num))).mp hmod
  have hpnotpow : ¬p ∣ 2 ^ d := by
    intro hpow
    apply hp2
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow hpow)
  have hlte := padicValNat.pow_sub_pow (hp.odd_of_ne_two hp2)
    (x := 2 ^ d) (y := 1) (one_lt_pow₀ one_lt_two hdpos.ne')
    (by simpa [mersenne] using hpd_mersenne) hpnotpow hqpos.ne'
  have hexp : (2 ^ d) ^ ((p - 1) / d) = 2 ^ (p - 1) := by
    rw [← pow_mul, Nat.mul_div_cancel' hdp]
  rw [one_pow, hexp, padicValNat.eq_zero_of_not_dvd hpnotq, add_zero] at hlte
  simpa [mersenne] using hlte

/-- The elementary size estimate for a Fermat quotient.  It is enough for
Yamada's finite small-prime range. -/
theorem fermat_quotient_trivial_log_bound {p : ℕ} (hp : p.Prime) :
    (padicValNat p (mersenne (p - 1)) : ℝ) * Real.log (p : ℝ) ≤
      (((p - 1 : ℕ) : ℝ)) * Real.log 2 := by
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hmpos : 0 < mersenne (p - 1) := mersenne_pos hp1
  have hval := padicValNat_mul_log_le_log hmpos hp
  have hmle : mersenne (p - 1) ≤ 2 ^ (p - 1) := Nat.sub_le _ _
  have hmR : (0 : ℝ) < mersenne (p - 1) := by exact_mod_cast hmpos
  have hmleR : (mersenne (p - 1) : ℝ) ≤ (2 : ℝ) ^ (p - 1) := by
    exact_mod_cast hmle
  have hlog := Real.log_le_log hmR hmleR
  rw [Real.log_pow] at hlog
  exact hval.trans hlog

/-- If the order of `2` modulo `p` is short, the elementary size of the
corresponding Mersenne number already gives a strong Fermat-quotient bound. -/
theorem fermat_quotient_orderOf_log_bound {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    (padicValNat p (mersenne (p - 1)) : ℝ) * Real.log (p : ℝ) ≤
      (orderOf (2 : ZMod p) : ℝ) * Real.log 2 := by
  rw [fermat_quotient_padicVal_eq_orderOf hp hp2]
  let d := orderOf (2 : ZMod p)
  have hdp : d ∣ p - 1 := orderOf_two_dvd_prime_sub_one hp hp2
  have hdpos : 0 < d :=
    Nat.pos_of_dvd_of_pos hdp (Nat.sub_pos_of_lt hp.one_lt)
  have hmpos : 0 < mersenne d := mersenne_pos hdpos
  have hval := padicValNat_mul_log_le_log hmpos hp
  have hmle : mersenne d ≤ 2 ^ d := Nat.sub_le _ _
  have hmR : (0 : ℝ) < mersenne d := by exact_mod_cast hmpos
  have hmleR : (mersenne d : ℝ) ≤ (2 : ℝ) ^ d := by exact_mod_cast hmle
  have hlog := Real.log_le_log hmR hmleR
  rw [Real.log_pow] at hlog
  exact hval.trans hlog

/-- Yamada's numerical inequality in the range `p ≤ 2^283`, proved only
from the trivial size estimate. -/
theorem yamada_fermat_quotient_bound_small {p : ℕ} (hp : p.Prime)
    (hpSmall : p ≤ 2 ^ 283) :
    (padicValNat p (mersenne (p - 1)) : ℝ) ≤
      283 * (((p - 1 : ℕ) : ℝ)) * Real.log 3 * Real.log 6 /
          (Real.log (p : ℝ) * Real.log (p : ℝ)) + 4 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2_3 : Real.log (2 : ℝ) ≤ Real.log (3 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog2_6 : Real.log (2 : ℝ) ≤ Real.log (6 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hpSmallR : (p : ℝ) ≤ (2 : ℝ) ^ 283 := by exact_mod_cast hpSmall
  have hlogp_le : Real.log (p : ℝ) ≤ 283 * Real.log 2 := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < p) hpSmallR
    simpa [Real.log_pow] using h
  have hprod : Real.log 2 * Real.log (p : ℝ) ≤
      283 * Real.log 3 * Real.log 6 := by
    calc
      Real.log 2 * Real.log (p : ℝ) ≤ Real.log 2 * (283 * Real.log 2) :=
        mul_le_mul_of_nonneg_left hlogp_le hlog2.le
      _ = 283 * (Real.log 2 * Real.log 2) := by ring
      _ ≤ 283 * (Real.log 3 * Real.log 6) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul hlog2_3 hlog2_6 hlog2.le
          (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le
      _ = 283 * Real.log 3 * Real.log 6 := by ring
  have htrivial := fermat_quotient_trivial_log_bound hp
  have hpred : 0 ≤ (((p - 1 : ℕ) : ℝ)) := by positivity
  have htargetMul :
      (((p - 1 : ℕ) : ℝ)) * Real.log 2 ≤
        (283 * (((p - 1 : ℕ) : ℝ)) * Real.log 3 * Real.log 6 /
          (Real.log (p : ℝ) * Real.log (p : ℝ))) * Real.log (p : ℝ) := by
    field_simp [hlogp.ne']
    nlinarith [mul_le_mul_of_nonneg_left hprod hpred]
  have hmain : (padicValNat p (mersenne (p - 1)) : ℝ) ≤
      283 * (((p - 1 : ℕ) : ℝ)) * Real.log 3 * Real.log 6 /
        (Real.log (p : ℝ) * Real.log (p : ℝ)) := by
    rw [← mul_le_mul_iff_of_pos_right hlogp]
    exact htrivial.trans htargetMul
  linarith

theorem coeff_prod_of_natDegree_le_varying
    {ι R : Type*} [CommSemiring R] [DecidableEq ι]
    (s : Finset ι) (f : ι → R[X]) (d : ι → ℕ)
    (hdeg : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) =
      ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha, prod_insert ha]
      rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hdeg a (mem_insert_self _ _))]
      · simpa using congrArg (fun z => (f a).coeff (d a) * z)
          (ih fun i hi => hdeg i (mem_insert_of_mem hi))
      · exact (Polynomial.natDegree_prod_le _ _).trans (by
          apply Finset.sum_le_sum
          intro i hi
          exact hdeg i (mem_insert_of_mem hi))

theorem coeff_det_of_column_natDegree_le
    {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R[X]) (d : n → ℕ)
    (hdeg : ∀ i j, (A i j).natDegree ≤ d j) :
    (Matrix.det A).coeff (∑ j, d j) =
      Matrix.det (fun i j => (A i j).coeff (d j)) := by
  classical
  let B : Matrix n n R := fun i j => (A i j).coeff (d j)
  change (Matrix.det A).coeff (∑ j, d j) = Matrix.det B
  rw [Matrix.det_apply, Polynomial.finsetSum_coeff, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Polynomial.coeff_smul]
  congr 1
  rw [coeff_prod_of_natDegree_le_varying]
  intro j hj
  exact hdeg (σ j) j

theorem geometric_shift_det_ne_zero {n : ℕ}
    (ell : Fin n → ℕ) (hell : Injective ell)
    (P : Fin n → ℚ[X]) (hP : ∀ j, P j ≠ 0)
    (q d : ℚ) (hq : 0 < q) (hq1 : q ≠ 1) :
    Matrix.det (fun i j : Fin n =>
      Polynomial.C (q ^ (i.1 * ell j)) *
        (P j).comp (Polynomial.X + Polynomial.C ((i.1 : ℚ) * d))) ≠ 0 := by
  classical
  let A : Matrix (Fin n) (Fin n) ℚ[X] := fun i j =>
    Polynomial.C (q ^ (i.1 * ell j)) *
      (P j).comp (Polynomial.X + Polynomial.C ((i.1 : ℚ) * d))
  let deg : Fin n → ℕ := fun j => (P j).natDegree
  have hshiftDegree (i j : Fin n) :
      ((P j).comp (Polynomial.X + Polynomial.C ((i.1 : ℚ) * d))).natDegree =
        deg j := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
  have hAdeg : ∀ i j, (A i j).natDegree ≤ deg j := by
    intro i j
    rw [show A i j = Polynomial.C (q ^ (i.1 * ell j)) *
      (P j).comp (Polynomial.X + Polynomial.C ((i.1 : ℚ) * d)) by rfl]
    rw [Polynomial.natDegree_C_mul (pow_ne_zero _ hq.ne')]
    exact (hshiftDegree i j).le
  have hlead (i j : Fin n) :
      (A i j).coeff (deg j) = q ^ (i.1 * ell j) * (P j).leadingCoeff := by
    rw [show A i j = Polynomial.C (q ^ (i.1 * ell j)) *
      (P j).comp (Polynomial.X + Polynomial.C ((i.1 : ℚ) * d)) by rfl,
      Polynomial.coeff_C_mul]
    rw [← hshiftDegree i j, Polynomial.coeff_natDegree]
    have hlin :
        (Polynomial.X + Polynomial.C ((i.1 : ℚ) * d)).natDegree ≠ 0 := by
      rw [Polynomial.natDegree_X_add_C]
      norm_num
    rw [Polynomial.leadingCoeff_comp hlin]
    rw [(Polynomial.monic_X_add_C ((i.1 : ℚ) * d)).leadingCoeff]
    simp
  let nodes : Fin n → ℚ := fun j => q ^ ell j
  have hnodes : Injective nodes := by
    intro i j hij
    apply hell
    exact pow_right_injective₀ hq hq1 hij
  have htop : Matrix.det (fun i j : Fin n =>
      (A i j).coeff (deg j)) ≠ 0 := by
    have hmatrix : (fun i j : Fin n => (A i j).coeff (deg j)) =
        (Matrix.vandermonde nodes).transpose *
          Matrix.diagonal (fun j => (P j).leadingCoeff) := by
      ext i j
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single j]
      · simp only [Matrix.transpose_apply, Matrix.vandermonde_apply,
          Matrix.diagonal_apply, if_pos, mul_one]
        rw [hlead]
        dsimp only [nodes]
        rw [Nat.mul_comm i.1 (ell j)]
        rw [pow_mul]
      · intro k hk hkj
        simp [hkj]
      · simp
    rw [hmatrix, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    exact mul_ne_zero
      (Matrix.det_vandermonde_ne_zero_iff.mpr hnodes)
      (Finset.prod_ne_zero_iff.mpr fun j _ => Polynomial.leadingCoeff_ne_zero.mpr (hP j))
  intro hdet
  have hcoeff := coeff_det_of_column_natDegree_le A deg hAdeg
  rw [hdet, Polynomial.coeff_zero] at hcoeff
  exact htop hcoeff.symm

theorem geometric_shift_common_zeros_card_le
    {n m : ℕ} (hn : 0 < n)
    (ell : Fin n → ℕ) (hell : Injective ell)
    (P : Fin n → ℚ[X]) (hP : ∀ j, P j ≠ 0)
    (q d : ℚ) (hq : 0 < q) (hq1 : q ≠ 1)
    (x y : Fin m → ℚ) (hx : Injective x) (hy : ∀ j, y j ≠ 0)
    (hzero : ∀ i : Fin n, ∀ b : Fin m,
      ∑ j : Fin n, (P j).eval (x b + (i.1 : ℚ) * d) *
        (q ^ i.1 * y b) ^ (ell j) = 0) :
    m ≤ ∑ j, (P j).natDegree := by
  classical
  let A : Matrix (Fin n) (Fin n) ℚ[X] := fun i j =>
    Polynomial.C (q ^ (i.1 * ell j)) *
      (P j).comp (Polynomial.X + Polynomial.C ((i.1 : ℚ) * d))
  let D : ℚ[X] := Matrix.det A
  have hD : D ≠ 0 := by
    exact geometric_shift_det_ne_zero ell hell P hP q d hq hq1
  have hDdegree : D.natDegree ≤ ∑ j, (P j).natDegree := by
    dsimp only [D]
    rw [Matrix.det_apply]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro σ hσ
    calc
      (Equiv.Perm.sign σ • ∏ j, A (σ j) j).natDegree ≤
          (∏ j, A (σ j) j).natDegree := Polynomial.natDegree_smul_le _ _
      _ ≤ ∑ j, (A (σ j) j).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ j, (P j).natDegree := by
        apply Finset.sum_le_sum
        intro j hj
        rw [show A (σ j) j = Polynomial.C (q ^ ((σ j).1 * ell j)) *
          (P j).comp (Polynomial.X + Polynomial.C (((σ j).1 : ℚ) * d)) by rfl]
        rw [Polynomial.natDegree_C_mul (pow_ne_zero _ hq.ne')]
        rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
  have hxroot : ∀ b, x b ∈ D.roots := by
    intro b
    have hmul :
        Matrix.mulVec (A.map (Polynomial.evalRingHom (x b)))
          (fun j => (y b) ^ (ell j)) = 0 := by
      funext i
      change (∑ j, (A i j).eval (x b) * (y b) ^ ell j) = 0
      simp only [A, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        Polynomial.eval_add, Polynomial.eval_X]
      simpa [mul_pow, pow_mul, mul_assoc, mul_left_comm, mul_comm] using hzero i b
    have hvne : (fun j : Fin n => (y b) ^ (ell j)) ≠ 0 := by
      intro hv
      have hz := congrFun hv (⟨0, hn⟩ : Fin n)
      exact (pow_ne_zero _ (hy b)) (by simpa using hz)
    have hdet : Matrix.det (A.map (Polynomial.evalRingHom (x b))) = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hvne, hmul⟩
    have heval : D.eval (x b) = 0 := by
      change (Polynomial.evalRingHom (x b)) (Matrix.det A) = 0
      rw [(Polynomial.evalRingHom (x b)).map_det]
      exact hdet
    exact (Polynomial.mem_roots hD).2 heval
  let xs : Finset ℚ := univ.image x
  have hcardxs : xs.card = m := by
    simp [xs, Finset.card_image_of_injective _ hx]
  have hxssub : xs ⊆ D.roots.toFinset := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨b, hb, rfl⟩ := hz
    exact Multiset.mem_toFinset.mpr (hxroot b)
  calc
    m = xs.card := hcardxs.symm
    _ ≤ D.roots.toFinset.card := card_le_card hxssub
    _ ≤ D.roots.card := Multiset.toFinset_card_le _
    _ ≤ D.natDegree := Polynomial.card_roots' D
    _ ≤ ∑ j, (P j).natDegree := hDdegree

theorem polynomial_geometric_translate_zero
    {K L m : ℕ}
    (P : Fin L → ℚ[X]) (hPdeg : ∀ j, (P j).natDegree < K)
    (hPne : ∃ j, P j ≠ 0)
    (q d : ℚ) (hq : 0 < q) (hq1 : q ≠ 1)
    (x y : Fin m → ℚ) (hx : Injective x) (hy : ∀ j, y j ≠ 0)
    (hm : (K - 1) * L < m)
    (hzero : ∀ i : Fin L, ∀ b : Fin m,
      ∑ j : Fin L, (P j).eval (x b + (i.1 : ℚ) * d) *
        (q ^ i.1 * y b) ^ j.1 = 0) : False := by
  classical
  let S : Finset (Fin L) := univ.filter fun j => P j ≠ 0
  have hSne : S.Nonempty := by
    obtain ⟨j, hj⟩ := hPne
    exact ⟨j, by simp [S, hj]⟩
  have hn : 0 < S.card := card_pos.mpr hSne
  let e : Fin S.card ≃ {j : Fin L // j ∈ S} := S.equivFin.symm
  let ell : Fin S.card → ℕ := fun j => (e j).1.1
  let P' : Fin S.card → ℚ[X] := fun j => P (e j).1
  have hell : Injective ell := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact Fin.ext hij
  have hP' : ∀ j, P' j ≠ 0 := by
    intro j
    have hj := (e j).2
    simpa [S, P'] using (mem_filter.mp hj).2
  have hcardSL : S.card ≤ L := by simpa using S.card_le_univ
  have hzero' : ∀ i : Fin S.card, ∀ b : Fin m,
      ∑ j : Fin S.card, (P' j).eval (x b + (i.1 : ℚ) * d) *
        (q ^ i.1 * y b) ^ (ell j) = 0 := by
    intro i b
    let iL : Fin L := ⟨i.1, lt_of_lt_of_le i.2 hcardSL⟩
    have hz := hzero iL b
    have hrestrict :
        (∑ j : Fin L, (P j).eval (x b + (i.1 : ℚ) * d) *
          (q ^ i.1 * y b) ^ j.1) =
        ∑ j ∈ S, (P j).eval (x b + (i.1 : ℚ) * d) *
          (q ^ i.1 * y b) ^ j.1 := by
      symm
      apply sum_subset (subset_univ S)
      intro j hjU hjS
      have hPj : P j = 0 := by
        simpa [S] using hjS
      simp [hPj]
    rw [hrestrict] at hz
    calc
      (∑ j : Fin S.card, (P' j).eval (x b + (i.1 : ℚ) * d) *
          (q ^ i.1 * y b) ^ ell j) =
          ∑ j : {j : Fin L // j ∈ S},
            (P j.1).eval (x b + (i.1 : ℚ) * d) *
              (q ^ i.1 * y b) ^ j.1.1 := by
            exact Equiv.sum_comp e (fun j =>
              (P j.1).eval (x b + (i.1 : ℚ) * d) *
                (q ^ i.1 * y b) ^ j.1.1)
      _ = ∑ j ∈ S, (P j).eval (x b + (i.1 : ℚ) * d) *
          (q ^ i.1 * y b) ^ j.1 := by
            exact Finset.sum_attach S (fun j =>
              (P j).eval (x b + (i.1 : ℚ) * d) *
                (q ^ i.1 * y b) ^ j.1)
      _ = 0 := hz
  have hbound := geometric_shift_common_zeros_card_le
    hn ell hell P' hP' q d hq hq1 x y hx hy hzero'
  have hsumdeg : (∑ j, (P' j).natDegree) ≤ S.card * (K - 1) := by
    calc
      (∑ j, (P' j).natDegree) ≤ ∑ _j : Fin S.card, (K - 1) := by
        apply Finset.sum_le_sum
        intro j hj
        exact Nat.le_sub_one_of_lt (hPdeg (e j).1)
      _ = S.card * (K - 1) := by simp [Fintype.card_fin]
  have hSL : S.card * (K - 1) ≤ L * (K - 1) :=
    Nat.mul_le_mul_right (K - 1) hcardSL
  have hSL' : S.card * (K - 1) ≤ (K - 1) * L := by
    simpa [Nat.mul_comm] using hSL
  omega



theorem exists_det_submatrix_ne_zero
    {N : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin N) C ℚ) (hA : LinearIndependent ℚ A.row) :
    ∃ c : Fin N → C, (A.submatrix id c).det ≠ 0 := by
  classical
  have hrank : A.rank = N := by
    simpa using hA.rank_matrix
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range A.col)
  rw [← A.rank_eq_finrank_span_cols, hrank] at hex
  obtain ⟨f, hfmem, _hfspan, hfind⟩ := hex
  choose c hc using hfmem
  refine ⟨c, ?_⟩
  have hcol : (A.submatrix id c).col = f := by
    funext j
    exact funext fun i => congrFun (hc j) i
  have hli : LinearIndependent ℚ (A.submatrix id c).col := by
    rw [hcol]
    exact hfind
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hli)).ne_zero



theorem linearIndependent_choose_geometric_rows
    {K L m : ℕ}
    (q d : ℚ) (hq : 0 < q) (hq1 : q ≠ 1)
    (x y : Fin m → ℚ) (hx : Injective x) (hy : ∀ j, y j ≠ 0)
    (hm : (K - 1) * L < m) :
    LinearIndependent ℚ (fun kl : Fin K × Fin L => fun ib : Fin L × Fin m =>
      (chooseMulPoly (S := ℚ) 1 kl.1.1).eval (x ib.2 + (ib.1.1 : ℚ) * d) *
        (q ^ ib.1.1 * y ib.2) ^ kl.2.1) := by
  classical
  by_cases hKzero : K = 0
  · subst K
    rw [Fintype.linearIndependent_iff]
    intro g hg kl
    exact Fin.elim0 kl.1
  have hKpos : 0 < K := Nat.pos_of_ne_zero hKzero
  rw [Fintype.linearIndependent_iff]
  intro g hg kl
  let P : Fin L → ℚ[X] := fun l =>
    ∑ k : Fin K, Polynomial.C (g (k, l)) * chooseMulPoly (S := ℚ) 1 k.1
  have hPdeg : ∀ l, (P l).natDegree < K := by
    intro l
    dsimp only [P]
    refine lt_of_le_of_lt
      (Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ)
        (fun k : Fin K =>
          Polynomial.C (g (k, l)) * chooseMulPoly (S := ℚ) 1 k.1) ?_)
      (Nat.sub_lt hKpos (by norm_num : 0 < 1))
    intro k hk
    exact (Polynomial.natDegree_mul_le.trans (by
      simpa using chooseMulPoly_natDegree_le (S := ℚ) 1 k.1)).trans
        (Nat.le_sub_one_of_lt k.2)
  have hzero : ∀ i : Fin L, ∀ b : Fin m,
      ∑ l : Fin L, (P l).eval (x b + (i.1 : ℚ) * d) *
        (q ^ i.1 * y b) ^ l.1 = 0 := by
    intro i b
    have hz := congrFun hg (i, b)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz
    rw [Fintype.sum_prod_type] at hz
    rw [Finset.sum_comm] at hz
    simpa [P, Polynomial.eval_finset_sum, Polynomial.eval_mul, mul_assoc,
      Finset.sum_mul] using hz
  have hPzero : ∀ l, P l = 0 := by
    by_contra hn
    push_neg at hn
    exact polynomial_geometric_translate_zero P hPdeg hn q d hq hq1 x y hx hy hm hzero
  have hcoeff : ∀ l : Fin L, ∀ n : Fin K, g (n, l) = 0 := by
    intro l n
    have haux : ∀ a : ℕ, ∀ haK : a < K, g (⟨a, haK⟩, l) = 0 := by
      intro a
      induction a using Nat.strong_induction_on with
      | h a ih =>
        intro haK
        have heval := congrArg (fun Q : ℚ[X] => Q.eval (a : ℚ)) (hPzero l)
        have hsum :
            (∑ k : Fin K, g (k, l) * (Nat.choose a k.1 : ℚ)) = 0 := by
          simpa [P, Polynomial.eval_finset_sum, Polynomial.eval_mul,
            chooseMulPoly_eval, Ring.choose_natCast] using heval
        have hsingle :
            (∑ k : Fin K, g (k, l) * (Nat.choose a k.1 : ℚ)) =
                g (⟨a, haK⟩, l) := by
          rw [Finset.sum_eq_single ⟨a, haK⟩]
          · simp
          · intro k hk hka
            rcases lt_trichotomy k.1 a with hlt | heq | hgt
            · rw [ih k.1 hlt k.2]
              simp
            · exact (hka (Fin.ext heq)).elim
            · rw [Nat.choose_eq_zero_of_lt hgt]
              simp
          · simp
        rw [hsingle] at hsum
        exact hsum
    exact haux n.1 n.2
  exact hcoeff kl.2 kl.1



theorem exists_yamada_seed
    {p H : ℕ} (hp : p.Prime) (hcard : p < H * H) :
    ∃ a₁ a₂ : Fin H × Fin H, a₁ ≠ a₂ ∧
      yamadaGridValue p H H a₁ = yamadaGridValue p H H a₂ := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hlt : Fintype.card (ZMod p) < Fintype.card (Fin H × Fin H) := by
    simpa [ZMod.card, Fintype.card_prod, Fintype.card_fin] using hcard
  have hninj := Fintype.not_injective_of_card_lt (yamadaGridValue p H H) hlt
  obtain ⟨a₁, a₂, heq, hne⟩ := Function.not_injective_iff.mp hninj
  exact ⟨a₁, a₂, hne, heq⟩

theorem yamada_seed_progression
    {H : ℕ} {a₁ a₂ : Fin H × Fin H} (hne : a₁ ≠ a₂) :
    let Y₁ := 6 ^ a₁.1.1 * 3 ^ a₁.2.1
    let Y₂ := 6 ^ a₂.1.1 * 3 ^ a₂.2.1
    let q : ℚ := (Y₁ : ℚ) / (Y₂ : ℚ)
    let d : ℚ := ((a₁.1.1 + a₁.2.1 : ℕ) : ℚ) -
      ((a₂.1.1 + a₂.2.1 : ℕ) : ℚ)
    let r : Fin 4 → ℕ := fun i => i.1 * a₁.1.1 + (3 - i.1) * a₂.1.1
    let s : Fin 4 → ℕ := fun i => i.1 * a₁.2.1 + (3 - i.1) * a₂.2.1
    0 < q ∧ q ≠ 1 ∧
      (∀ i, ((r i + s i : ℕ) : ℚ) =
        (3 * (a₂.1.1 + a₂.2.1 : ℕ) : ℕ) + (i.1 : ℚ) * d) ∧
      (∀ i, ((6 ^ r i * 3 ^ s i : ℕ) : ℚ) = q ^ i.1 * (Y₂ : ℚ) ^ 3) := by
  dsimp only
  let Y₁ := 6 ^ a₁.1.1 * 3 ^ a₁.2.1
  let Y₂ := 6 ^ a₂.1.1 * 3 ^ a₂.2.1
  have hY₁ : 0 < Y₁ := by positivity
  have hY₂ : 0 < Y₂ := by positivity
  have hqpos : (0 : ℚ) < (Y₁ : ℚ) / (Y₂ : ℚ) := by positivity
  have hqne : ((Y₁ : ℚ) / (Y₂ : ℚ)) ≠ 1 := by
    intro hq
    have hcast : (Y₁ : ℚ) = (Y₂ : ℚ) := (div_eq_one_iff_eq (by positivity)).mp hq
    have hnat : Y₁ = Y₂ := by exact_mod_cast hcast
    have hpairs : (a₁.1.1, a₁.2.1) = (a₂.1.1, a₂.2.1) :=
      six_pow_mul_three_pow_injective hnat
    apply hne
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.fst hpairs
    · apply Fin.ext
      exact congrArg Prod.snd hpairs
  refine ⟨by simpa [Y₁, Y₂] using hqpos,
    by simpa [Y₁, Y₂] using hqne, ?_, ?_⟩
  · intro i
    have hi : i.1 ≤ 3 := by omega
    push_cast
    rw [Nat.cast_sub hi]
    ring
  · intro i
    have hi : i.1 ≤ 3 := by omega
    have hmonoNat :
        6 ^ (i.1 * a₁.1.1 + (3 - i.1) * a₂.1.1) *
            3 ^ (i.1 * a₁.2.1 + (3 - i.1) * a₂.2.1) =
          Y₁ ^ i.1 * Y₂ ^ (3 - i.1) := by
      simp only [Y₁, Y₂, pow_add, ← pow_mul]
      ring
    rw [hmonoNat]
    have hrat : ((Y₁ ^ i.1 * Y₂ ^ (3 - i.1) : ℕ) : ℚ) =
        ((Y₁ : ℚ) / (Y₂ : ℚ)) ^ i.1 * (Y₂ : ℚ) ^ 3 := by
      push_cast
      rw [div_pow]
      have hpow : (Y₂ : ℚ) ^ (3 - i.1) * (Y₂ : ℚ) ^ i.1 =
          (Y₂ : ℚ) ^ 3 := pow_sub_mul_pow _ hi
      field_simp
      nlinarith
    simpa [Y₁, Y₂] using hrat

theorem exists_nonsingular_yamada_interpolation
    {p H R K : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hK : 0 < K) (hseed : p < H * H) (harea : p * (K * 4) ≤ R * R) :
    orderOf (2 : ZMod p) < R ∨
      ∃ r s : Fin (K * 4) → ℕ,
        (∀ j, r j < R + 3 * H) ∧ (∀ j, s j < R + 3 * H) ∧
        (∀ i j,
          (6 : ZMod p) ^ r i * (3 : ZMod p) ^ s i =
            (6 : ZMod p) ^ r j * (3 : ZMod p) ^ s j) ∧
        Matrix.det (fun i j : Fin (K * 4) =>
          (Nat.choose (r j + s j) ((finProdFinEquiv.symm i).1.1) : ℚ) *
            (6 : ℚ) ^ ((finProdFinEquiv.symm i).2.1 * r j) *
            (3 : ℚ) ^ ((finProdFinEquiv.symm i).2.1 * s j)) ≠ 0 := by
  classical
  obtain ⟨c, hc, htrans | horder⟩ :=
    exists_large_yamadaGridValue_fiber_with_dichotomy hp hp2 hp3 harea
  · right
    let F := {z : Fin R × Fin R // yamadaGridValue p R R z = c}
    have hcF : K * 4 ≤ Fintype.card F := by
      simpa [F, Fintype.card_subtype] using hc
    let eB : Fin (K * 4) ↪ F :=
      (Function.Embedding.nonempty_of_card_le (by simpa using hcF)).some
    let B : Fin (K * 4) → Fin R × Fin R := fun j => (eB j).1
    have hBx : Injective (fun j => (B j).1.1 + (B j).2.1) := by
      exact htrans.comp eB.injective
    obtain ⟨a₁, a₂, ha12, hseedval⟩ := exists_yamada_seed hp hseed
    let Y₁ := 6 ^ a₁.1.1 * 3 ^ a₁.2.1
    let Y₂ := 6 ^ a₂.1.1 * 3 ^ a₂.2.1
    let q : ℚ := (Y₁ : ℚ) / (Y₂ : ℚ)
    let d : ℚ := ((a₁.1.1 + a₁.2.1 : ℕ) : ℚ) -
      ((a₂.1.1 + a₂.2.1 : ℕ) : ℚ)
    let ar : Fin 4 → ℕ := fun i =>
      i.1 * a₁.1.1 + (3 - i.1) * a₂.1.1
    let as : Fin 4 → ℕ := fun i =>
      i.1 * a₁.2.1 + (3 - i.1) * a₂.2.1
    obtain ⟨hq, hq1, hxA, hyA⟩ := yamada_seed_progression ha12
    have hq' : 0 < q := by simpa [q, Y₁, Y₂] using hq
    have hq1' : q ≠ 1 := by simpa [q, Y₁, Y₂] using hq1
    have hxA' : ∀ i, ((ar i + as i : ℕ) : ℚ) =
        (3 * (a₂.1.1 + a₂.2.1 : ℕ) : ℕ) + (i.1 : ℚ) * d := by
      simpa [ar, as, d] using hxA
    have hyA' : ∀ i, ((6 ^ ar i * 3 ^ as i : ℕ) : ℚ) =
        q ^ i.1 * (Y₂ : ℚ) ^ 3 := by
      simpa [ar, as, q, Y₁, Y₂] using hyA
    let x : Fin (K * 4) → ℚ := fun b =>
      ((B b).1.1 + (B b).2.1 : ℕ) +
        (3 * (a₂.1.1 + a₂.2.1 : ℕ) : ℕ)
    let y : Fin (K * 4) → ℚ := fun b =>
      (Y₂ : ℚ) ^ 3 * ((6 ^ (B b).1.1 * 3 ^ (B b).2.1 : ℕ) : ℚ)
    have hx : Injective x := by
      intro b₁ b₂ hb
      apply hBx
      have hcast :
          (((B b₁).1.1 + (B b₁).2.1 : ℕ) : ℚ) =
            (((B b₂).1.1 + (B b₂).2.1 : ℕ) : ℚ) := by
        dsimp only [x] at hb
        linarith
      exact_mod_cast hcast
    have hy : ∀ b, y b ≠ 0 := by
      intro b
      positivity
    have hm : (K - 1) * 4 < K * 4 := by omega
    have hrows := linearIndependent_choose_geometric_rows q d hq' hq1' x y hx hy hm
    let erow : Fin (K * 4) ≃ Fin K × Fin 4 := finProdFinEquiv.symm
    let A : Matrix (Fin (K * 4)) (Fin 4 × Fin (K * 4)) ℚ := fun row col =>
      (chooseMulPoly (S := ℚ) 1 (erow row).1.1).eval
          (x col.2 + (col.1.1 : ℚ) * d) *
        (q ^ col.1.1 * y col.2) ^ (erow row).2.1
    have hA : LinearIndependent ℚ A.row := by
      change LinearIndependent ℚ (fun row => A row)
      dsimp only [A, erow]
      exact hrows.comp finProdFinEquiv.symm finProdFinEquiv.symm.injective
    obtain ⟨sel, hsel⟩ := exists_det_submatrix_ne_zero A hA
    let r : Fin (K * 4) → ℕ := fun j => ar (sel j).1 + (B (sel j).2).1.1
    let s : Fin (K * 4) → ℕ := fun j => as (sel j).1 + (B (sel j).2).2.1
    have hr : ∀ j, r j < R + 3 * H := by
      intro j
      have hi : (sel j).1.1 ≤ 3 := by omega
      have ha₁r : a₁.1.1 < H := a₁.1.2
      have ha₂r : a₂.1.1 < H := a₂.1.2
      have hBr : (B (sel j).2).1.1 < R := (B (sel j).2).1.2
      dsimp [r, ar]
      nlinarith [Nat.sub_add_cancel hi]
    have hs : ∀ j, s j < R + 3 * H := by
      intro j
      have hi : (sel j).1.1 ≤ 3 := by omega
      have ha₁s : a₁.2.1 < H := a₁.2.2
      have ha₂s : a₂.2.1 < H := a₂.2.2
      have hBs : (B (sel j).2).2.1 < R := (B (sel j).2).2.2
      dsimp [s, as]
      nlinarith [Nat.sub_add_cancel hi]
    have hfiber : ∀ i j,
        (6 : ZMod p) ^ r i * (3 : ZMod p) ^ s i =
          (6 : ZMod p) ^ r j * (3 : ZMod p) ^ s j := by
      intro i j
      have hAi : yamadaGridValue p H H a₁ = yamadaGridValue p H H a₂ := hseedval
      have hAconst : ∀ t : Fin 4,
          (6 : ZMod p) ^ ar t * (3 : ZMod p) ^ as t =
            ((6 : ZMod p) ^ a₂.1.1 * (3 : ZMod p) ^ a₂.2.1) ^ 3 := by
        intro t
        have ht : t.1 ≤ 3 := by omega
        have hmono : (6 : ZMod p) ^ ar t * (3 : ZMod p) ^ as t =
            ((6 : ZMod p) ^ a₁.1.1 * (3 : ZMod p) ^ a₁.2.1) ^ t.1 *
              ((6 : ZMod p) ^ a₂.1.1 * (3 : ZMod p) ^ a₂.2.1) ^ (3 - t.1) := by
          simp only [ar, as, pow_add, ← pow_mul]
          ring
        rw [hmono]
        have hval : (6 : ZMod p) ^ a₁.1.1 * (3 : ZMod p) ^ a₁.2.1 =
            (6 : ZMod p) ^ a₂.1.1 * (3 : ZMod p) ^ a₂.2.1 := by
          simpa [yamadaGridValue] using hAi
        rw [hval, ← pow_add, Nat.add_sub_of_le ht]
      have hBi : yamadaGridValue p R R (B (sel i).2) = c := (eB (sel i).2).2
      have hBj : yamadaGridValue p R R (B (sel j).2) = c := (eB (sel j).2).2
      simp only [r, s, pow_add]
      rw [mul_mul_mul_comm, hAconst, show
          (6 : ZMod p) ^ (B (sel i).2).1.1 * 3 ^ (B (sel i).2).2.1 = c by
            simpa [yamadaGridValue] using hBi,
        mul_mul_mul_comm, hAconst, show
          (6 : ZMod p) ^ (B (sel j).2).1.1 * 3 ^ (B (sel j).2).2.1 = c by
            simpa [yamadaGridValue] using hBj]
    refine ⟨r, s, hr, hs, hfiber, ?_⟩
    have hmatrix : A.submatrix id sel = fun i j : Fin (K * 4) =>
        (Nat.choose (r j + s j) ((finProdFinEquiv.symm i).1.1) : ℚ) *
          (6 : ℚ) ^ ((finProdFinEquiv.symm i).2.1 * r j) *
          (3 : ℚ) ^ ((finProdFinEquiv.symm i).2.1 * s j) := by
      ext i j
      let t := (sel j).1
      let b := (sel j).2
      have hxcol : x b + (t.1 : ℚ) * d = ((r j + s j : ℕ) : ℚ) := by
        rw [show r j + s j = (ar t + as t) + ((B b).1.1 + (B b).2.1) by
          simp [r, s, t, b]; omega]
        rw [Nat.cast_add]
        rw [hxA' t]
        simp only [x, t, b, Nat.cast_add]
        ring
      have hycol : q ^ t.1 * y b =
          ((6 ^ r j * 3 ^ s j : ℕ) : ℚ) := by
        calc
          q ^ t.1 * y b =
              (q ^ t.1 * (Y₂ : ℚ) ^ 3) *
                ((6 ^ (B b).1.1 * 3 ^ (B b).2.1 : ℕ) : ℚ) := by
            simp only [y]
            ring
          _ = ((6 ^ ar t * 3 ^ as t : ℕ) : ℚ) *
                ((6 ^ (B b).1.1 * 3 ^ (B b).2.1 : ℕ) : ℚ) := by
            rw [← hyA' t]
          _ = ((6 ^ r j * 3 ^ s j : ℕ) : ℚ) := by
            push_cast
            simp only [r, s, t, b, pow_add]
            ring
      change (chooseMulPoly (S := ℚ) 1 ((finProdFinEquiv.symm i).1.1)).eval
          (x b + (t.1 : ℚ) * d) *
            (q ^ t.1 * y b) ^ (finProdFinEquiv.symm i).2.1 = _
      rw [hxcol, chooseMulPoly_eval]
      simp only [Nat.cast_one, one_mul]
      rw [Ring.choose_natCast, hycol]
      push_cast
      rw [mul_pow, ← pow_mul, ← pow_mul]
      ring
    rw [← hmatrix]
    exact hsel
  · exact Or.inl horder



theorem yamada_row_k_sum (K : ℕ) :
    (∑ i : Fin (K * 4), (finProdFinEquiv.symm i).1.1) = 2 * K * (K - 1) := by
  rw [Equiv.sum_comp finProdFinEquiv.symm
    (fun z : Fin K × Fin 4 => z.1.1)]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) K, Finset.sum_range_id]
  have hdiv : 2 ∣ K * (K - 1) := by
    rcases Nat.even_or_odd K with ⟨a, ha⟩ | ⟨a, ha⟩
    · refine ⟨a * (K - 1), ?_⟩
      rw [ha]
      ring
    · refine ⟨K * a, ?_⟩
      have hpred : K - 1 = 2 * a := by omega
      rw [hpred]
      ring
  calc
    4 * (K * (K - 1) / 2) = 2 * (2 * (K * (K - 1) / 2)) := by ring
    _ = 2 * (K * (K - 1)) := by rw [Nat.mul_div_cancel' hdiv]
    _ = 2 * K * (K - 1) := by ring

theorem yamada_row_l_sum (K : ℕ) :
    (∑ i : Fin (K * 4), (finProdFinEquiv.symm i).2.1) = 6 * K := by
  rw [Equiv.sum_comp finProdFinEquiv.symm
    (fun z : Fin K × Fin 4 => z.2.1)]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  omega

theorem yamada_exponent (K : ℕ) :
    (∑ a ∈ range (K * 4), a) -
      ∑ i : Fin (K * 4), (finProdFinEquiv.symm i).1.1 = 6 * K * K := by
  rw [Finset.sum_range_id, yamada_row_k_sum]
  by_cases hKzero : K = 0
  · simp [hKzero]
  have hKone : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hKzero
  have hsum : K * 4 * (K * 4 - 1) / 2 = 2 * K * (K * 4 - 1) := by
    rw [show K * 4 * (K * 4 - 1) = 2 * (2 * K * (K * 4 - 1)) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [hsum]
  have hle : 2 * K * (K - 1) ≤ 2 * K * (K * 4 - 1) := by
    gcongr <;> omega
  rw [Nat.sub_eq_iff_eq_add hle]
  have hfour : 1 ≤ K * 4 := by omega
  nlinarith [Nat.sub_add_cancel hKone, Nat.sub_add_cancel hfour]

def yamadaIntegerMatrix (K : ℕ) (r s : Fin (K * 4) → ℕ) :
    Matrix (Fin (K * 4)) (Fin (K * 4)) ℤ := fun i j =>
  ((Nat.choose (r j + s j) ((finProdFinEquiv.symm i).1.1) *
    6 ^ ((finProdFinEquiv.symm i).2.1 * r j) *
    3 ^ ((finProdFinEquiv.symm i).2.1 * s j) : ℕ) : ℤ)

theorem yamadaIntegerMatrix_natAbs_det_le
    {K X T : ℕ} (r s : Fin (K * 4) → ℕ)
    (hx : ∀ j, r j + s j ≤ X) (hr : ∀ j, r j ≤ T) (hs : ∀ j, s j ≤ T) :
    (Matrix.det (yamadaIntegerMatrix K r s)).natAbs ≤
      (K * 4).factorial * X ^ (2 * K * (K - 1)) *
        6 ^ (6 * K * T) * 3 ^ (6 * K * T) := by
  classical
  let k : Fin (K * 4) → ℕ := fun i => (finProdFinEquiv.symm i).1.1
  let l : Fin (K * 4) → ℕ := fun i => (finProdFinEquiv.symm i).2.1
  let B := X ^ (2 * K * (K - 1)) * 6 ^ (6 * K * T) * 3 ^ (6 * K * T)
  have hentry : ∀ i j,
      (yamadaIntegerMatrix K r s i j).natAbs ≤
        X ^ k i * 6 ^ (l i * T) * 3 ^ (l i * T) := by
    intro i j
    change Nat.choose (r j + s j) (k i) * 6 ^ (l i * r j) * 3 ^ (l i * s j) ≤ _
    apply Nat.mul_le_mul
    · apply Nat.mul_le_mul
      · exact (Nat.choose_le_pow _ _).trans (pow_le_pow_left' (hx j) _)
      · exact pow_le_pow_right' (by norm_num) (Nat.mul_le_mul_left (l i) (hr j))
    · exact pow_le_pow_right' (by norm_num) (Nat.mul_le_mul_left (l i) (hs j))
  have hterm : ∀ σ : Equiv.Perm (Fin (K * 4)),
      (∏ j, (yamadaIntegerMatrix K r s (σ j) j).natAbs) ≤ B := by
    intro σ
    calc
      (∏ j, (yamadaIntegerMatrix K r s (σ j) j).natAbs) ≤
          ∏ j, (X ^ k (σ j) * 6 ^ (l (σ j) * T) * 3 ^ (l (σ j) * T)) :=
        Finset.prod_le_prod (fun _ _ => by positivity) (fun j _ => hentry (σ j) j)
      _ = X ^ (∑ j, k (σ j)) * 6 ^ (∑ j, l (σ j) * T) *
          3 ^ (∑ j, l (σ j) * T) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      _ = B := by
        rw [Equiv.sum_comp σ k]
        simp_rw [← Finset.sum_mul]
        rw [Equiv.sum_comp σ l]
        simp only [B, k, l, yamada_row_k_sum, yamada_row_l_sum]
  rw [Matrix.det_apply]
  calc
    (∑ σ : Equiv.Perm (Fin (K * 4)),
        Equiv.Perm.sign σ • ∏ i, yamadaIntegerMatrix K r s (σ i) i).natAbs ≤
        ∑ σ : Equiv.Perm (Fin (K * 4)),
          (Equiv.Perm.sign σ • ∏ i, yamadaIntegerMatrix K r s (σ i) i).natAbs :=
      Int.natAbs_sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin (K * 4)),
        ∏ i, (yamadaIntegerMatrix K r s (σ i) i).natAbs := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
      · simp [hsign]
        exact map_prod Int.natAbsHom
          (fun i => yamadaIntegerMatrix K r s (σ i) i) Finset.univ
      · simp [hsign]
        exact map_prod Int.natAbsHom
          (fun i => yamadaIntegerMatrix K r s (σ i) i) Finset.univ
    _ ≤ ∑ _σ : Equiv.Perm (Fin (K * 4)), B := by
      apply Finset.sum_le_sum
      intro σ hσ
      exact hterm σ
    _ = (K * 4).factorial * B := by
      simp [Fintype.card_perm]
    _ = (K * 4).factorial * X ^ (2 * K * (K - 1)) *
        6 ^ (6 * K * T) * 3 ^ (6 * K * T) := by simp [B]; ring

theorem six_three_height_le
    {p h K T : ℕ} (hp : p.Prime) (hh : h = Nat.log 2 p)
    (hheight : 30 * T ≤ h * K) :
    6 ^ (6 * K * T) * 3 ^ (6 * K * T) ≤ p ^ (K * K) := by
  let a := 6 * K * T
  have hpow6 : 6 ^ a ≤ 2 ^ (3 * a) := by
    calc
      6 ^ a ≤ (2 ^ 3) ^ a := pow_le_pow_left' (by norm_num) a
      _ = 2 ^ (3 * a) := (pow_mul 2 3 a).symm
  have hpow3 : 3 ^ a ≤ 2 ^ (2 * a) := by
    calc
      3 ^ a ≤ (2 ^ 2) ^ a := pow_le_pow_left' (by norm_num) a
      _ = 2 ^ (2 * a) := (pow_mul 2 2 a).symm
  have hexp : 3 * a + 2 * a ≤ h * (K * K) := by
    dsimp [a]
    nlinarith [Nat.mul_le_mul_right K hheight]
  calc
    6 ^ (6 * K * T) * 3 ^ (6 * K * T) = 6 ^ a * 3 ^ a := by rfl
    _ ≤ 2 ^ (3 * a) * 2 ^ (2 * a) := Nat.mul_le_mul hpow6 hpow3
    _ = 2 ^ (3 * a + 2 * a) := by rw [pow_add]
    _ ≤ 2 ^ (h * (K * K)) := pow_le_pow_right' (by norm_num) hexp
    _ = (2 ^ h) ^ (K * K) := by rw [pow_mul]
    _ ≤ p ^ (K * K) := by
      apply pow_le_pow_left'
      rw [hh]
      exact Nat.pow_log_le_self 2 hp.ne_zero

theorem fermat_quotient_lt_or_order_lt_of_parameters
    {p H R K : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hK : 2 ≤ K) (hseed : p < H * H) (harea : p * (K * 4) ≤ R * R)
    (hNle : K * 4 ≤ p) (hcoord : 2 * (R + 3 * H) ≤ p)
    (hheight : 30 * (R + 3 * H) ≤ Nat.log 2 p * K) :
    padicValNat p (mersenne (p - 1)) < K * 4 ∨
      orderOf (2 : ZMod p) < R := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rcases exists_nonsingular_yamada_interpolation hp hp2 hp3 (by omega)
      hseed harea with horder | ⟨r, s, hr, hs, hfiber, hdetQ⟩
  · exact Or.inr horder
  · left
    by_contra hnot
    have hE : K * 4 ≤ padicValNat p (mersenne (p - 1)) := by omega
    let x : Fin (K * 4) → ℕ := fun j => r j + s j
    let k : Fin (K * 4) → ℕ := fun i => (finProdFinEquiv.symm i).1.1
    let l : Fin (K * 4) → ℕ := fun i => (finProdFinEquiv.symm i).2.1
    have hx : ∀ j, x j = r j + s j := fun _ => rfl
    have hxM : ∀ j, x j < p + 1 := by
      intro j
      have hrj : r j ≤ R + 3 * H := (hr j).le
      have hsj : s j ≤ R + 3 * H := (hs j).le
      dsimp [x]
      omega
    have hpadic := norm_yamada_evaluation_le (b := 1) hp2 hp3
      (by omega : 0 < K * 4)
      k l r s x hx hxM hE le_rfl hfiber
    have hexp : (∑ a ∈ range (K * 4), a) - ∑ i, k i = 6 * K * K := by
      simpa [k] using yamada_exponent K
    rw [hexp] at hpadic
    let MZ := yamadaIntegerMatrix K r s
    have hmapQ : MZ.map (Int.castRingHom ℚ) = fun i j : Fin (K * 4) =>
        (Nat.choose (r j + s j) ((finProdFinEquiv.symm i).1.1) : ℚ) *
          (6 : ℚ) ^ ((finProdFinEquiv.symm i).2.1 * r j) *
          (3 : ℚ) ^ ((finProdFinEquiv.symm i).2.1 * s j) := by
      ext i j
      simp [MZ, yamadaIntegerMatrix]
    have hDne : Matrix.det MZ ≠ 0 := by
      intro hD
      apply hdetQ
      rw [← hmapQ]
      calc
        Matrix.det (MZ.map (Int.castRingHom ℚ)) =
            (Int.castRingHom ℚ) (Matrix.det MZ) :=
          ((Int.castRingHom ℚ).map_det MZ).symm
        _ = 0 := by simp [hD]
    have hmapP : MZ.map (Int.castRingHom ℚ_[p]) = fun i j : Fin (K * 4) =>
        (Nat.choose (r j + s j) ((finProdFinEquiv.symm i).1.1) : ℚ_[p]) *
          (6 : ℚ_[p]) ^ ((finProdFinEquiv.symm i).2.1 * r j) *
          (3 : ℚ_[p]) ^ ((finProdFinEquiv.symm i).2.1 * s j) := by
      ext i j
      simp [MZ, yamadaIntegerMatrix]
    have hnormD : ‖((Matrix.det MZ : ℤ) : ℚ_[p])‖ ≤
        ((p : ℝ)⁻¹) ^ (6 * K * K) := by
      rw [show (((Matrix.det MZ : ℤ) : ℚ_[p])) =
          Matrix.det (MZ.map (Int.castRingHom ℚ_[p])) by
        exact (Int.castRingHom ℚ_[p]).map_det MZ]
      rw [hmapP]
      simpa [x, k, l] using hpadic
    have hdvdInt : (p ^ (6 * K * K) : ℤ) ∣ Matrix.det MZ := by
      apply (Padic.norm_int_le_pow_iff_dvd (p := p) (Matrix.det MZ) (6 * K * K)).mp
      calc
        ‖((Matrix.det MZ : ℤ) : ℚ_[p])‖ ≤
            ((p : ℝ)⁻¹) ^ (6 * K * K) := hnormD
        _ = (p : ℝ) ^ (-((6 * K * K : ℕ) : ℤ)) := by
          rw [zpow_neg, zpow_natCast, inv_pow]
    have hdvdNat : p ^ (6 * K * K) ∣ (Matrix.det MZ).natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hdvdInt
    have hpQ_le : p ^ (6 * K * K) ≤ (Matrix.det MZ).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hDne) hdvdNat
    let T := R + 3 * H
    have harch0 : (Matrix.det MZ).natAbs ≤
        (K * 4).factorial * p ^ (2 * K * (K - 1)) *
          6 ^ (6 * K * T) * 3 ^ (6 * K * T) := by
      apply yamadaIntegerMatrix_natAbs_det_le r s
      · intro j
        have hrj : r j ≤ T := (hr j).le
        have hsj : s j ≤ T := (hs j).le
        dsimp [T] at hrj hsj ⊢
        omega
      · intro j
        exact (hr j).le
      · intro j
        exact (hs j).le
    have hfact : (K * 4).factorial ≤ p ^ (K * 4) := by
      exact (Nat.factorial_le_pow (K * 4)).trans
        (pow_le_pow_left' hNle (K * 4))
    have hbase : 6 ^ (6 * K * T) * 3 ^ (6 * K * T) ≤ p ^ (K * K) := by
      exact six_three_height_le hp rfl (by simpa [T] using hheight)
    have harch : (Matrix.det MZ).natAbs ≤
        p ^ ((K * 4) + 2 * K * (K - 1) + K * K) := by
      calc
        (Matrix.det MZ).natAbs ≤
            (K * 4).factorial * p ^ (2 * K * (K - 1)) *
              (6 ^ (6 * K * T) * 3 ^ (6 * K * T)) := by
          simpa only [mul_assoc] using harch0
        _ ≤ p ^ (K * 4) * p ^ (2 * K * (K - 1)) * p ^ (K * K) := by
          exact Nat.mul_le_mul (Nat.mul_le_mul hfact le_rfl) hbase
        _ = p ^ ((K * 4) + 2 * K * (K - 1) + K * K) := by
          rw [← pow_add, ← pow_add]
    have hexplt : (K * 4) + 2 * K * (K - 1) + K * K < 6 * K * K := by
      nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ K)]
    have hpPowLt : p ^ ((K * 4) + 2 * K * (K - 1) + K * K) <
        p ^ (6 * K * K) := (Nat.pow_lt_pow_iff_right hp.one_lt).2 hexplt
    omega



theorem large_poly_le_two_pow {n : ℕ} (hn : 128 ≤ n) :
    2_000_000_000_000 * n * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      nlinarith [sq_nonneg (n - 1)]

theorem large_prime_parameters {p : ℕ} (hp : p.Prime)
    (hlarge : 20_000_000 ≤ Nat.log 2 p) :
    let h := Nat.log 2 p
    let H := p / h + 1
    let K := 1_000_000_000_000 * (p / (h * h))
    let R := 3_000_000 * H
    2 ≤ K ∧ p < H * H ∧ p * (K * 4) ≤ R * R ∧
      K * 4 ≤ p ∧ 2 * (R + 3 * H) ≤ p ∧
      30 * (R + 3 * H) ≤ h * K := by
  dsimp only
  let h := Nat.log 2 p
  let q := p / (h * h)
  let u := p / h
  let H := u + 1
  let K := 1_000_000_000_000 * q
  let R := 3_000_000 * H
  have hh : 20_000_000 ≤ h := hlarge
  have hhpos : 0 < h := by omega
  have hpoly : 2_000_000_000_000 * h * h ≤ 2 ^ h :=
    large_poly_le_two_pow (by omega)
  have hpowp : 2 ^ h ≤ p := by
    dsimp [h]
    exact Nat.pow_log_le_self 2 hp.ne_zero
  have hhhp : h * h ≤ p := by
    calc
      h * h ≤ 2_000_000_000_000 * h * h := by
        nlinarith [show 1 ≤ 2_000_000_000_000 by norm_num]
      _ ≤ 2 ^ h := hpoly
      _ ≤ p := hpowp
  have hq1 : 1 ≤ q := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < h * h)).2
    simpa [q] using hhhp
  have hqmul : q * (h * h) ≤ p := by
    exact Nat.div_mul_le_self p (h * h)
  have hqupper : p < (q + 1) * (h * h) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < h * h)).mp
    simpa [q] using Nat.lt_succ_self (p / (h * h))
  have humul : u * h ≤ p := by
    exact Nat.div_mul_le_self p h
  have huupper : p < (u + 1) * h := by
    apply (Nat.div_lt_iff_lt_mul hhpos).mp
    simpa [u] using Nat.lt_succ_self (p / h)
  have hhleu : h ≤ u := by
    apply (Nat.le_div_iff_mul_le hhpos).2
    simpa [u, mul_comm] using hhhp
  have hpHH : p < H * H := by
    calc
      p < H * h := by simpa [H, u, mul_comm] using huupper
      _ ≤ H * H := Nat.mul_le_mul_left H (by omega)
  have hHq : H ≤ 2 * q * h := by
    have huq : u < (q + 1) * h := by
      apply (Nat.div_lt_iff_lt_mul hhpos).2
      simpa [mul_assoc] using hqupper
    dsimp [H]
    nlinarith [Nat.mul_le_mul_right h hq1]
  have hK2 : 2 ≤ K := by
    dsimp [K]
    nlinarith
  have hhC : 4_000_000_000_000 ≤ h * h := by nlinarith
  have hNle : K * 4 ≤ p := by
    calc
      K * 4 = q * 4_000_000_000_000 := by simp [K]; ring
      _ ≤ q * (h * h) := Nat.mul_le_mul_left q hhC
      _ ≤ p := hqmul
  have harea : p * (K * 4) ≤ R * R := by
    have ha : (p * (K * 4)) * (h * h) ≤
        4_000_000_000_000 * (p * p) := by
      calc
        (p * (K * 4)) * (h * h) =
            4_000_000_000_000 * p * (q * (h * h)) := by simp [K]; ring
        _ ≤ 4_000_000_000_000 * (p * p) := by
          simpa [mul_assoc] using
            Nat.mul_le_mul_left (4_000_000_000_000 * p) hqmul
    have hb : 4_000_000_000_000 * (p * p) ≤ (R * R) * (h * h) := by
      have hp2 : p * p ≤ (H * h) * (H * h) :=
        Nat.mul_le_mul huupper.le huupper.le
      calc
        4_000_000_000_000 * (p * p) ≤
            4_000_000_000_000 * ((H * h) * (H * h)) :=
          Nat.mul_le_mul_left _ hp2
        _ ≤ 9_000_000_000_000 * ((H * h) * (H * h)) := by
          exact Nat.mul_le_mul_right _ (by norm_num)
        _ = (R * R) * (h * h) := by simp [R]; ring
    exact Nat.le_of_mul_le_mul_right (ha.trans hb) (by positivity)
  have hcoord : 2 * (R + 3 * H) ≤ p := by
    have hcH : 6_000_006 * H ≤ p := by
      have hc1 : 2 * 6_000_006 * u ≤ p := by
        calc
          2 * 6_000_006 * u ≤ h * u := by
            exact Nat.mul_le_mul_right u (by omega)
          _ ≤ p := by simpa [mul_comm] using humul
      have hc2 : 2 * 6_000_006 ≤ p := by
        calc
          2 * 6_000_006 ≤ h * h := by nlinarith
          _ ≤ p := hhhp
      dsimp [H]
      omega
    calc
      2 * (R + 3 * H) = 6_000_006 * H := by simp [R]; ring
      _ ≤ p := hcH
  have hheight : 30 * (R + 3 * H) ≤ h * K := by
    have hc : 180_000_180 ≤ 1_000_000_000_000 := by norm_num
    calc
      30 * (R + 3 * H) = 90_000_090 * H := by simp [R]; ring
      _ ≤ 90_000_090 * (2 * q * h) := Nat.mul_le_mul_left _ hHq
      _ = 180_000_180 * (q * h) := by ring
      _ ≤ 1_000_000_000_000 * (q * h) := Nat.mul_le_mul_right _ hc
      _ = h * K := by simp [K]; ring
  exact ⟨hK2, hpHH, harea, hNle, hcoord, hheight⟩

theorem real_log_bounds_nat_log_two {n : ℕ} (hn : n ≠ 0) :
    ((Nat.log 2 n : ℕ) : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) ∧
      Real.log (n : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 := by
  have hloNat : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
  have hhiNat : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self one_lt_two n
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h2powR : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n := by positivity
  constructor
  · have hloR : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by exact_mod_cast hloNat
    have hlog := Real.log_le_log h2powR hloR
    simpa [Real.log_pow] using hlog
  · have hhiR : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 n + 1) := by
      exact_mod_cast hhiNat.le
    have hlog := Real.log_le_log hnR hhiR
    simpa [Real.log_pow] using hlog

theorem fermat_quotient_uniform_bound :
    ∀ p : ℕ, p.Prime →
      (padicValNat p (mersenne (p - 1)) : ℝ) * Real.log (p : ℝ) ≤
        1_000_000_000_000_000 *
          ((p : ℝ) / Real.log (p : ℝ) + Real.log (p : ℝ)) := by
  intro p hp
  let h := Nat.log 2 p
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  obtain ⟨hlogLower, hlogUpper⟩ := real_log_bounds_nat_log_two hp.ne_zero
  by_cases hlarge : 20_000_000 ≤ h
  · have hp2 : p ≠ 2 := by
      intro heq
      subst p
      norm_num [h] at hlarge
    have hp3 : p ≠ 3 := by
      intro heq
      subst p
      norm_num [h] at hlarge
    obtain ⟨hK, hseed, harea, hNle, hcoord, hheight⟩ :=
      large_prime_parameters hp (by simpa [h] using hlarge)
    have halt := fermat_quotient_lt_or_order_lt_of_parameters hp hp2 hp3
      hK hseed harea hNle hcoord hheight
    have hhR : (0 : ℝ) < h := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hlarge)
    have hlogUpper2 : Real.log (p : ℝ) ≤ 2 * (h : ℝ) := by
      calc
        Real.log (p : ℝ) ≤ ((h + 1 : ℕ) : ℝ) * Real.log 2 := by
          simpa [h] using hlogUpper
        _ ≤ ((h + 1 : ℕ) : ℝ) :=
          mul_le_of_le_one_right (by positivity) hlog2le
        _ ≤ 2 * (h : ℝ) := by norm_cast; omega
    have hpDivH : (p : ℝ) / (h : ℝ) ≤
        2 * ((p : ℝ) / Real.log (p : ℝ)) := by
      rw [div_le_iff₀ hhR]
      have hone : (1 : ℝ) ≤ 2 * (h : ℝ) / Real.log (p : ℝ) :=
        (le_div_iff₀ hlogp).2 (by simpa using hlogUpper2)
      calc
        (p : ℝ) ≤ (p : ℝ) * (2 * (h : ℝ) / Real.log (p : ℝ)) := by
          exact le_mul_of_one_le_right (by positivity) hone
        _ = 2 * ((p : ℝ) / Real.log (p : ℝ)) * (h : ℝ) := by ring
    rcases halt with hval | horder
    · have hqcast : ((p / (h * h) : ℕ) : ℝ) ≤
          (p : ℝ) / ((h : ℝ) * (h : ℝ)) := by
        simpa [Nat.cast_mul] using
          (Nat.cast_div_le (α := ℝ) (m := p) (n := h * h))
      have hEval : (padicValNat p (mersenne (p - 1)) : ℝ) ≤
          4_000_000_000_000 *
            ((p : ℝ) / ((h : ℝ) * (h : ℝ))) := by
        calc
          (padicValNat p (mersenne (p - 1)) : ℝ) ≤
              (1_000_000_000_000 * (p / (h * h)) * 4 : ℕ) := by
            exact_mod_cast hval.le
          _ = 4_000_000_000_000 * ((p / (h * h) : ℕ) : ℝ) := by
            push_cast
            ring
          _ ≤ 4_000_000_000_000 *
              ((p : ℝ) / ((h : ℝ) * (h : ℝ))) := by gcongr
      have hmain : (padicValNat p (mersenne (p - 1)) : ℝ) *
          Real.log (p : ℝ) ≤
            8_000_000_000_000 * ((p : ℝ) / (h : ℝ)) := by
        calc
          (padicValNat p (mersenne (p - 1)) : ℝ) * Real.log (p : ℝ) ≤
              (4_000_000_000_000 *
                ((p : ℝ) / ((h : ℝ) * (h : ℝ)))) *
                  (2 * (h : ℝ)) :=
            mul_le_mul hEval hlogUpper2 hlogp.le (by positivity)
          _ = 8_000_000_000_000 * ((p : ℝ) / (h : ℝ)) := by
            field_simp
            ring
      calc
        (padicValNat p (mersenne (p - 1)) : ℝ) * Real.log (p : ℝ) ≤
            8_000_000_000_000 * ((p : ℝ) / (h : ℝ)) := hmain
        _ ≤ 8_000_000_000_000 *
            (2 * ((p : ℝ) / Real.log (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hpDivH (by norm_num)
        _ ≤ 1_000_000_000_000_000 *
            ((p : ℝ) / Real.log (p : ℝ) + Real.log (p : ℝ)) := by
          have hpdivnonneg : 0 ≤ (p : ℝ) / Real.log (p : ℝ) := by positivity
          nlinarith
    · have hordBound := fermat_quotient_orderOf_log_bound hp hp2
      have hRcast : (orderOf (2 : ZMod p) : ℝ) ≤
          3_000_000 * (((p : ℝ) / (h : ℝ)) + 1) := by
        calc
          (orderOf (2 : ZMod p) : ℝ) ≤
              (3_000_000 * (p / h + 1) : ℕ) := by exact_mod_cast horder.le
          _ = 3_000_000 * (((p / h : ℕ) : ℝ) + 1) := by push_cast; ring
          _ ≤ 3_000_000 * (((p : ℝ) / (h : ℝ)) + 1) := by
            gcongr
            exact Nat.cast_div_le (α := ℝ)
      have hlogpOne : (1 : ℝ) ≤ Real.log (p : ℝ) := by
        have hhalf : (1 / 2 : ℝ) < Real.log 2 :=
          lt_trans (by norm_num) Real.log_two_gt_d9
        have hhcast : (2 : ℝ) ≤ h := by exact_mod_cast (by omega : 2 ≤ h)
        nlinarith
      calc
        _ ≤ (orderOf (2 : ZMod p) : ℝ) * Real.log 2 := hordBound
        _ ≤ (orderOf (2 : ZMod p) : ℝ) :=
          mul_le_of_le_one_right (by positivity) hlog2le
        _ ≤ 3_000_000 * (((p : ℝ) / (h : ℝ)) + 1) := hRcast
        _ ≤ 3_000_000 *
            (2 * ((p : ℝ) / Real.log (p : ℝ)) + Real.log (p : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add hpDivH hlogpOne) (by norm_num)
        _ ≤ 1_000_000_000_000_000 *
            ((p : ℝ) / Real.log (p : ℝ) + Real.log (p : ℝ)) := by
          have hpdivnonneg : 0 ≤ (p : ℝ) / Real.log (p : ℝ) := by positivity
          nlinarith
  · have hhsmall : h < 20_000_000 := by omega
    have hlogpUpper : Real.log (p : ℝ) ≤ 20_000_000 := by
      calc
        Real.log (p : ℝ) ≤ ((h + 1 : ℕ) : ℝ) * Real.log 2 := by
          simpa [h] using hlogUpper
        _ ≤ ((h + 1 : ℕ) : ℝ) :=
          mul_le_of_le_one_right (by positivity) hlog2le
        _ ≤ 20_000_000 := by exact_mod_cast hhsmall
    have htriv := fermat_quotient_trivial_log_bound hp
    have htrivP : (padicValNat p (mersenne (p - 1)) : ℝ) * Real.log (p : ℝ) ≤
        (p : ℝ) := by
      calc
        _ ≤ (((p - 1 : ℕ) : ℝ)) * Real.log 2 := htriv
        _ ≤ (((p - 1 : ℕ) : ℝ)) :=
          mul_le_of_le_one_right (by positivity) hlog2le
        _ ≤ p := by exact_mod_cast Nat.sub_le p 1
    have hpC : (p : ℝ) ≤
        1_000_000_000_000_000 * ((p : ℝ) / Real.log (p : ℝ)) := by
      calc
        (p : ℝ) = ((p : ℝ) / Real.log (p : ℝ)) * Real.log (p : ℝ) := by
          field_simp
        _ ≤ ((p : ℝ) / Real.log (p : ℝ)) * 1_000_000_000_000_000 := by
          exact mul_le_mul_of_nonneg_left
            (hlogpUpper.trans (by norm_num)) (by positivity)
        _ = 1_000_000_000_000_000 * ((p : ℝ) / Real.log (p : ℝ)) := by ring
    exact htrivP.trans (hpC.trans (by
      have : 0 ≤ Real.log (p : ℝ) := hlogp.le
      nlinarith))



/-- The factor by which Stewart's lower bound improves on the linear
primitive-divisor bound. -/
noncomputable def stewartFactor (n : ℕ) : ℝ :=
  Real.exp
    (Real.log (n : ℝ) /
      (104 * Real.log (Real.log (n : ℝ))))

/-- The slower factor obtained from Yamada's two-logarithm estimate.  Stewart
records that an eventual lower bound by a positive constant times
`n * yamadaFactor n` already gives an alternative proof of Problem 977. -/
noncomputable def yamadaFactor (n : ℕ) : ℝ :=
  Real.sqrt
    (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))

/-- Formula (1.8) in Stewart's paper, specialized to `(a,b) = (2,1)` and
expressed as an eventual proposition. -/
def StewartMersenneEstimate : Prop :=
  ∀ᶠ n : ℕ in atTop,
    (n : ℝ) * stewartFactor n <
      (greatestPrimeFactor (mersenne n) : ℝ)

/-- The weaker published estimate that follows from Yamada's bound for two
`p`-adic logarithms.  Unlike `StewartMersenneEstimate`, the multiplicative
constant is not normalized to one. -/
def YamadaMersenneEstimate : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) * yamadaFactor n <
        (greatestPrimeFactor (mersenne n) : ℝ)

/-- The real function `x / log x` diverges to positive infinity. -/
theorem tendsto_id_div_log_atTop :
    Tendsto (fun x : ℝ => x / Real.log x) atTop atTop := by
  have hzero : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in atTop, Real.log x / x ∈ Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (lt_trans zero_lt_one hx)
  have hright : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hzero hpos
  have hinv := hright.inv_tendsto_nhdsGT_zero
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (inv_div (Real.log x) x).trans (by simp only)

/-- The common logarithmic quotient in both Stewart's and Yamada's bounds
diverges to positive infinity along the natural numbers. -/
theorem log_div_log_log_tendsto_atTop :
    Tendsto
      (fun n : ℕ =>
        Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))
      atTop atTop := by
  simpa [Function.comp_def] using
    tendsto_id_div_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- The exponent in Stewart's factor tends to positive infinity along the
natural numbers. -/
theorem stewartExponent_tendsto_atTop :
    Tendsto
      (fun n : ℕ =>
        Real.log (n : ℝ) /
          (104 * Real.log (Real.log (n : ℝ))))
      atTop atTop := by
  convert Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 104)
    log_div_log_log_tendsto_atTop using 1
  funext n
  ring

/-- Stewart's superlinear factor itself tends to positive infinity. -/
theorem stewartFactor_tendsto_atTop :
    Tendsto stewartFactor atTop atTop := by
  exact Real.tendsto_exp_atTop.comp stewartExponent_tendsto_atTop

/-- Yamada's square-root factor tends to positive infinity. -/
theorem yamadaFactor_tendsto_atTop :
    Tendsto yamadaFactor atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp log_div_log_log_tendsto_atTop

/-- Stewart's published eventual estimate implies exactly the limit asked in
Problem 977.  This theorem contains the complete elementary/analytic transfer
from the number-theoretic estimate to filter convergence. -/
theorem erdos_977_of_stewart (hStewart : StewartMersenneEstimate) :
    Erdos977Statement := by
  rw [Erdos977Statement]
  refine tendsto_atTop.mpr fun A => ?_
  filter_upwards [hStewart, stewartFactor_tendsto_atTop.eventually_ge_atTop A,
    eventually_gt_atTop (0 : ℕ)] with n hbound hfactor hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact hfactor.trans (le_of_lt ((lt_div_iff₀ hn').2 (by
    simpa only [mul_comm] using hbound)))

/-- The complete transfer from Yamada's weaker published estimate to the
literal limit in Problem 977. -/
theorem erdos_977_of_yamada (hYamada : YamadaMersenneEstimate) :
    Erdos977Statement := by
  obtain ⟨c, hc, hbound⟩ := hYamada
  rw [Erdos977Statement]
  refine tendsto_atTop.mpr fun A => ?_
  filter_upwards [hbound,
    yamadaFactor_tendsto_atTop.eventually_ge_atTop (A / c),
    eventually_gt_atTop (0 : ℕ)] with n hnBound hnFactor hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : A ≤ c * yamadaFactor n := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hnFactor
  apply hA.trans
  exact le_of_lt ((lt_div_iff₀ hn').2 (by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hnBound))

/-- Erdős Problem 977 has an affirmative answer: the greatest prime
factor of `2^n - 1`, divided by `n`, tends to positive infinity. -/
theorem erdos_977 : (Filter.Tendsto
  (fun n : ℕ => (Erdos977.greatestPrimeFactor (Erdos977.mersenne n) : ℝ) / (n : ℝ))
  Filter.atTop Filter.atTop) := by
  exact erdos_977_of_fermat_quotient_bound
    1_000_000_000_000_000 (by positivity) fermat_quotient_uniform_bound

#print axioms Erdos977.stewartFactor_tendsto_atTop
#print axioms Erdos977.erdos_977_of_stewart
#print axioms Erdos977.erdos_977_of_yamada
#print axioms Erdos977.erdos_977

end Erdos977
