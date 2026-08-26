import ErdosProblems.Erdos4.RandomResidueSieve
import ErdosProblems.Erdos4.LocalSurvivalRatios

/-!
# Counting the primes at which a finite set has a collision

All collision primes divide the positive product of pairwise positive
differences. The elementary bound `2 ^ card ≤ product` bounds their
number by a logarithm, uniformly over the finite set.
-/

open scoped BigOperators

namespace Erdos4.CollisionModuli

theorem prime_divisor_card_log_le (S : Finset ℕ) {N : ℕ} (hN : 0 < N)
    (hprime : ∀ p ∈ S, p.Prime) (hdiv : ∀ p ∈ S, p ∣ N) :
    (S.card : ℝ) * Real.log 2 ≤ Real.log N := by
  have hsub : S ⊆ N.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hp, hdiv p hp, hN.ne'⟩
  have hprod : ∏ p ∈ S, p ∣ N :=
    (Finset.prod_dvd_prod_of_subset S N.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd N)
  have htwo : 2 ^ S.card ≤ ∏ p ∈ S, p := by
    calc
      _ = ∏ _p ∈ S, 2 := by simp
      _ ≤ _ := Finset.prod_le_prod' (fun p hp => (hprime p hp).two_le)
  have hle : (2 : ℝ) ^ S.card ≤ N := by exact_mod_cast htwo.trans (Nat.le_of_dvd hN hprod)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ S.card) hle
  simpa only [Real.log_pow] using hlog

def differenceProduct (T : Finset ℕ) : ℕ :=
  ∏ n ∈ T, ∏ m ∈ T, if n < m then m - n else 1

theorem differenceProduct_pos (T : Finset ℕ) : 0 < differenceProduct T := by
  apply Finset.prod_pos
  intro n _hn
  apply Finset.prod_pos
  intro m _hm
  split_ifs with hnm
  · exact Nat.sub_pos_of_lt hnm
  · exact Nat.zero_lt_one

theorem differenceProduct_le (T : Finset ℕ) {Y : ℕ} (hY : 1 ≤ Y)
    (hT : ∀ n ∈ T, n ≤ Y) : differenceProduct T ≤ Y ^ (T.card ^ 2) := by
  calc
    _ ≤ ∏ _n ∈ T, ∏ _m ∈ T, Y := by
      apply Finset.prod_le_prod'
      intro n _hn
      apply Finset.prod_le_prod'
      intro m hm
      split_ifs
      · exact (Nat.sub_le m n).trans (hT m hm)
      · exact hY
    _ = _ := by simp [← pow_mul, pow_two]

theorem prime_dvd_differenceProduct (T : Finset ℕ) {p n m : ℕ}
    (hn : n ∈ T) (hm : m ∈ T) (hnm : n ≠ m) (hmod : n ≡ m [MOD p]) :
    p ∣ differenceProduct T := by
  have hordered {a b : ℕ} (ha : a ∈ T) (hb : b ∈ T) (hab : a < b)
      (hd : p ∣ b - a) : p ∣ differenceProduct T := by
    have hinner : p ∣ ∏ m ∈ T, if a < m then m - a else 1 :=
      dvd_trans (by simpa only [if_pos hab] using hd) (Finset.dvd_prod_of_mem _ hb)
    exact hinner.trans (Finset.dvd_prod_of_mem _ ha)
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hordered hn hm hlt hmod.dvd'
  · exact hordered hm hn hgt hmod.symm.dvd'

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def collisionPrimes (T : Finset ℕ) : Finset P := by
  classical
  exact Finset.univ.filter (fun l => ¬Set.InjOn (fun n : ℕ => (n : ZMod (ell l))) T)

theorem collision_dvd (T : Finset ℕ) {l : P} (hl : l ∈ collisionPrimes ell T) :
    ell l ∣ differenceProduct T := by
  classical
  have hh := (Finset.mem_filter.mp hl).2
  change ¬(∀ n ∈ T, ∀ m ∈ T, (n : ZMod (ell l)) = (m : ZMod (ell l)) → n = m) at hh
  push_neg at hh
  obtain ⟨n, hn, m, hm, hmod, hne⟩ := hh
  exact prime_dvd_differenceProduct T hn hm hne ((ZMod.natCast_eq_natCast_iff n m (ell l)).mp hmod)

theorem collision_card_log_le (hinj : Function.Injective ell) (T : Finset ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) (hT : ∀ n ∈ T, n ≤ Y) :
    ((collisionPrimes ell T).card : ℝ) * Real.log 2 ≤ (T.card : ℝ) ^ 2 * Real.log Y := by
  classical
  let S := (collisionPrimes ell T).image ell
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    obtain ⟨l, _hl, rfl⟩ := Finset.mem_image.mp hp
    exact Fact.out
  have hdiv : ∀ p ∈ S, p ∣ differenceProduct T := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    exact collision_dvd ell T hl
  have hcount := prime_divisor_card_log_le S (differenceProduct_pos T) hprime hdiv
  have hcard : S.card = (collisionPrimes ell T).card := Finset.card_image_of_injective _ hinj
  rw [hcard] at hcount
  have hlog : Real.log (differenceProduct T : ℝ) ≤ (T.card : ℝ) ^ 2 * Real.log Y := by
    have h := Real.log_le_log (by exact_mod_cast differenceProduct_pos T)
      (by exact_mod_cast differenceProduct_le T hY hT :
        (differenceProduct T : ℝ) ≤ (Y : ℝ) ^ (T.card ^ 2))
    simpa only [Real.log_pow, Nat.cast_pow] using h
  exact hcount.trans hlog

theorem collision_reciprocal_le (hinj : Function.Injective ell) (T : Finset ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) (hT : ∀ n ∈ T, n ≤ Y)
    {w : ℝ} (hw : 0 < w) (hlarge : ∀ l, w ≤ ell l) :
    (∑ l ∈ collisionPrimes ell T, 1 / (ell l : ℝ)) ≤
      (T.card : ℝ) ^ 2 * Real.log Y / (w * Real.log 2) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc := (le_div_iff₀ hlog2).mpr (collision_card_log_le ell hinj T hY hT)
  calc
    _ ≤ ∑ _l ∈ collisionPrimes ell T, 1 / w :=
      Finset.sum_le_sum (fun l _hl => one_div_le_one_div_of_le hw (hlarge l))
    _ = ((collisionPrimes ell T).card : ℝ) / w := by simp [div_eq_mul_inv]
    _ ≤ ((T.card : ℝ) ^ 2 * Real.log Y / Real.log 2) / w :=
      div_le_div_of_nonneg_right hc hw.le
    _ = _ := by ring

end Erdos4.CollisionModuli
