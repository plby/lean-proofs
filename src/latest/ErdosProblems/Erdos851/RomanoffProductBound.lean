import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Ring.Pow

/-!
# A finite Euler-product bound for Erdős problem 851

We prove the elementary estimate

`(∏ p ∈ P, p / (p - 1)) ^ 5 ≤ 8 * |P| ^ 2`

for every nonempty finite set of odd primes.  The proof inducts on the largest
prime.  Its only counting input is an injection that compresses the odd primes
below `a` into `Finset.range (a / 3)`.
-/

open Finset
open scoped BigOperators

namespace Erdos851

/-- Compress the exceptional prime `3` to zero and every other odd prime to
its block of three consecutive natural numbers. -/
private def primeCompress (q : ℕ) : ℕ := if q = 3 then 0 else q / 3

private lemma primeCompress_injOn (P : Finset ℕ)
    (hprime : ∀ q ∈ P, q.Prime) (hne2 : ∀ q ∈ P, q ≠ 2) :
    Set.InjOn primeCompress P := by
  intro q hq r hr heq
  have hqp := hprime q hq
  have hrp := hprime r hr
  have hq2 := hne2 q hq
  have hr2 := hne2 r hr
  by_cases hq3 : q = 3
  · subst q
    by_cases hr3 : r = 3
    · exact hr3.symm
    · simp [primeCompress, hr3] at heq
      have hr2le := hrp.two_le
      have hrge : 3 ≤ r := by omega
      omega
  · by_cases hr3 : r = 3
    · subst r
      simp [primeCompress, hq3] at heq
      have hq2le := hqp.two_le
      have hqge : 3 ≤ q := by omega
      omega
    · have hqodd := hqp.odd_of_ne_two hq2
      have hrodd := hrp.odd_of_ne_two hr2
      obtain ⟨uq, huq⟩ := hqodd
      obtain ⟨ur, hur⟩ := hrodd
      have hqmod : q % 3 ≠ 0 := by
        intro hz
        have hdvd : 3 ∣ q := Nat.dvd_of_mod_eq_zero hz
        rcases (Nat.dvd_prime hqp).mp hdvd with h31 | h3q
        · omega
        · exact hq3 h3q.symm
      have hrmod : r % 3 ≠ 0 := by
        intro hz
        have hdvd : 3 ∣ r := Nat.dvd_of_mod_eq_zero hz
        rcases (Nat.dvd_prime hrp).mp hdvd with h31 | h3r
        · omega
        · exact hr3 h3r.symm
      simp [primeCompress, hq3, hr3] at heq
      omega

private lemma primeCompress_lt_div_of_lt {q a : ℕ}
    (hqp : q.Prime) (hq2 : q ≠ 2) (hap : a.Prime) (ha2 : a ≠ 2)
    (hqa : q < a) : primeCompress q < a / 3 := by
  by_cases hq3 : q = 3
  · subst q
    have ha2le := hap.two_le
    simp [primeCompress]
    omega
  · have hq2le := hqp.two_le
    have hq3le : 3 ≤ q := by omega
    have ha3 : a ≠ 3 := by omega
    have hqodd := hqp.odd_of_ne_two hq2
    have haodd := hap.odd_of_ne_two ha2
    obtain ⟨uq, huq⟩ := hqodd
    obtain ⟨ua, hua⟩ := haodd
    have hqmod : q % 3 ≠ 0 := by
      intro hz
      have hdvd : 3 ∣ q := Nat.dvd_of_mod_eq_zero hz
      rcases (Nat.dvd_prime hqp).mp hdvd with h31 | h3q
      · omega
      · exact hq3 h3q.symm
    have hamod : a % 3 ≠ 0 := by
      intro hz
      have hdvd : 3 ∣ a := Nat.dvd_of_mod_eq_zero hz
      rcases (Nat.dvd_prime hap).mp hdvd with h31 | h3a
      · omega
      · exact ha3 h3a.symm
    simp [primeCompress, hq3]
    omega

/-- If `a` is an odd prime strictly larger than every odd prime in the
nonempty set `s`, then `a` is strictly larger than `3 * s.card`. -/
private lemma three_mul_card_lt_max_insert
    (a : ℕ) (s : Finset ℕ) (hlt : ∀ q ∈ s, q < a)
    (ha : a.Prime) (ha2 : a ≠ 2)
    (hsprime : ∀ q ∈ s, q.Prime) (hs2 : ∀ q ∈ s, q ≠ 2)
    (hsne : s.Nonempty) : 3 * s.card < a := by
  have himage : image primeCompress s ⊆ range (a / 3) := by
    rw [image_subset_iff]
    intro q hq
    simp only [mem_range]
    exact primeCompress_lt_div_of_lt (hsprime q hq) (hs2 q hq) ha ha2 (hlt q hq)
  have hcardimage : (image primeCompress s).card = s.card :=
    card_image_iff.mpr (primeCompress_injOn s hsprime hs2)
  have hcard : s.card ≤ a / 3 := by
    rw [← hcardimage]
    exact (card_le_card himage).trans_eq (card_range _)
  have hweak : 3 * s.card ≤ a := by
    have := (Nat.le_div_iff_mul_le (by omega : 0 < 3)).mp hcard
    omega
  by_contra hnlt
  have heq : 3 * s.card = a := by omega
  have h3dvd : 3 ∣ a := by
    use s.card
    omega
  have ha3 : a = 3 := by
    rcases (Nat.dvd_prime ha).mp h3dvd with h31 | h3a
    · omega
    · exact h3a.symm
  obtain ⟨q, hq⟩ := hsne
  have hq2le := (hsprime q hq).two_le
  have hq2 := hs2 q hq
  have hq3le : 3 ≤ q := by omega
  have hqa := hlt q hq
  omega

private lemma model_ratio_pow_five (x : ℝ) (hx : 2 ≤ x) :
    (((3 * x + 1) / (3 * x)) ^ 5) * x ^ 2 ≤ (x + 1) ^ 2 := by
  have hden : 0 < (3 * x) ^ 5 := by positivity
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ hden]
  have hy : 0 ≤ x - 2 := by linarith
  have hpoly :
      0 ≤ 81 * (x - 2) ^ 6 + 945 * (x - 2) ^ 5 +
          4500 * (x - 2) ^ 4 + 11145 * (x - 2) ^ 3 +
          15029 * (x - 2) ^ 2 + 10328 * (x - 2) + 2756 := by
    positivity
  calc
    (3 * x + 1) ^ 5 * x ^ 2 ≤
        (3 * x) ^ 5 * (x + 1) ^ 2 := by
      nlinarith [hpoly]
    _ = (x + 1) ^ 2 * (3 * x) ^ 5 := by ring

private lemma prime_ratio_step (a m : ℕ) (ha : a.Prime) (ha2 : a ≠ 2)
    (hm : 0 < m) (hmax : 3 * m < a) :
    (((a : ℝ) / (a - 1)) ^ 5) * (8 * (m : ℝ) ^ 2) ≤
      8 * ((m + 1 : ℕ) : ℝ) ^ 2 := by
  by_cases hm1 : m = 1
  · subst m
    have haodd := ha.odd_of_ne_two ha2
    obtain ⟨u, hu⟩ := haodd
    have ha5 : 5 ≤ a := by omega
    have haR : (5 : ℝ) ≤ a := by exact_mod_cast ha5
    have hden : (0 : ℝ) < a - 1 := by
      nlinarith
    have hratio : (a : ℝ) / (a - 1) ≤ (5 : ℝ) / 4 := by
      rw [div_le_iff₀ hden]
      nlinarith
    have hnonneg : 0 ≤ (a : ℝ) / (a - 1) := by positivity
    have hp := pow_le_pow_left₀ hnonneg hratio 5
    norm_num at hp ⊢
    nlinarith
  · have hm2 : 2 ≤ m := by omega
    have hma : 3 * m + 1 ≤ a := by omega
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hmaR : (3 * (m : ℝ) + 1) ≤ a := by exact_mod_cast hma
    have hdena : (0 : ℝ) < a - 1 := by
      nlinarith
    have hdenm : (0 : ℝ) < 3 * m := by positivity
    have hratio : (a : ℝ) / (a - 1) ≤
        (3 * (m : ℝ) + 1) / (3 * m) := by
      rw [div_le_div_iff₀ hdena hdenm]
      nlinarith
    have hnonneg : 0 ≤ (a : ℝ) / (a - 1) := by positivity
    have hp := pow_le_pow_left₀ hnonneg hratio 5
    have hmodel := model_ratio_pow_five (m : ℝ) hmR
    calc
      ((a : ℝ) / (a - 1)) ^ 5 * (8 * (m : ℝ) ^ 2) ≤
          ((3 * (m : ℝ) + 1) / (3 * m)) ^ 5 *
            (8 * (m : ℝ) ^ 2) := by gcongr
      _ ≤ 8 * ((m : ℝ) + 1) ^ 2 := by nlinarith
      _ = 8 * ((m + 1 : ℕ) : ℝ) ^ 2 := by norm_num

private theorem oddPrimeProduct_fifth_le_ne_two (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hne2 : ∀ p ∈ P, p ≠ 2)
    (hPne : P.Nonempty) :
    (∏ p ∈ P, (p : ℝ) / (p - 1)) ^ 5 ≤ 8 * (P.card : ℝ) ^ 2 := by
  induction P using Finset.induction_on_max with
  | empty => simp at hPne
  | @insert a s hlt ih =>
      have has : a ∉ s := by
        intro haS
        exact Nat.lt_irrefl a (hlt a haS)
      have ha := hprime a (mem_insert_self a s)
      have ha2 := hne2 a (mem_insert_self a s)
      have hsprime : ∀ q ∈ s, q.Prime := by
        intro q hq
        exact hprime q (mem_insert_of_mem hq)
      have hs2 : ∀ q ∈ s, q ≠ 2 := by
        intro q hq
        exact hne2 q (mem_insert_of_mem hq)
      by_cases hsne : s.Nonempty
      · have hih := ih hsprime hs2 hsne
        have hmax := three_mul_card_lt_max_insert a s hlt ha ha2 hsprime hs2 hsne
        have hstep := prime_ratio_step a s.card ha ha2 (card_pos.mpr hsne) hmax
        have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha.two_le
        have hafac_nonneg : 0 ≤ (a : ℝ) / (a - 1) := by
          exact div_nonneg (by positivity) (by linarith)
        rw [prod_insert has, card_insert_of_notMem has]
        calc
          (((a : ℝ) / (a - 1)) *
              ∏ p ∈ s, (p : ℝ) / (p - 1)) ^ 5 =
              ((a : ℝ) / (a - 1)) ^ 5 *
                (∏ p ∈ s, (p : ℝ) / (p - 1)) ^ 5 := by ring
          _ ≤ ((a : ℝ) / (a - 1)) ^ 5 *
                (8 * (s.card : ℝ) ^ 2) := by
            exact mul_le_mul_of_nonneg_left hih (pow_nonneg hafac_nonneg 5)
          _ ≤ 8 * ((s.card + 1 : ℕ) : ℝ) ^ 2 := hstep
      · have hs0 : s = ∅ := not_nonempty_iff_eq_empty.mp hsne
        subst s
        have ha2le := ha.two_le
        have ha3 : 3 ≤ a := by omega
        have ha3R : (3 : ℝ) ≤ a := by exact_mod_cast ha3
        have hden : (0 : ℝ) < a - 1 := by
          nlinarith
        have hratio : (a : ℝ) / (a - 1) ≤ (3 : ℝ) / 2 := by
          rw [div_le_iff₀ hden]
          nlinarith
        have hnonneg : 0 ≤ (a : ℝ) / (a - 1) := by positivity
        have hp := pow_le_pow_left₀ hnonneg hratio 5
        have hfinal := hp.trans (by norm_num : ((3 : ℝ) / 2) ^ 5 ≤ 8)
        simpa using hfinal

/-- The finite product estimate underlying the elementary proof of convergence
of Romanoff's series. -/
theorem oddPrimeProduct_fifth_le (P : Finset ℕ) (hPne : P.Nonempty)
    (hP : ∀ p ∈ P, p.Prime ∧ Odd p) :
    (∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 1)) ^ 5 ≤ 8 * (P.card : ℝ) ^ 2 := by
  apply oddPrimeProduct_fifth_le_ne_two P (fun p hp ↦ (hP p hp).1)
  · intro p hp hp2
    obtain ⟨k, hk⟩ := (hP p hp).2
    omega
  · exact hPne

end Erdos851
