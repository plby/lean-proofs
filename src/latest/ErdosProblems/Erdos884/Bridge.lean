/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 884.
Informal proof: Daniel Larsen, building on Terence Tao's construction.
Formal proof: Claude Fable 5, with minor guidance from R. J. Honicky.
Source: https://www.erdosproblems.com/884#post-7362
https://github.com/honicky/erdos884/tree/323e9a01306df1e094b434beaa48c018370fe258
Original Lean/Mathlib version: 4.31.0.
Original Mathlib commit: fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.
The port reuses the repository's existing PNT+ Selberg sieve by Arend Mellendijk.
-/
import ErdosProblems.Erdos884.PairSieveCore

set_option linter.mathlibStandardSet false

/-!
# Erdős Problem 884 — bridge to the official formal-conjectures statement

The two `abbrev`s below are VERBATIM the definitions from
google-deepmind/formal-conjectures `ErdosProblems/884.lean`.  We identify them (for `n ≠ 0`)
with `pairSum n.divisors` and `gapSum n.divisors` from the shared interface, using that
`Nat.nth (· ∣ n)` is the increasing enumeration of `n.divisors`.
-/

namespace Erdos884

/-! ### `Nat.nth (· ∣ n)` enumerates `n.divisors` -/

private lemma finite_dvd {n : ℕ} (hn : n ≠ 0) : (Set.ofPred (· ∣ n)).Finite :=
  (Set.finite_Iic n).subset fun _ hd => Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd

private lemma toFinset_dvd {n : ℕ} (hn : n ≠ 0) (hf : (Set.ofPred (· ∣ n)).Finite) :
    hf.toFinset = n.divisors := by
  ext d
  simp [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Nat.mem_divisors, hn]

private lemma lt_card_dvd {n : ℕ} (hn : n ≠ 0) {i : ℕ} (hi : i < n.divisors.card) :
    ∀ hf : (Set.ofPred (· ∣ n)).Finite, i < hf.toFinset.card := fun hf => by
  rw [toFinset_dvd hn hf]; exact hi

private lemma nth_dvd_mem {n : ℕ} (hn : n ≠ 0) {i : ℕ} (hi : i < n.divisors.card) :
    Nat.nth (· ∣ n) i ∈ n.divisors :=
  Nat.mem_divisors.2 ⟨Nat.nth_mem i (lt_card_dvd hn hi), hn⟩

private lemma nth_dvd_lt {n : ℕ} (hn : n ≠ 0) {i j : ℕ} (hij : i < j)
    (hj : j < n.divisors.card) :
    Nat.nth (· ∣ n) i < Nat.nth (· ∣ n) j :=
  Nat.nth_lt_nth_of_lt_card (finite_dvd hn) hij (by rw [toFinset_dvd hn]; exact hj)

private lemma count_dvd_lt_card {n : ℕ} (hn : n ≠ 0) {d : ℕ} (hd : d ∈ n.divisors) :
    Nat.count (· ∣ n) d < n.divisors.card := by
  have h := Nat.count_lt_card (finite_dvd hn) (Nat.mem_divisors.1 hd).1
  rwa [toFinset_dvd hn] at h

private lemma nth_count_dvd {n d : ℕ} (hd : d ∈ n.divisors) :
    Nat.nth (· ∣ n) (Nat.count (· ∣ n) d) = d :=
  Nat.nth_count (Nat.mem_divisors.1 hd).1

private lemma count_nth_dvd {n : ℕ} (hn : n ≠ 0) {i : ℕ} (hi : i < n.divisors.card) :
    Nat.count (· ∣ n) (Nat.nth (· ∣ n) i) = i :=
  Nat.count_nth (lt_card_dvd hn hi)

private lemma count_dvd_lt_count {n : ℕ} (hn : n ≠ 0) {a b : ℕ} (ha : a ∈ n.divisors)
    (hb : b ∈ n.divisors) (hab : a < b) :
    Nat.count (· ∣ n) a < Nat.count (· ∣ n) b := by
  by_contra h
  push Not at h
  have h1 : Nat.nth (· ∣ n) (Nat.count (· ∣ n) b) ≤ Nat.nth (· ∣ n) (Nat.count (· ∣ n) a) := by
    rcases eq_or_lt_of_le h with heq | hlt
    · rw [heq]
    · exact (nth_dvd_lt hn hlt (count_dvd_lt_card hn ha)).le
  rw [nth_count_dvd hb, nth_count_dvd ha] at h1
  omega

/-! ### The pairwise bridge -/

theorem sumDivisorInvPairwiseDifference_eq {n : ℕ} (hn : n ≠ 0) :
    sumDivisorInvPairwiseDifference n = pairSum n.divisors := by
  classical
  have h1 : sumDivisorInvPairwiseDifference n =
      ∑ j ∈ Finset.range n.divisors.card, ∑ i ∈ Finset.range j,
        invGap (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) j) := by
    simp only [sumDivisorInvPairwiseDifference, Rat.cast_one, one_div]
    exact Eq.trans
      (Finset.sum_congr rfl fun j _ => Fin.sum_univ_eq_sum_range
        (fun i => invGap (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) (j : ℕ))) (j : ℕ))
      (Fin.sum_univ_eq_sum_range
        (fun j => ∑ i ∈ Finset.range j, invGap (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) j))
        n.divisors.card)
  rw [h1, Finset.sum_sigma']
  unfold pairSum pairSumOn
  refine Finset.sum_nbij'
      (fun x : (_ : ℕ) × ℕ => (Nat.nth (· ∣ n) x.2, Nat.nth (· ∣ n) x.1))
      (fun p : ℕ × ℕ => ⟨Nat.count (· ∣ n) p.2, Nat.count (· ∣ n) p.1⟩)
      ?_ ?_ ?_ ?_ (fun x _ => rfl)
  · rintro ⟨j, i⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [Finset.mem_filter, Finset.mem_product, and_true]
    exact ⟨⟨nth_dvd_mem hn (hx.2.trans hx.1), nth_dvd_mem hn hx.1⟩,
      nth_dvd_lt hn hx.2 hx.1⟩
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, and_true] at hp
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    simp only [Finset.mem_sigma, Finset.mem_range]
    exact ⟨count_dvd_lt_card hn hb, count_dvd_lt_count hn ha hb hab⟩
  · rintro ⟨j, i⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [count_nth_dvd hn hx.1, count_nth_dvd hn (hx.2.trans hx.1)]
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, and_true] at hp
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    simp only [nth_count_dvd ha, nth_count_dvd hb]

/-! ### The consecutive bridge -/

theorem sumDivisorInvConsecutiveDifference_eq {n : ℕ} (hn : n ≠ 0) :
    sumDivisorInvConsecutiveDifference n = gapSum n.divisors := by
  classical
  have h1 : sumDivisorInvConsecutiveDifference n =
      ∑ i ∈ Finset.range (n.divisors.card - 1),
        invGap (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) (i + 1)) := by
    simp only [sumDivisorInvConsecutiveDifference, Rat.cast_one, one_div]
    exact Fin.sum_univ_eq_sum_range
      (fun i => invGap (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) (i + 1))) _
  rw [h1]
  unfold gapSum pairSumOn
  refine Finset.sum_nbij'
      (fun i : ℕ => (Nat.nth (· ∣ n) i, Nat.nth (· ∣ n) (i + 1)))
      (fun p : ℕ × ℕ => Nat.count (· ∣ n) p.1)
      ?_ ?_ ?_ ?_ (fun x _ => rfl)
  · intro i hi
    rw [Finset.mem_range] at hi
    have hi1 : i + 1 < n.divisors.card := by omega
    have hi0 : i < n.divisors.card := by omega
    have hcons : IsConsecutive n.divisors (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) (i + 1)) := by
      refine ⟨nth_dvd_mem hn hi0, nth_dvd_mem hn hi1, nth_dvd_lt hn (by omega) hi1, ?_⟩
      rintro c hc ⟨h1c, h2c⟩
      have e1 : i < Nat.count (· ∣ n) c := by
        have h := count_dvd_lt_count hn (nth_dvd_mem hn hi0) hc h1c
        rwa [count_nth_dvd hn hi0] at h
      have e2 : Nat.count (· ∣ n) c < i + 1 := by
        have h := count_dvd_lt_count hn hc (nth_dvd_mem hn hi1) h2c
        rwa [count_nth_dvd hn hi1] at h
      omega
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨nth_dvd_mem hn hi0, nth_dvd_mem hn hi1⟩, nth_dvd_lt hn (by omega) hi1, hcons⟩
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ha, hb⟩, hab, -⟩ := hp
    simp only [Finset.mem_range]
    have h1 := count_dvd_lt_count hn ha hb hab
    have h2 := count_dvd_lt_card hn hb
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    simp only [count_nth_dvd hn (show i < n.divisors.card by omega)]
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ha, hb⟩, hab, hcons⟩ := hp
    have hca : Nat.count (· ∣ n) a < Nat.count (· ∣ n) b := count_dvd_lt_count hn ha hb hab
    have hcb : Nat.count (· ∣ n) b < n.divisors.card := count_dvd_lt_card hn hb
    have hkey : Nat.count (· ∣ n) a + 1 = Nat.count (· ∣ n) b := by
      by_contra hne
      have hlt : Nat.count (· ∣ n) a + 1 < Nat.count (· ∣ n) b := by omega
      have hmem' : Nat.nth (· ∣ n) (Nat.count (· ∣ n) a + 1) ∈ n.divisors :=
        nth_dvd_mem hn (by omega)
      have hgt : a < Nat.nth (· ∣ n) (Nat.count (· ∣ n) a + 1) := by
        conv_lhs => rw [← nth_count_dvd ha]
        exact nth_dvd_lt hn (by omega) (by omega)
      have hlt2 : Nat.nth (· ∣ n) (Nat.count (· ∣ n) a + 1) < b := by
        conv_rhs => rw [← nth_count_dvd hb]
        exact nth_dvd_lt hn hlt hcb
      exact hcons.2.2.2 _ hmem' ⟨hgt, hlt2⟩
    simp only [nth_count_dvd ha, hkey, nth_count_dvd hb]

/-! ### Nonnegativity corollaries -/

theorem sumDivisorInvPairwise_nonneg (n : ℕ) (hn : n ≠ 0) :
    0 ≤ sumDivisorInvPairwiseDifference n := by
  rw [sumDivisorInvPairwiseDifference_eq hn]
  exact pairSum_nonneg _

theorem sumDivisorInvConsecutive_nonneg (n : ℕ) (hn : n ≠ 0) :
    0 ≤ sumDivisorInvConsecutiveDifference n := by
  rw [sumDivisorInvConsecutiveDifference_eq hn]
  exact gapSum_nonneg _

end Erdos884
