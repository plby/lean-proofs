/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import Mathlib

/-!
# Arithmetic helpers for Erdős Problem 58

This file collects the elementary natural-number facts used in the proof of
Gyárfás's odd-cycle theorem: strict growth of positive prefix sums, the
two-class pigeonhole principle, ceiling-half identities, and the elementary
sumset-chain estimate.
-/

namespace Erdos58

open scoped BigOperators Pointwise

namespace Arithmetic

/-- The ceiling of `n / 2`, expressed without leaving the natural numbers. -/
def ceilHalf (n : ℕ) : ℕ :=
  (n + 1) / 2

@[simp] theorem ceilHalf_zero : ceilHalf 0 = 0 := by
  simp [ceilHalf]

@[simp] theorem ceilHalf_two_mul (n : ℕ) : ceilHalf (2 * n) = n := by
  unfold ceilHalf
  rw [Nat.mul_add_div (by omega : 0 < 2)]
  norm_num

@[simp] theorem ceilHalf_two_mul_add_one (n : ℕ) : ceilHalf (2 * n + 1) = n + 1 := by
  unfold ceilHalf
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) + 0 by omega]
  rw [Nat.mul_add_div (by omega : 0 < 2)]

/-- The ceiling-half function is monotone. -/
theorem ceilHalf_mono : Monotone ceilHalf := by
  intro m n hmn
  unfold ceilHalf
  omega

/-- A useful closed form for natural-number ceiling halves. -/
theorem ceilHalf_eq_div_add_mod (n : ℕ) : ceilHalf n = n / 2 + n % 2 := by
  unfold ceilHalf
  omega

/-- The exact numerical identity appearing at the end of inequality (7) in
Gyárfás's proof. -/
theorem ceilHalf_two_mul_sub_add (j q : ℕ) (hq : q ≤ 2 * j) :
    ceilHalf (2 * j - q) + q = j + ceilHalf q := by
  unfold ceilHalf
  omega

/-- Inequality (7): if `p ≥ 2j-q`, then
`⌈p/2⌉ + q ≥ j + ⌈q/2⌉`. -/
theorem gyarfas_inequality_seven {j p q : ℕ} (hq : q ≤ 2 * j)
    (hp : 2 * j - q ≤ p) :
    j + ceilHalf q ≤ ceilHalf p + q := by
  rw [← ceilHalf_two_mul_sub_add j q hq]
  exact Nat.add_le_add_right (ceilHalf_mono hp) q

/-- Inequality (7), in the form in which its hypothesis arises from the
endpoint degree count.  This version also covers the automatic case
`2j < q`. -/
theorem gyarfas_inequality_seven_of_le_add {j p q : ℕ} (hpq : 2 * j ≤ p + q) :
    j + ceilHalf q ≤ ceilHalf p + q := by
  by_cases hq : q ≤ 2 * j
  · exact gyarfas_inequality_seven hq (by omega)
  · unfold ceilHalf
    omega

/-- The exact numerical identity at the lower endpoint in inequality (8). -/
theorem ceilHalf_two_mul_sub_sub_one_add (j q : ℕ) (hq : q ≤ 2 * j) :
    ceilHalf (2 * j - q - 1) + q = j + q / 2 := by
  unfold ceilHalf
  omega

/-- Inequality (8): if `p ≥ 2j-q`, then
`⌈(p-1)/2⌉ + q ≥ j + ⌊q/2⌋`. -/
theorem gyarfas_inequality_eight {j p q : ℕ} (hq : q ≤ 2 * j)
    (hp : 2 * j - q ≤ p) :
    j + q / 2 ≤ ceilHalf (p - 1) + q := by
  rw [← ceilHalf_two_mul_sub_sub_one_add j q hq]
  exact Nat.add_le_add_right (ceilHalf_mono (Nat.sub_le_sub_right hp 1)) q

/-- Inequality (8), directly from `2j ≤ p+q`. -/
theorem gyarfas_inequality_eight_of_le_add {j p q : ℕ} (hpq : 2 * j ≤ p + q) :
    j + q / 2 ≤ ceilHalf (p - 1) + q := by
  by_cases hq : q ≤ 2 * j
  · exact gyarfas_inequality_eight hq (by omega)
  · unfold ceilHalf
    omega

/-- The lower bound in (8) is strict once `q ≥ 2`. -/
theorem gyarfas_inequality_eight_strict {j p q : ℕ} (hq : q ≤ 2 * j)
    (hp : 2 * j - q ≤ p) (hq2 : 2 ≤ q) :
    j < ceilHalf (p - 1) + q := by
  have h := gyarfas_inequality_eight hq hp
  omega

/-- The direct-hypothesis form of strictness in (8). -/
theorem gyarfas_inequality_eight_strict_of_le_add {j p q : ℕ}
    (hpq : 2 * j ≤ p + q) (hq2 : 2 ≤ q) :
    j < ceilHalf (p - 1) + q := by
  have h := gyarfas_inequality_eight_of_le_add hpq
  omega

/-- Prefix sums of a positive sequence of natural numbers are strictly
increasing. -/
theorem strictMono_sum_range_of_pos {a : ℕ → ℕ} (ha : ∀ i, 0 < a i) :
    StrictMono fun n ↦ ∑ i ∈ Finset.range n, a i := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [Finset.sum_range_succ]
  exact Nat.lt_add_of_pos_right (ha n)

/-- A bounded version of strict growth of prefix sums.  It is convenient
when positivity is known only up to a fixed endpoint. -/
theorem sum_range_lt_sum_range_of_pos {a : ℕ → ℕ} {i j : ℕ} (hij : i < j)
    (ha : ∀ r < j, 0 < a r) :
    (∑ r ∈ Finset.range i, a r) < ∑ r ∈ Finset.range j, a r := by
  have hle : (∑ r ∈ Finset.range i, a r) ≤ ∑ r ∈ Finset.range (j - 1), a r := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun _ _ _ ↦ Nat.zero_le _)
  calc
    (∑ r ∈ Finset.range i, a r) ≤ ∑ r ∈ Finset.range (j - 1), a r := hle
    _ < (∑ r ∈ Finset.range (j - 1), a r) + a (j - 1) :=
      Nat.lt_add_of_pos_right (ha (j - 1) (by omega))
    _ = ∑ r ∈ Finset.range j, a r := by
      rw [← Finset.sum_range_succ]
      congr
      omega

/-- Strict growth of prefix sums stated directly for lists. -/
theorem list_sum_take_lt_sum_take_of_pos {l : List ℕ} {i j : ℕ}
    (hij : i < j) (hj : j ≤ l.length) (hl : ∀ x ∈ l, 0 < x) :
    (l.take i).sum < (l.take j).sum := by
  induction l generalizing i j with
  | nil =>
      simp at hj
      omega
  | cons x xs ih =>
      cases i with
      | zero =>
          cases j with
          | zero => omega
          | succ j =>
              simp only [List.take_zero, List.sum_nil, List.take_succ_cons, List.sum_cons]
              exact Nat.add_pos_left (hl x (by simp)) _
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              simp only [List.take_succ_cons, List.sum_cons]
              apply Nat.add_lt_add_left
              apply ih
              · omega
              · simpa using hj
              · intro y hy
                exact hl y (by simp [hy])

/-- In any partition of a finite set into two classes, one class has at
least `⌈|s|/2⌉` members. -/
theorem card_filter_ge_ceilHalf_or_card_filter_neg_ge_ceilHalf
    { α : Type* } [DecidableEq α] (s : Finset α) (P : α → Prop) [DecidablePred P] :
    ceilHalf s.card ≤ (s.filter P).card ∨
      ceilHalf s.card ≤ (s.filter fun x ↦ ¬ P x).card := by
  have hcard : (s.filter P).card + (s.filter fun x ↦ ¬ P x).card = s.card := by
    rw [Finset.card_filter_add_card_filter_not]
  unfold ceilHalf
  omega

/-- Among `2j+1` objects colored with two colors, `j+1` have one color. -/
theorem card_filter_ge_succ_or_card_filter_neg_ge_succ
    { α : Type* } [DecidableEq α] {s : Finset α} {j : ℕ}
    (P : α → Prop) [DecidablePred P] (hs : s.card = 2 * j + 1) :
    j + 1 ≤ (s.filter P).card ∨
      j + 1 ≤ (s.filter fun x ↦ ¬ P x).card := by
  simpa [hs] using card_filter_ge_ceilHalf_or_card_filter_neg_ge_ceilHalf s P

/-- The parity specialization of the two-class pigeonhole principle. -/
theorem card_even_ge_ceilHalf_or_card_odd_ge_ceilHalf (s : Finset ℕ) :
    ceilHalf s.card ≤ (s.filter Even).card ∨
      ceilHalf s.card ≤ (s.filter Odd).card := by
  simpa only [Nat.not_even_iff_odd] using
    (card_filter_ge_ceilHalf_or_card_filter_neg_ge_ceilHalf s Even)

/-- Among `2j+1` natural numbers, at least `j+1` have a common parity. -/
theorem card_even_ge_succ_or_card_odd_ge_succ
    {s : Finset ℕ} {j : ℕ} (hs : s.card = 2 * j + 1) :
    j + 1 ≤ (s.filter Even).card ∨ j + 1 ≤ (s.filter Odd).card := by
  simpa [hs] using card_even_ge_ceilHalf_or_card_odd_ge_ceilHalf s

/-- The elementary sumset-chain bound `|A+B| ≥ |A|+|B|-1`, stated for
strictly increasing nonempty lists. -/
theorem card_list_sumset_ge_add_sub_one {l m : List ℕ}
    (hlne : l ≠ []) (hmne : m ≠ [])
    (hl : l.Pairwise (· < ·)) (hm : m.Pairwise (· < ·)) :
    l.length + m.length - 1 ≤ (l.toFinset + m.toFinset).card := by
  have hlnd : l.Nodup := hl.imp fun h ↦ h.ne
  have hmnd : m.Nodup := hm.imp fun h ↦ h.ne
  have hlnonempty : l.toFinset.Nonempty := by
    simpa only [List.toFinset_nonempty_iff] using hlne
  have hmnonempty : m.toFinset.Nonempty := by
    simpa only [List.toFinset_nonempty_iff] using hmne
  rw [← List.toFinset_card_of_nodup hlnd, ← List.toFinset_card_of_nodup hmnd]
  exact cauchy_davenport_add_of_linearOrder_isCancelAdd hlnonempty hmnonempty

end Arithmetic

end Erdos58
