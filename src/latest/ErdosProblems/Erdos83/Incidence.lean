import Mathlib

/-!
# Incidence and binomial-coefficient helpers for Erdős Problem 83

This file contains the finite double-counting lemma used at the central
defect level, together with cross-multiplied forms of the elementary ratios
between adjacent binomial coefficients.  All statements take values in
`ℕ`, so downstream proofs do not need division or casts.
-/

open scoped BigOperators
open Finset

namespace Erdos83

/-- A nonempty finite set contains a point whose value is at least the
average, in division-free form. -/
lemma exists_card_mul_value_ge_sum {T : Type*} [Fintype T] [Nonempty T]
    (f : T → ℕ) :
    ∃ z ∈ (Finset.univ : Finset T),
      Fintype.card T * f z ≥ ∑ x : T, f x := by
  by_contra h
  push_neg at h
  have hlt :
      ∑ z : T, Fintype.card T * f z <
        ∑ _z : T, ∑ x : T, f x := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun z _hz ↦ h z (Finset.mem_univ z))
  have hleft :
      ∑ z : T, Fintype.card T * f z =
        Fintype.card T * ∑ z : T, f z := by
    rw [Finset.mul_sum]
  have hright :
      ∑ _z : T, ∑ x : T, f x =
        Fintype.card T * ∑ x : T, f x := by simp
  rw [hleft, hright] at hlt
  exact (Nat.lt_irrefl _ hlt)

/-- Incidence averaging for a uniform finite family of finite sets.

If every member of `P` has `r` elements, then some point lies in at least
the average number of members.  The conclusion is cross-multiplied so that
it remains a statement in `ℕ`. -/
theorem exists_incidence_ge_average {T : Type*} [Fintype T] [DecidableEq T]
    [Nonempty T] (P : Finset (Finset T)) (r : ℕ)
    (hcard : ∀ C ∈ P, C.card = r) :
    ∃ z ∈ (Finset.univ : Finset T),
      Fintype.card T * (P.filter fun C ↦ z ∈ C).card ≥ r * P.card := by
  have hdouble :
      ∑ z : T, (P.filter fun C ↦ z ∈ C).card = r * P.card := by
    calc
      ∑ z : T, (P.filter fun C ↦ z ∈ C).card =
          ∑ z : T, ∑ C ∈ P, if z ∈ C then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro z _hz
            simp
      _ = ∑ C ∈ P, ∑ z : T, if z ∈ C then 1 else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ C ∈ P, C.card := by
            apply Finset.sum_congr rfl
            intro C _hC
            simp
      _ = ∑ _C ∈ P, r := by
            apply Finset.sum_congr rfl
            intro C hC
            exact hcard C hC
      _ = r * P.card := by simp [Nat.mul_comm]
  obtain ⟨z, hz, hzavg⟩ :=
    exists_card_mul_value_ge_sum
      (fun z : T ↦ (P.filter fun C ↦ z ∈ C).card)
  exact ⟨z, hz, hdouble ▸ hzavg⟩

/-- The ratio between two binomial coefficients with consecutive upper
indices, written without division. -/
lemma choose_succ_left_cross (n k : ℕ) :
    Nat.choose (n + 1) k * (n + 1 - k) =
      Nat.choose n k * (n + 1) := by
  exact (Nat.choose_mul_succ_eq n k).symm

/-- The ratio between adjacent lower indices of a binomial coefficient,
written without division. -/
lemma choose_succ_right_cross (n k : ℕ) :
    Nat.choose n (k + 1) * (k + 1) =
      Nat.choose n k * (n - k) := by
  exact Nat.choose_succ_right_eq n k

/-- Multiplying the two adjacent-lower-index identities gives a convenient
cross-product identity for two binomial coefficients. -/
lemma choose_adjacent_product_cross (n a b : ℕ) :
    Nat.choose n a * Nat.choose n b * ((n - a) * (n - b)) =
      Nat.choose n (a + 1) * Nat.choose n (b + 1) *
        ((a + 1) * (b + 1)) := by
  have ha := Nat.choose_succ_right_eq n a
  have hb := Nat.choose_succ_right_eq n b
  calc
    Nat.choose n a * Nat.choose n b * ((n - a) * (n - b)) =
        (Nat.choose n a * (n - a)) *
          (Nat.choose n b * (n - b)) := by ac_rfl
    _ = (Nat.choose n (a + 1) * (a + 1)) *
          (Nat.choose n (b + 1) * (b + 1)) := by rw [← ha, ← hb]
    _ = Nat.choose n (a + 1) * Nat.choose n (b + 1) *
          ((a + 1) * (b + 1)) := by ac_rfl

/-- When `a + b = n + 2`, each adjacent-binomial identity can be expressed
using the complementary defect level. -/
lemma choose_mul_index_eq_choose_pred_mul_complement
    {n a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = n + 2) :
    Nat.choose n a * a = Nat.choose n (a - 1) * (b - 1) := by
  have ha_index : a - 1 + 1 = a := by omega
  have hcomplement : n - (a - 1) = b - 1 := by omega
  simpa only [ha_index, hcomplement] using
    (Nat.choose_succ_right_eq n (a - 1))

/-- The numerical contradiction at noncentral defect levels, separated from
the combinatorial replacement argument.  In fact the strict inequality is
valid for every pair of positive complementary levels. -/
lemma choose_product_lt_pred_product_of_add_eq
    {n a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = n + 2) :
    Nat.choose n a * Nat.choose n b <
      Nat.choose n (a - 1) * Nat.choose n (b - 1) := by
  have han : a - 1 ≤ n := by omega
  have hbn : b - 1 ≤ n := by omega
  have hpred_pos :
      0 < Nat.choose n (a - 1) * Nat.choose n (b - 1) :=
    Nat.mul_pos (Nat.choose_pos han) (Nat.choose_pos hbn)
  have hfactor : (a - 1) * (b - 1) < a * b := by
    refine lt_of_le_of_lt (Nat.mul_le_mul_right (b - 1) (Nat.sub_le a 1)) ?_
    exact Nat.mul_lt_mul_of_pos_left (by omega) ha
  have ha' := choose_mul_index_eq_choose_pred_mul_complement ha hb hab
  have hb' := choose_mul_index_eq_choose_pred_mul_complement
    (n := n) (a := b) (b := a) hb ha (by omega)
  have hmul :
      (Nat.choose n a * Nat.choose n b) * (a * b) =
        (Nat.choose n (a - 1) * Nat.choose n (b - 1)) *
          ((a - 1) * (b - 1)) := by
    calc
      (Nat.choose n a * Nat.choose n b) * (a * b) =
          (Nat.choose n a * a) * (Nat.choose n b * b) := by ac_rfl
      _ = (Nat.choose n (a - 1) * (b - 1)) *
          (Nat.choose n (b - 1) * (a - 1)) := by rw [ha', hb']
      _ = (Nat.choose n (a - 1) * Nat.choose n (b - 1)) *
          ((a - 1) * (b - 1)) := by ac_rfl
  by_contra hnot
  have hle :
      Nat.choose n (a - 1) * Nat.choose n (b - 1) ≤
        Nat.choose n a * Nat.choose n b := Nat.le_of_not_gt hnot
  have hle' := Nat.mul_le_mul_right (a * b) hle
  rw [hmul] at hle'
  exact (Nat.not_le_of_gt (Nat.mul_lt_mul_of_pos_left hfactor hpred_pos)) hle'

/-- Transfer a cross-multiplied strict inequality through the ratio between
`choose (n + 1) k` and `choose n k`.  This is the division-free central-level
estimate used after incidence averaging. -/
lemma choose_succ_left_mul_lt_of_cross_lt
    {n k x y : ℕ} (hk : k ≤ n)
    (hxy : y * (n + 1 - k) < x * (n + 1)) :
    Nat.choose n k * y < Nat.choose (n + 1) k * x := by
  have hchoose_pos : 0 < Nat.choose n k := Nat.choose_pos hk
  have hscaled :
      Nat.choose n k * (y * (n + 1 - k)) <
        Nat.choose n k * (x * (n + 1)) :=
    Nat.mul_lt_mul_of_pos_left hxy hchoose_pos
  have hcross := choose_succ_left_cross n k
  apply Nat.lt_of_mul_lt_mul_right (a := n + 1 - k)
  calc
    (Nat.choose n k * y) * (n + 1 - k) =
        Nat.choose n k * (y * (n + 1 - k)) := by ac_rfl
    _ < Nat.choose n k * (x * (n + 1)) := hscaled
    _ = (Nat.choose n k * (n + 1)) * x := by ac_rfl
    _ = (Nat.choose (n + 1) k * (n + 1 - k)) * x :=
      congrArg (fun q : ℕ ↦ q * x) hcross.symm
    _ = (Nat.choose (n + 1) k * x) * (n + 1 - k) := by ac_rfl

/-- Cross-cancel the positive multiplicities in the two inequalities arising
from the two noncentral defect replacements. -/
lemma mul_mul_le_mul_mul_of_cross_bounds
    {A B C D x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h₁ : A * x ≤ B * y) (h₂ : C * y ≤ D * x) :
    A * C ≤ B * D := by
  have hxy : 0 < x * y := Nat.mul_pos hx hy
  have hprod : (A * x) * (C * y) ≤ (B * y) * (D * x) :=
    Nat.mul_le_mul h₁ h₂
  have hfactored : (x * y) * (A * C) ≤ (x * y) * (B * D) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hprod
  exact Nat.le_of_mul_le_mul_left hfactored hxy

end Erdos83
