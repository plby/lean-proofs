/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.MassProducts
import Mathlib.Data.List.Rotate
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Erdős Problem 446: the cyclic composition identity

Ford's lower bound uses the fact that the reciprocal penalties of all cyclic
rotations of a composition add to one.  We first prove the underlying exact
identity for an arbitrary positive real list of product one.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Sum of all nonempty initial products of a list. -/
def prefixProductMass : List ℝ → ℝ
  | [] => 0
  | x :: xs => x * (1 + prefixProductMass xs)

/-- Sum of all proper initial products, including the empty product. -/
def properPrefixProductMass : List ℝ → ℝ
  | [] => 0
  | x :: xs => 1 + x * properPrefixProductMass xs

@[simp] theorem prefixProductMass_nil : prefixProductMass [] = 0 := rfl

@[simp] theorem prefixProductMass_cons (x : ℝ) (xs : List ℝ) :
    prefixProductMass (x :: xs) = x * (1 + prefixProductMass xs) := rfl

@[simp] theorem properPrefixProductMass_nil :
    properPrefixProductMass [] = 0 := rfl

@[simp] theorem properPrefixProductMass_cons (x : ℝ) (xs : List ℝ) :
    properPrefixProductMass (x :: xs) =
      1 + x * properPrefixProductMass xs := rfl

theorem prefixProductMass_append (u v : List ℝ) :
    prefixProductMass (u ++ v) =
      prefixProductMass u + u.prod * prefixProductMass v := by
  induction u with
  | nil => simp
  | cons x u ih =>
      simp only [List.cons_append, prefixProductMass_cons, List.prod_cons, ih]
      ring

theorem prefixProductMass_eq_proper_add_prod_sub_one (l : List ℝ) :
    prefixProductMass l =
      properPrefixProductMass l + l.prod - 1 := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [prefixProductMass_cons, properPrefixProductMass_cons,
        List.prod_cons, ih]
      ring

theorem properPrefixProductMass_eq_sum_take (l : List ℝ) :
    properPrefixProductMass l =
      ∑ r ∈ Finset.range l.length, (l.take r).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [properPrefixProductMass_cons, List.length_cons,
        Finset.sum_range_succ']
      simp only [List.take_zero, List.prod_nil, List.take_succ_cons,
        List.prod_cons, one_mul, ih, Finset.mul_sum]
      ring

theorem properPrefixProductMass_append (u v : List ℝ) :
    properPrefixProductMass (u ++ v) =
      properPrefixProductMass u + u.prod * properPrefixProductMass v := by
  induction u with
  | nil => simp
  | cons x u ih =>
      simp only [List.cons_append, properPrefixProductMass_cons,
        List.prod_cons, ih]
      ring

theorem properPrefixProductMass_nonneg {l : List ℝ}
    (hpos : ∀ x ∈ l, 0 ≤ x) : 0 ≤ properPrefixProductMass l := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [properPrefixProductMass_cons]
      exact add_nonneg zero_le_one
        (mul_nonneg (hpos x (by simp))
          (ih fun y hy ↦ hpos y (by simp [hy])))

theorem one_le_properPrefixProductMass {l : List ℝ} (hl : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) : 1 ≤ properPrefixProductMass l := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  rw [properPrefixProductMass_cons]
  have htail : 0 ≤ properPrefixProductMass xs :=
    properPrefixProductMass_nonneg fun y hy ↦
      (hpos y (by simp [hy])).le
  exact le_add_of_nonneg_right
    (mul_nonneg (hpos x (by simp)).le htail)

theorem prefixProductMass_nonneg {l : List ℝ}
    (hpos : ∀ x ∈ l, 0 ≤ x) : 0 ≤ prefixProductMass l := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [prefixProductMass_cons]
      exact mul_nonneg (hpos x (by simp))
        (by have := ih (fun y hy ↦ hpos y (by simp [hy])); linarith)

theorem prefixProductMass_pos {l : List ℝ} (hl : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) : 0 < prefixProductMass l := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  rw [prefixProductMass_cons]
  have hx : 0 < x := hpos x (by simp)
  have htail : 0 ≤ prefixProductMass xs :=
    prefixProductMass_nonneg fun y hy ↦
      (hpos y (by simp [hy])).le
  positivity

theorem prefixProductMass_rotate_div {l : List ℝ}
    (hprod : l.prod = 1) (hpos : ∀ x ∈ l, 0 < x)
    {r : ℕ} (hr : r < l.length) :
    prefixProductMass (l.rotate r) =
      prefixProductMass l / (l.take r).prod := by
  let v := l.take r
  let u := l.drop r
  have hlSplit : v ++ u = l := by
    exact List.take_append_drop r l
  have hrotate : l.rotate r = u ++ v := by
    exact List.rotate_eq_drop_append_take hr.le
  have hvPos : 0 < v.prod := by
    apply List.prod_pos
    intro x hx
    exact hpos x (List.mem_of_mem_take hx)
  have huvProd : v.prod * u.prod = 1 := by
    rw [← List.prod_append, hlSplit, hprod]
  have hmul : v.prod * prefixProductMass (u ++ v) =
      prefixProductMass (v ++ u) := by
    rw [prefixProductMass_append, prefixProductMass_append]
    calc
      v.prod * (prefixProductMass u + u.prod * prefixProductMass v) =
          v.prod * prefixProductMass u +
            (v.prod * u.prod) * prefixProductMass v := by ring
      _ = v.prod * prefixProductMass u + prefixProductMass v := by
        rw [huvProd, one_mul]
      _ = prefixProductMass v + v.prod * prefixProductMass u := by ring
  have hdiv : prefixProductMass (u ++ v) =
      prefixProductMass (v ++ u) / v.prod :=
    (eq_div_iff hvPos.ne').2 (by simpa [mul_comm] using hmul)
  simpa only [hrotate, hlSplit, v] using hdiv

/-- The upper half of Ford's cyclic inequality for a list whose product is
at most one. -/
theorem sum_inv_prefixProductMass_rotate_le_inv_prod {l : List ℝ}
    (hl : l ≠ []) (hpos : ∀ x ∈ l, 0 < x) (hprodLe : l.prod ≤ 1) :
    (∑ r ∈ Finset.range l.length,
      1 / prefixProductMass (l.rotate r)) ≤ 1 / l.prod := by
  have hprodPos : 0 < l.prod := by
    apply List.prod_pos
    exact hpos
  have hproperPos : 0 < properPrefixProductMass l :=
    lt_of_lt_of_le zero_lt_one (one_le_properPrefixProductMass hl hpos)
  have hterm : ∀ r ∈ Finset.range l.length,
      1 / prefixProductMass (l.rotate r) ≤
        (l.take r).prod /
          (l.prod * properPrefixProductMass l) := by
    intro r hr
    have hrlt := Finset.mem_range.mp hr
    let v := l.take r
    let u := l.drop r
    have hsplit : v ++ u = l := List.take_append_drop r l
    have huNe : u ≠ [] := by
      intro hu
      have hlen : l.length - r = 0 := by
        simpa only [u, List.length_drop, List.length_nil] using
          congrArg List.length hu
      omega
    have hvPos : 0 < v.prod := by
      apply List.prod_pos
      intro x hx
      exact hpos x (List.mem_of_mem_take hx)
    have huPos : 0 < u.prod := by
      apply List.prod_pos
      intro x hx
      exact hpos x (List.mem_of_mem_drop hx)
    have huProper : 1 ≤ properPrefixProductMass u := by
      apply one_le_properPrefixProductMass huNe
      intro x hx
      exact hpos x (List.mem_of_mem_drop hx)
    have hprodSplit : v.prod * u.prod = l.prod := by
      rw [← List.prod_append, hsplit]
    have hproperSplit : properPrefixProductMass l =
        properPrefixProductMass v +
          v.prod * properPrefixProductMass u := by
      rw [← hsplit, properPrefixProductMass_append]
    have hrotate : l.rotate r = u ++ v :=
      List.rotate_eq_drop_append_take hrlt.le
    have hmassPos : 0 < prefixProductMass (l.rotate r) := by
      apply prefixProductMass_pos
      · simpa [List.rotate_eq_nil_iff] using hl
      · intro x hx
        exact hpos x (List.mem_rotate.mp hx)
    have hdenom :
        l.prod * properPrefixProductMass l ≤
          v.prod * prefixProductMass (l.rotate r) := by
      have hidentity :
          v.prod * prefixProductMass (l.rotate r) -
              l.prod * properPrefixProductMass l =
            v.prod * (1 - l.prod) *
              (properPrefixProductMass u - 1) := by
        rw [hrotate, prefixProductMass_append,
          prefixProductMass_eq_proper_add_prod_sub_one,
          prefixProductMass_eq_proper_add_prod_sub_one,
          hproperSplit, ← hprodSplit]
        ring
      rw [← sub_nonneg]
      rw [hidentity]
      positivity
    exact (div_le_div_iff₀ hmassPos
      (mul_pos hprodPos hproperPos)).2 (by simpa using hdenom)
  calc
    (∑ r ∈ Finset.range l.length,
        1 / prefixProductMass (l.rotate r)) ≤
        ∑ r ∈ Finset.range l.length,
          (l.take r).prod /
            (l.prod * properPrefixProductMass l) :=
      Finset.sum_le_sum hterm
    _ = properPrefixProductMass l /
          (l.prod * properPrefixProductMass l) := by
      rw [← Finset.sum_div, ← properPrefixProductMass_eq_sum_take]
    _ = 1 / l.prod := by
      field_simp [hprodPos.ne', hproperPos.ne']

/-- Ford's exact cyclic identity: if a positive nonempty list has product
one, the reciprocals of the prefix-product penalties of all rotations sum to
one. -/
theorem sum_inv_prefixProductMass_rotate {l : List ℝ}
    (hl : l ≠ []) (hprod : l.prod = 1)
    (hpos : ∀ x ∈ l, 0 < x) :
    (∑ r ∈ Finset.range l.length,
      1 / prefixProductMass (l.rotate r)) = 1 := by
  have hmassPos : 0 < prefixProductMass l :=
    prefixProductMass_pos hl hpos
  calc
    (∑ r ∈ Finset.range l.length,
        1 / prefixProductMass (l.rotate r)) =
        ∑ r ∈ Finset.range l.length,
          (l.take r).prod / prefixProductMass l := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrlt := Finset.mem_range.mp hr
      rw [prefixProductMass_rotate_div hprod hpos hrlt]
      have hvPos : 0 < (l.take r).prod := by
        apply List.prod_pos
        intro x hx
        exact hpos x (List.mem_of_mem_take hx)
      field_simp [hmassPos.ne', hvPos.ne']
    _ = properPrefixProductMass l / prefixProductMass l := by
      rw [← Finset.sum_div, ← properPrefixProductMass_eq_sum_take]
    _ = 1 := by
      have heq : prefixProductMass l = properPrefixProductMass l := by
        rw [prefixProductMass_eq_proper_add_prod_sub_one, hprod]
        ring
      rw [← heq]
      field_simp [hmassPos.ne']

/-! ## Specialization to integer compositions -/

/-- The cyclic permutation of a `k`-tuple by `r` coordinates. -/
def rotateComposition {k : ℕ} {α : Type*} (r : Fin k) :
    (Fin k → α) ≃ (Fin k → α) :=
  Equiv.arrowCongr (finCycle r).symm (Equiv.refl α)

@[simp] theorem rotateComposition_apply {k : ℕ} {α : Type*} (r : Fin k)
    (b : Fin k → α) (i : Fin k) :
    rotateComposition r b i = b (finCycle r i) := by
  rfl

theorem ofFn_rotateComposition {k : ℕ} {α : Type*} (r : Fin k)
    (b : Fin k → α) :
    List.ofFn (rotateComposition r b) = (List.ofFn b).rotate r.val := by
  apply List.ext_get
  · simp
  · intro i hi hi'
    haveI : NeZero k := NeZero.of_pos r.pos
    rw [List.get_rotate]
    simp only [List.length_ofFn, Fin.cast_eq_self, List.get_ofFn,
      rotateComposition_apply, finCycle_apply]
    rfl

/-- Ford's factor `2^(bᵢ-1)`, written without an integer exponent. -/
noncomputable def compositionFactor {k : ℕ} (b : Fin k → ℕ)
    (i : Fin k) : ℝ :=
  (2 : ℝ) ^ b i / 2

/-- The geometric close-pair penalty attached to one composition. -/
noncomputable def compositionPenalty {k : ℕ} (b : Fin k → ℕ) : ℝ :=
  prefixProductMass (List.ofFn (compositionFactor b))

noncomputable def compositionFactorial {k : ℕ} (b : Fin k → ℕ) : ℝ :=
  ∏ i : Fin k, ((b i).factorial : ℝ)

def compositions (k : ℕ) : Finset (Fin k → ℕ) :=
  Finset.finAntidiagonal k k

theorem mem_compositions {k : ℕ} {b : Fin k → ℕ} :
    b ∈ compositions k ↔ ∑ i : Fin k, b i = k := by
  simp [compositions]

theorem compositionFactor_pos {k : ℕ} (b : Fin k → ℕ) (i : Fin k) :
    0 < compositionFactor b i := by
  dsimp [compositionFactor]
  positivity

theorem prod_compositionFactor_eq_one {k : ℕ} {b : Fin k → ℕ}
    (hb : b ∈ compositions k) :
    (List.ofFn (compositionFactor b)).prod = 1 := by
  have hsum : ∑ i : Fin k, b i = k := mem_compositions.mp hb
  rw [Fin.prod_ofFn]
  simp only [compositionFactor]
  calc
    (∏ i : Fin k, (2 : ℝ) ^ b i / 2) =
        (∏ i : Fin k, (2 : ℝ) ^ b i) /
          ∏ _i : Fin k, (2 : ℝ) := by
      rw [Finset.prod_div_distrib]
    _ = (2 : ℝ) ^ (∑ i : Fin k, b i) / (2 : ℝ) ^ k := by
      rw [Finset.prod_pow_eq_pow_sum, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    _ = 1 := by rw [hsum]; field_simp

theorem compositionPenalty_rotate_sum_one {k : ℕ} (hk : 0 < k)
    {b : Fin k → ℕ} (hb : b ∈ compositions k) :
    (∑ r : Fin k, 1 / compositionPenalty (rotateComposition r b)) = 1 := by
  let l := List.ofFn (compositionFactor b)
  have hl : l ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [l, hk.ne'] at this
  have hprod : l.prod = 1 := prod_compositionFactor_eq_one hb
  have hpos : ∀ x ∈ l, 0 < x := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact compositionFactor_pos b i
  have hcycle := sum_inv_prefixProductMass_rotate hl hprod hpos
  calc
    (∑ r : Fin k, 1 / compositionPenalty (rotateComposition r b)) =
        ∑ r : Fin k,
          1 / prefixProductMass (l.rotate r.val) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [compositionPenalty]
      have hfactor :
          compositionFactor (rotateComposition r b) =
            rotateComposition r (compositionFactor b) := by
        funext i
        rfl
      rw [hfactor, ofFn_rotateComposition]
    _ = ∑ r ∈ Finset.range k,
          1 / prefixProductMass (l.rotate r) := by
      exact (Finset.sum_range
        (fun r : ℕ ↦ 1 / prefixProductMass (l.rotate r))).symm
    _ = 1 := by simpa [l] using hcycle

theorem sum_rotateComposition {k : ℕ} {α : Type*}
    [AddCommMonoid α] (r : Fin k) (b : Fin k → α) :
    (∑ i : Fin k, rotateComposition r b i) = ∑ i : Fin k, b i := by
  exact Fintype.sum_equiv (finCycle r)
    (fun i : Fin k ↦ b (finCycle r i)) b (fun _ ↦ rfl)

theorem prod_rotateComposition {k : ℕ} {α : Type*}
    [CommMonoid α] (r : Fin k) (b : Fin k → α) :
    (∏ i : Fin k, rotateComposition r b i) = ∏ i : Fin k, b i := by
  exact Fintype.prod_equiv (finCycle r)
    (fun i : Fin k ↦ b (finCycle r i)) b (fun _ ↦ rfl)

theorem rotateComposition_mem_compositions {k : ℕ} (r : Fin k)
    {b : Fin k → ℕ} (hb : b ∈ compositions k) :
    rotateComposition r b ∈ compositions k := by
  rw [mem_compositions, sum_rotateComposition]
  exact mem_compositions.mp hb

theorem compositionFactorial_rotate {k : ℕ} (r : Fin k)
    (b : Fin k → ℕ) :
    compositionFactorial (rotateComposition r b) =
      compositionFactorial b := by
  exact prod_rotateComposition r (fun i : Fin k ↦ ((b i).factorial : ℝ))

theorem inv_compositionFactorial_eq_multinomial_div
    {k : ℕ} {b : Fin k → ℕ} (hb : b ∈ compositions k) :
    1 / compositionFactorial b =
      (Nat.multinomial Finset.univ b : ℝ) / (k.factorial : ℝ) := by
  have hsum : ∑ i : Fin k, b i = k := mem_compositions.mp hb
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin k)) b
  rw [hsum] at hspec
  have hspecR :
      compositionFactorial b * (Nat.multinomial Finset.univ b : ℝ) =
        (k.factorial : ℝ) := by
    dsimp [compositionFactorial]
    exact_mod_cast hspec
  have hfacPos : (0 : ℝ) < k.factorial := by positivity
  have hweightPos : 0 < compositionFactorial b := by
    dsimp [compositionFactorial]
    positivity
  field_simp [hfacPos.ne', hweightPos.ne']
  nlinarith

theorem sum_multinomial_compositions (k : ℕ) :
    (∑ b ∈ compositions k, Nat.multinomial Finset.univ b) = k ^ k := by
  have h := Finset.sum_pow_eq_sum_piAntidiag
    (s := (Finset.univ : Finset (Fin k)))
    (f := fun _i : Fin k ↦ (1 : ℕ)) k
  have hfin :
      Finset.piAntidiag (Finset.univ : Finset (Fin k)) k =
        compositions k := by
    ext b
    simp [compositions]
  rw [← hfin]
  simpa using h.symm

theorem sum_inv_compositionFactorial (k : ℕ) :
    (∑ b ∈ compositions k, 1 / compositionFactorial b) =
      (k : ℝ) ^ k / (k.factorial : ℝ) := by
  calc
    (∑ b ∈ compositions k, 1 / compositionFactorial b) =
        ∑ b ∈ compositions k,
          (Nat.multinomial Finset.univ b : ℝ) /
            (k.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact inv_compositionFactorial_eq_multinomial_div hb
    _ = ((∑ b ∈ compositions k,
          Nat.multinomial Finset.univ b : ℕ) : ℝ) /
          (k.factorial : ℝ) := by
      rw [← Finset.sum_div]
      congr 1
      norm_cast
    _ = (k : ℝ) ^ k / (k.factorial : ℝ) := by
      rw [sum_multinomial_compositions]
      norm_cast

/-- The reciprocal factorial-and-cycle weight attached to a composition. -/
noncomputable def compositionCycleWeight {k : ℕ} (b : Fin k → ℕ) : ℝ :=
  1 / (compositionFactorial b * compositionPenalty b)

theorem sum_compositionCycleWeight_rotate {k : ℕ} (r : Fin k) :
    (∑ b ∈ compositions k,
        compositionCycleWeight (rotateComposition r b)) =
      ∑ b ∈ compositions k, compositionCycleWeight b := by
  exact Finset.sum_equiv (rotateComposition r)
    (fun b ↦ by
      simp only [mem_compositions, sum_rotateComposition])
    (fun _b _hb ↦ rfl)

theorem sum_compositionCycleWeight_rotations {k : ℕ} (hk : 0 < k)
    {b : Fin k → ℕ} (hb : b ∈ compositions k) :
    (∑ r : Fin k, compositionCycleWeight (rotateComposition r b)) =
      1 / compositionFactorial b := by
  have hfacPos : 0 < compositionFactorial b := by
    dsimp [compositionFactorial]
    positivity
  calc
    (∑ r : Fin k, compositionCycleWeight (rotateComposition r b)) =
        ∑ r : Fin k,
          (1 / compositionFactorial b) *
            (1 / compositionPenalty (rotateComposition r b)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [compositionCycleWeight, compositionFactorial_rotate]
      field_simp [hfacPos.ne']
    _ = (1 / compositionFactorial b) *
          ∑ r : Fin k,
            1 / compositionPenalty (rotateComposition r b) := by
      rw [Finset.mul_sum]
    _ = 1 / compositionFactorial b := by
      rw [compositionPenalty_rotate_sum_one hk hb, mul_one]

theorem card_mul_sum_compositionCycleWeight (k : ℕ) (hk : 0 < k) :
    (k : ℝ) *
        (∑ b ∈ compositions k, compositionCycleWeight b) =
      (k : ℝ) ^ k / (k.factorial : ℝ) := by
  calc
    (k : ℝ) *
        (∑ b ∈ compositions k, compositionCycleWeight b) =
        ∑ r : Fin k,
          (∑ b ∈ compositions k, compositionCycleWeight b) := by
      simp
    _ = ∑ r : Fin k,
          ∑ b ∈ compositions k,
            compositionCycleWeight (rotateComposition r b) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [sum_compositionCycleWeight_rotate]
    _ = ∑ b ∈ compositions k,
          ∑ r : Fin k,
            compositionCycleWeight (rotateComposition r b) := by
      rw [Finset.sum_comm]
    _ = ∑ b ∈ compositions k, 1 / compositionFactorial b := by
      apply Finset.sum_congr rfl
      intro b hb
      exact sum_compositionCycleWeight_rotations hk hb
    _ = (k : ℝ) ^ k / (k.factorial : ℝ) :=
      sum_inv_compositionFactorial k

/-- The exact unrestricted cycle-weight sum.  This is the source of the
`k^(k-1)/k!` factor in Ford's lower-bound construction. -/
theorem sum_compositionCycleWeight (k : ℕ) (hk : 0 < k) :
    (∑ b ∈ compositions k, compositionCycleWeight b) =
      (k : ℝ) ^ (k - 1) / (k.factorial : ℝ) := by
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hpow : (k : ℝ) ^ k =
      (k : ℝ) * (k : ℝ) ^ (k - 1) := by
    calc
      (k : ℝ) ^ k = (k : ℝ) ^ ((k - 1) + 1) := by
        congr 1
        omega
      _ = (k : ℝ) ^ (k - 1) * (k : ℝ) := by rw [pow_succ]
      _ = (k : ℝ) * (k : ℝ) ^ (k - 1) := by ring
  have h := card_mul_sum_compositionCycleWeight k hk
  rw [hpow] at h
  apply (mul_left_cancel₀ hkR)
  calc
    (k : ℝ) *
        (∑ b ∈ compositions k, compositionCycleWeight b) =
        (k : ℝ) * (k : ℝ) ^ (k - 1) /
          (k.factorial : ℝ) := h
    _ = (k : ℝ) *
        ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ)) := by ring

end Erdos446
