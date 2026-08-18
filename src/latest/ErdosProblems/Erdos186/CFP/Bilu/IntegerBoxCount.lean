/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval

/-!
# Counting bounded integral coordinate vectors

This is the elementary counting input in Bilu's Lemma 6.8.  A vector whose
integer coordinates have real absolute value strictly smaller than `X` lies
in a centered box of half-width `Nat.ceil X - 1`.  For `1 ≤ X`, that box has
at most `(3 * X)^d` points.
-/

namespace Erdos186.CFP.Bilu.IntegerBoxCount

open scoped BigOperators

/-- The integral coordinate box `[-N,N]^d`. -/
def centeredIntBox (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(N : ℤ)) (N : ℤ)

@[simp]
theorem mem_centeredIntBox {d N : ℕ} {x : Fin d → ℤ} :
    x ∈ centeredIntBox d N ↔ ∀ i, -(N : ℤ) ≤ x i ∧ x i ≤ (N : ℤ) := by
  simp [centeredIntBox]

@[simp]
theorem card_centeredIntBox (d N : ℕ) :
    (centeredIntBox d N).card = (2 * N + 1) ^ d := by
  simp only [centeredIntBox, Fintype.card_piFinset, Int.card_Icc,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- Strict real coordinate bounds place an integral vector in the smallest
centered box determined by the ceiling of the bound. -/
theorem mem_centeredIntBox_ceil_sub_one {d : ℕ} {X : ℝ}
    (hX : 0 < X) (x : Fin d → ℤ)
    (hx : ∀ i, |(x i : ℝ)| < X) :
    x ∈ centeredIntBox d (Nat.ceil X - 1) := by
  rw [mem_centeredIntBox]
  intro i
  have habs : ((x i).natAbs : ℝ) < X := by
    simpa using hx i
  have hlt : (x i).natAbs < Nat.ceil X := by
    exact Nat.lt_ceil.mpr habs
  have hceil_pos : 0 < Nat.ceil X := Nat.ceil_pos.mpr hX
  have hnat : (x i).natAbs ≤ Nat.ceil X - 1 := by omega
  have hnatZ : ((x i).natAbs : ℤ) ≤ (Nat.ceil X - 1 : ℕ) := by
    exact_mod_cast hnat
  constructor
  · have hneg : -x i ≤ ((x i).natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -x i))
    linarith
  · exact Int.le_natAbs.trans hnatZ

/-- The real cardinality estimate used to count the possible integer vectors
in Bilu's bad-set union. -/
theorem card_centeredIntBox_ceil_sub_one_le {d : ℕ} {X : ℝ}
    (hX : 1 ≤ X) :
    ((centeredIntBox d (Nat.ceil X - 1)).card : ℝ) ≤ (3 * X) ^ d := by
  rw [card_centeredIntBox, Nat.cast_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  have hceil_lt : (Nat.ceil X : ℝ) < X + 1 := Nat.ceil_lt_add_one hX0
  have hceil_pos : 0 < Nat.ceil X := Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hX)
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hceil_pos.ne')]
  norm_num
  nlinarith

/-- Consequently, the set of all integral vectors satisfying the strict
coordinate bound has cardinal at most `(3X)^d`. -/
theorem card_filter_coordBound_le {d : ℕ} {X : ℝ} (hX : 1 ≤ X) :
    (((centeredIntBox d (Nat.ceil X - 1)).filter
      fun x ↦ ∀ i, |(x i : ℝ)| < X).card : ℝ) ≤ (3 * X) ^ d := by
  calc
    (((centeredIntBox d (Nat.ceil X - 1)).filter
        fun x ↦ ∀ i, |(x i : ℝ)| < X).card : ℝ) ≤
        ((centeredIntBox d (Nat.ceil X - 1)).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le _ _
    _ ≤ (3 * X) ^ d := card_centeredIntBox_ceil_sub_one_le hX

/-- Simultaneously count an ambient integer vector and a coefficient vector.
This is the finite index set for the bad affine slices in Lemma 6.8. -/
theorem card_product_centeredIntBox_le {n r : ℕ} {X : ℝ} (hX : 1 ≤ X) :
    (((centeredIntBox n (Nat.ceil X - 1)) ×ˢ
        (centeredIntBox r (Nat.ceil X - 1))).card : ℝ) ≤
      (3 * X) ^ (n + r) := by
  rw [Finset.card_product, Nat.cast_mul, pow_add]
  exact mul_le_mul
    (card_centeredIntBox_ceil_sub_one_le (d := n) hX)
    (card_centeredIntBox_ceil_sub_one_le (d := r) hX)
    (by positivity) (by positivity)

end Erdos186.CFP.Bilu.IntegerBoxCount

#print axioms Erdos186.CFP.Bilu.IntegerBoxCount.card_centeredIntBox_ceil_sub_one_le
