/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import Mathlib

/-!
# Elementary analytic estimates for the DGK argument

This file collects the small, wholly finite estimates used by the
Duraj--Gutowski--Kozik part of the proof of Erdős Problem 1027.  Keeping these
lemmas independent of the hypergraph development makes both their hypotheses
and their use in finite probability spaces explicit.
-/

open scoped BigOperators

namespace Erdos1027.DGKAnalytic

open Finset

/-! ## Markov's inequality on a finite set -/

/-- The division-free form of Markov's inequality for a finite sum.

Every term indexed by `i` with `t ≤ f i` contributes at least `t`; the
nonnegativity hypothesis allows us to discard all remaining terms. -/
lemma threshold_mul_card_le_sum {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ℝ) (t : ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    t * ((s.filter fun i ↦ t ≤ f i).card : ℝ) ≤ ∑ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self _ _)
      have hfs : ∀ i ∈ s, 0 ≤ f i :=
        fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have ih' := ih hfs
      by_cases hat : t ≤ f a
      · calc
          t * ((((insert a s).filter fun i ↦ t ≤ f i).card : ℕ) : ℝ) =
              t + t * ((s.filter fun i ↦ t ≤ f i).card : ℝ) := by
                have haf : a ∉ s.filter fun i ↦ t ≤ f i := by simp [ha]
                rw [Finset.filter_insert, if_pos hat,
                  Finset.card_insert_of_notMem haf]
                push_cast
                ring
          _ ≤ f a + ∑ i ∈ s, f i := add_le_add hat ih'
          _ = ∑ i ∈ insert a s, f i := (Finset.sum_insert ha).symm
      · calc
          t * ((((insert a s).filter fun i ↦ t ≤ f i).card : ℕ) : ℝ) =
              t * ((s.filter fun i ↦ t ≤ f i).card : ℝ) := by
                rw [Finset.filter_insert, if_neg hat]
          _ ≤ ∑ i ∈ s, f i := ih'
          _ ≤ f a + ∑ i ∈ s, f i := le_add_of_nonneg_left hfa
          _ = ∑ i ∈ insert a s, f i := (Finset.sum_insert ha).symm

/-- Markov's inequality in cardinality form. -/
lemma card_threshold_le_sum_div {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ℝ) {t : ℝ} (ht : 0 < t)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ((s.filter fun i ↦ t ≤ f i).card : ℝ) ≤ (∑ i ∈ s, f i) / t := by
  rw [le_div_iff₀ ht]
  simpa [mul_comm] using threshold_mul_card_le_sum s f t hf

/-- Markov's inequality for the uniform probability measure on a nonempty
finite set.  Both sides are written out as quotients so no probability-space
infrastructure is required. -/
lemma card_threshold_div_card_le_average_div {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ℝ) {t : ℝ} (ht : 0 < t)
    (hs : s.Nonempty) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ((s.filter fun i ↦ t ≤ f i).card : ℝ) / s.card ≤
      ((∑ i ∈ s, f i) / s.card) / t := by
  have hspos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  calc
    ((s.filter fun i ↦ t ≤ f i).card : ℝ) / s.card ≤
        ((∑ i ∈ s, f i) / t) / s.card :=
      div_le_div_of_nonneg_right (card_threshold_le_sum_div s f ht hf) hspos.le
    _ = ((∑ i ∈ s, f i) / s.card) / t := by ring

/-! ## Finite products and exponentials -/

/-- A finite product of factors `1 + a i` is at most the exponential of their
sum when all increments are nonnegative. -/
lemma prod_one_add_le_exp_sum {I : Type*} (s : Finset I) (a : I → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, (1 + a i) ≤ Real.exp (∑ i ∈ s, a i) := by
  calc
    ∏ i ∈ s, (1 + a i) ≤ ∏ i ∈ s, Real.exp (a i) := by
      exact Finset.prod_le_prod
        (fun i hi ↦ add_nonneg zero_le_one (ha i hi))
        (fun i _ ↦ (add_comm 1 (a i)).le.trans (Real.add_one_le_exp _))
    _ = Real.exp (∑ i ∈ s, a i) := (Real.exp_sum s a).symm

/-- The exponential of a positive natural number is strictly bounded by the
corresponding power of `3`.  Positivity is necessary: both sides equal one
when `n = 0`. -/
lemma exp_natCast_lt_three_pow (n : ℕ) (hn : 0 < n) :
    Real.exp (n : ℝ) < (3 : ℝ) ^ n := by
  rw [show (n : ℝ) = (n : ℝ) * 1 by ring, Real.exp_nat_mul]
  exact pow_lt_pow_left₀ (Real.exp_one_lt_three) (Real.exp_pos 1).le hn.ne'

/-- A monotone variant useful when an exponential's argument is bounded by an
explicit natural-number cap. -/
lemma exp_le_three_pow_of_le_natCast {x : ℝ} {n : ℕ} (hx : x ≤ n) :
    Real.exp x ≤ (3 : ℝ) ^ n := by
  refine (Real.exp_le_exp.mpr hx).trans ?_
  rw [show (n : ℝ) = (n : ℝ) * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le n

/-! ## A rational finite-decay estimate -/

/-- The real version of the elementary decay estimate
`(1 - d / j)^j ≤ 1 / (d + 1)` for `d ≤ j`.

The degenerate case `j = 0` is separated.  Otherwise `1 - d/j` is
nonnegative, it is at most `exp (-d/j)`, and raising this inequality to the
`j`-th power gives `exp (-d)`.  Finally `1 + d ≤ exp d`. -/
lemma one_sub_div_pow_le_inv_add_one_real (d j : ℕ) (hdj : d ≤ j) :
    (1 - (d : ℝ) / j) ^ j ≤ 1 / ((d : ℝ) + 1) := by
  by_cases hj : j = 0
  · subst j
    have hd : d = 0 := Nat.eq_zero_of_le_zero hdj
    subst d
    norm_num
  · have hjpos : (0 : ℝ) < j := by positivity
    have hratio : (0 : ℝ) ≤ (d : ℝ) / j := by positivity
    have hratio_le : (d : ℝ) / j ≤ 1 := by
      rw [div_le_one hjpos]
      exact_mod_cast hdj
    have hbase : 0 ≤ 1 - (d : ℝ) / j := sub_nonneg.mpr hratio_le
    have hbase_exp : 1 - (d : ℝ) / j ≤ Real.exp (-((d : ℝ) / j)) := by
      simpa [sub_eq_add_neg, add_comm] using
        Real.add_one_le_exp (-((d : ℝ) / j))
    have hpow :
        (1 - (d : ℝ) / j) ^ j ≤ (Real.exp (-((d : ℝ) / j))) ^ j :=
      pow_le_pow_left₀ hbase hbase_exp j
    have hexp_pow :
        (Real.exp (-((d : ℝ) / j))) ^ j = Real.exp (-(d : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    have hden_exp : (d : ℝ) + 1 ≤ Real.exp (d : ℝ) :=
      Real.add_one_le_exp (d : ℝ)
    have hdenpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
    have hinv : Real.exp (-(d : ℝ)) ≤ 1 / ((d : ℝ) + 1) := by
      rw [Real.exp_neg, one_div]
      exact (inv_le_inv₀ (Real.exp_pos _) hdenpos).mpr hden_exp
    exact hpow.trans (hexp_pow.le.trans hinv)

/-- Rational form of the same estimate.  This avoids introducing real-valued
probabilities in finite rational calculations. -/
lemma one_sub_div_pow_le_inv_add_one_rat (d j : ℕ) (hdj : d ≤ j) :
    (1 - (d : ℚ) / j) ^ j ≤ 1 / ((d : ℚ) + 1) := by
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact one_sub_div_pow_le_inv_add_one_real d j hdj

end Erdos1027.DGKAnalytic
