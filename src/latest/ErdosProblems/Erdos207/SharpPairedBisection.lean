/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairedBisectionDegreeScalar

/-! # Paired-cut degree tails retaining the deterministic double-pair gain -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem paired_generating_scalar_sharp (m d D S : ℕ) (hD : D ≤ d) (hcount : m ≤ 2*D+S+2) :
    (2 : ℝ≥0)^(d-D)*(3/4 : ℝ≥0)^S ≤ (2 : ℝ≥0)^d*(3/4 : ℝ≥0)^(m-2) := by
  have hfactor : 1 ≤ ((2 : ℝ≥0)*(3/4 : ℝ≥0)^2)^D := one_le_pow₀ (by
    apply NNReal.coe_le_coe.mp
    norm_num)
  calc
    _ ≤ ((2 : ℝ≥0)^(d-D)*(3/4 : ℝ≥0)^S)*((2 : ℝ≥0)*(3/4 : ℝ≥0)^2)^D :=
      le_mul_of_one_le_right zero_le hfactor
    _ = ((2 : ℝ≥0)^(d-D)*(2 : ℝ≥0)^D)*((3/4 : ℝ≥0)^S*((3/4 : ℝ≥0)^2)^D) := by
      rw [mul_pow]
      ring
    _ = (2 : ℝ≥0)^d*(3/4 : ℝ≥0)^(S+2*D) := by
      rw [← pow_add, Nat.sub_add_cancel hD, ← pow_mul, ← pow_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (NNReal.pow_antitone_exp (m-2) (S+2*D) (by omega) (by
      apply NNReal.coe_le_coe.mp
      norm_num)) zero_le

theorem BalancedBisection.pairedLaw_probability_crossDegree_lt_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r]
    (x : V) (hx : x ∈ W) (m d : ℕ) (hdegree : m ≤ (W.filter (r x)).card) :
    B.pairedLaw.probability (fun ω ↦ B.pairedCrossDegree r ω x < d) ≤
      2*(2 : ℝ≥0)^d*(3/4 : ℝ≥0)^(m-2) := by
  let owner := B.pairOwner x hx
  let D := (B.doubleNeighborPairs r x owner).card
  let S := (B.singleNeighborPairs r x owner).card
  by_cases hdD : d ≤ D
  · calc
      _ ≤ B.pairedLaw.probability (fun _ ↦ False) := by
        apply B.pairedLaw.probability_mono
        intro ω hω
        exact (not_lt_of_ge (hdD.trans (B.doubleNeighborPairs_card_le_pairedCrossDegree r x owner ω))) hω
      _ = 0 := B.pairedLaw.probability_false
      _ ≤ _ := zero_le
  · have hcount : m ≤ 2*D+S+2 := hdegree.trans (B.card_filter_relation_le_double_single r x owner)
    have hb := B.pairedLaw_probability_crossDegree_lt_le r x owner d
    apply hb.trans
    calc
      _ ≤ 2*((2 : ℝ≥0)^d*(3/4 : ℝ≥0)^(m-2)) :=
        mul_le_mul_of_nonneg_left (paired_generating_scalar_sharp m d D S (by omega) hcount) zero_le
      _ = _ := (mul_assoc _ _ _).symm

theorem BalancedBisection.exists_pairedBisection_minCrossDegree_of_sharp
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r] (m d : ℕ)
    (hdegree : ∀ x ∈ W, m ≤ (W.filter (r x)).card)
    (hsmall : (W.card : ℝ≥0)*(2*(2 : ℝ≥0)^d*(3/4 : ℝ≥0)^(m-2)) < 1) :
    ∃ ω : ↥B.left → Bool, ∀ x ∈ W, d ≤ B.pairedCrossDegree r ω x := by
  let Bad := fun x : W ↦ fun ω ↦ B.pairedCrossDegree r ω x.1 < d
  have hprob : ∑ x : W, B.pairedLaw.probability (Bad x) ≤
      (W.card : ℝ≥0)*(2*(2 : ℝ≥0)^d*(3/4 : ℝ≥0)^(m-2)) := by
    calc
      _ ≤ ∑ _x : W, (2*(2 : ℝ≥0)^d*(3/4 : ℝ≥0)^(m-2)) := by
        apply sum_le_sum
        intro x _
        exact B.pairedLaw_probability_crossDegree_lt_le_sharp r x.1 x.2 m d (hdegree x.1 x.2)
      _ = _ := by simp
  obtain ⟨ω, hω⟩ := B.pairedLaw.exists_avoiding_of_sum_probability_lt_one
    (univ : Finset W) Bad (hprob.trans_lt hsmall)
  exact ⟨ω, fun x hx ↦ Nat.le_of_not_gt (hω ⟨x, hx⟩ (mem_univ _))⟩

theorem sharp_paired_tail_eighth_blocks (u : ℕ) :
    2*(2 : ℝ≥0)^(3*u)*(3/4 : ℝ≥0)^((8*u+2)-2) = 2*(6561/8192 : ℝ≥0)^u := by
  rw [Nat.add_sub_cancel, pow_mul, pow_mul, mul_assoc, ← mul_pow]
  norm_num

theorem sharp_paired_tail_le_dyadic (t u : ℕ) (htu : 4*t ≤ u) :
    2*(6561/8192 : ℝ≥0)^u ≤ 2*(1/2 : ℝ≥0)^t := by
  have hbase : (6561/8192 : ℝ≥0) ≤ 1 := by apply NNReal.coe_le_coe.mp; norm_num
  have hfour : (6561/8192 : ℝ≥0)^4 ≤ 1/2 := by apply NNReal.coe_le_coe.mp; norm_num
  apply mul_le_mul_of_nonneg_left _ zero_le
  calc
    _ ≤ (6561/8192 : ℝ≥0)^(4*t) := NNReal.pow_antitone_exp _ _ htu hbase
    _ = ((6561/8192 : ℝ≥0)^4)^t := pow_mul _ _ _
    _ ≤ _ := pow_le_pow_left' hfour t

theorem BalancedBisection.exists_pairedBisection_threeEighths
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (r : V → V → Prop) [DecidableRel r] (u : ℕ)
    (hdegree : ∀ x ∈ W, 8*u+2 ≤ (W.filter (r x)).card)
    (hsmall : (W.card : ℝ≥0)*(2*(6561/8192 : ℝ≥0)^u) < 1) :
    ∃ ω : ↥B.left → Bool, ∀ x ∈ W, 3*u ≤ B.pairedCrossDegree r ω x := by
  apply B.exists_pairedBisection_minCrossDegree_of_sharp r (8*u+2) (3*u) hdegree
  simpa only [sharp_paired_tail_eighth_blocks] using hsmall

end

end Erdos207
