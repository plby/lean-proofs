/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpHallSumBound
import ErdosProblems.Erdos207.PowerConcentrationOptimization

/-! # Explicit exponential slack makes the sharp Hall sum geometric -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem sharpHall_size_base_le_half_pow
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (c Delta t : ℕ)
    (hbudget : (Delta + t : ℝ≥0) ≤ sigma * c / 2) :
    (1 - sigma / 2) ^ c * (2 : ℝ≥0) ^ Delta ≤ (1 / 2 : ℝ≥0) ^ t := by
  have hsigmaR : (sigma : ℝ) ≤ 1 := by exact_mod_cast hsigma
  have hbudgetR : (Delta : ℝ) + t ≤ (sigma : ℝ) * c / 2 := by exact_mod_cast hbudget
  have hhalf : sigma / 2 ≤ (1 : ℝ≥0) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).mpr
    exact hsigma.trans (by norm_num)
  have hbase0 : 0 ≤ 1 - (sigma : ℝ) / 2 := by linarith [sigma.property]
  have hbase : 1 - (sigma : ℝ) / 2 ≤ Real.exp (-(sigma : ℝ) / 2) := by
    simpa only [neg_div] using Real.one_sub_le_exp_neg ((sigma : ℝ) / 2)
  have hpow : (1 - (sigma : ℝ) / 2) ^ c ≤ Real.exp ((c : ℝ) * (-(sigma : ℝ) / 2)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hbase0 hbase c
  have htwo : (2 : ℝ) ^ Delta ≤ Real.exp (Delta : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ Delta := pow_le_pow_left₀ (by norm_num)
        (by nlinarith [Real.add_one_le_exp (1 : ℝ)]) Delta
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one]
  have hbound : (1 - (sigma : ℝ) / 2) ^ c * (2 : ℝ) ^ Delta ≤ (1 / 2 : ℝ) ^ t := by
    calc
      _ ≤ Real.exp ((c : ℝ) * (-(sigma : ℝ) / 2)) * Real.exp (Delta : ℝ) :=
        mul_le_mul hpow htwo (by positivity) (Real.exp_nonneg _)
      _ = Real.exp ((c : ℝ) * (-(sigma : ℝ) / 2) + Delta) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(t : ℝ)) := Real.exp_le_exp.mpr (by nlinarith [hbudgetR])
      _ ≤ _ := exp_neg_nat_le_half_pow t
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_sub hhalf,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hbound

theorem sharpHall_sum_le_geometric
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r] (hcard : Fintype.card A = Fintype.card B)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (c Delta t : ℕ)
    (hcandidate : ∀ o : OrientedSmallHallObstruction A B,
      c * orientedSmallHallSize o ≤ (orientedSmallHallCandidates r o).card)
    (hbudget : (Delta + t : ℝ≥0) ≤ sigma * c / 2)
    (hsmall : ((2 * (Fintype.card A + 1) * (Fintype.card B + 1) : ℕ) : ℝ≥0) *
      (1 / 2 : ℝ≥0) ^ t ≤ 1 / 2) :
    (∑ o : OrientedSmallHallObstruction A B,
      (1 - sigma / 2) ^ (orientedSmallHallCandidates r o).card /
        (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize o)) ≤
      4 * ((2 * (Fintype.card A + 1) * (Fintype.card B + 1) : ℕ) : ℝ≥0) * (1 / 2 : ℝ≥0) ^ t := by
  have hbase := sharpHall_size_base_le_half_pow sigma hsigma c Delta t hbudget
  exact (sharpHall_sum_le r hcard sigma c Delta hcandidate
    ((mul_le_mul_of_nonneg_left hbase zero_le).trans hsmall)).trans
      (mul_le_mul_of_nonneg_left hbase zero_le)

theorem simultaneous_sharpHall_sum_le_geometric
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (c : O → ℕ) (Delta t N : ℕ)
    (hsize : ∀ o, (K o).left.card ≤ N ∧ (K o).right.card ≤ N)
    (hcandidate : ∀ o (h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right),
      c o * orientedSmallHallSize h ≤ (orientedSmallHallCandidates (r o) h).card)
    (hbudget : ∀ o, (Delta + t : ℝ≥0) ≤ sigma * c o / 2)
    (hsmall : 2 * (N+1 : ℝ≥0) ^ 2 * (1 / 2 : ℝ≥0) ^ t ≤ 1 / 2) :
    (∑ o : O, ∑ h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right,
      (1 - sigma / 2) ^ (orientedSmallHallCandidates (r o) h).card /
        (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize h)) ≤
      8 * (Fintype.card O : ℝ≥0) * (N+1 : ℝ≥0) ^ 2 * (1 / 2 : ℝ≥0) ^ t := by
  have hcoeff (o : O) :
      ((2 * (Fintype.card ↥(K o).left + 1) * (Fintype.card ↥(K o).right + 1) : ℕ) : ℝ≥0) ≤
        2 * (N+1 : ℝ≥0) ^ 2 := by
    simp only [Fintype.card_coe, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_two]
    calc
      _ ≤ 2 * (N+1 : ℝ≥0) * (N+1 : ℝ≥0) := by
        gcongr
        · exact_mod_cast (hsize o).1
        · exact_mod_cast (hsize o).2
      _ = _ := by ring
  calc
    _ ≤ ∑ _o : O, 8 * (N+1 : ℝ≥0) ^ 2 * (1 / 2 : ℝ≥0) ^ t := by
      apply sum_le_sum
      intro o _
      have ht := sharpHall_sum_le_geometric (r o) (by simpa only [Fintype.card_coe] using hbalanced o)
        sigma hsigma (c o) Delta t (hcandidate o) (hbudget o)
        ((mul_le_mul_of_nonneg_right (hcoeff o) zero_le).trans hsmall)
      apply ht.trans
      calc
        _ ≤ 4 * (2 * (N+1 : ℝ≥0) ^ 2) * (1 / 2 : ℝ≥0) ^ t := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcoeff o) zero_le) zero_le
        _ = _ := by ring
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring

theorem independentBits_not_all_twoSidedRobust_le_geometric
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (c : O → ℕ) (Delta t N : ℕ)
    (hsize : ∀ o, (K o).left.card ≤ N ∧ (K o).right.card ≤ N)
    (hcandidate : ∀ o (h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right),
      c o * orientedSmallHallSize h ≤ (orientedSmallHallCandidates (r o) h).card)
    (hbudget : ∀ o, (Delta + t : ℝ≥0) ≤ sigma * c o / 2)
    (hsmall : 2 * (N+1 : ℝ≥0) ^ 2 * (1 / 2 : ℝ≥0) ^ t ≤ 1 / 2) :
    (FiniteLaw.independentBits (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)).probability
      (fun omega ↦ ¬ ∀ o, IsTwoSidedRobustMatchingSample (r o) Delta (simultaneousLinkSelectedPairs K omega o)) ≤
        8 * (Fintype.card O : ℝ≥0) * (N+1 : ℝ≥0) ^ 2 * (1 / 2 : ℝ≥0) ^ t :=
  (independentBits_probability_not_all_twoSidedRobust_le_sharp K r Delta hbalanced sigma hsigma).trans
    (simultaneous_sharpHall_sum_le_geometric K r hbalanced sigma hsigma c Delta t N hsize hcandidate hbudget hsmall)

end

end Erdos207
