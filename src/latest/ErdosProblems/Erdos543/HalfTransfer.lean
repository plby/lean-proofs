/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import ErdosProblems.Erdos543.IIDModel
import ErdosProblems.Erdos543.IIDTransfer
import ErdosProblems.Erdos543.Asymptotics
import ErdosProblems.Erdos543.PrimeSequence

/-!
# Transferring independent-model failure to the uniform subset model

This file is the normalization bridge between a real-valued uniform
probability estimate on independent tuples and the strict natural-number
inequality required by `IIDTransfer`.  It also disposes of tuple collisions
uniformly at the rounded cutoff and packages the result along the canonical
cofinal sequence of prime moduli.
-/

open Filter
open scoped Topology

namespace Erdos543.HalfTransfer

attribute [local instance] Classical.propDecidable

open FiniteProbability

/-! ## Exact normalization and event containment -/

lemma iidGoodCount_eq_card_underlyingCompleteTuples
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    IIDTransfer.iidGoodCount (α := G) Model.SubsetSumComplete k =
      (IIDModel.underlyingCompleteTuples G k).card := by
  rw [IIDTransfer.iidGoodCount, IIDModel.underlyingCompleteTuples]
  congr 1

/-- The ordinary-completeness probability of an independent tuple is the
`iidGoodCount` divided by the exact size of the product sample space. -/
lemma prob_underlyingCompleteEvent_eq_iidGoodCount_div
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    prob (IIDModel.underlyingCompleteEvent G k) =
      (IIDTransfer.iidGoodCount (α := G) Model.SubsetSumComplete k : ℝ) /
        (Fintype.card G ^ k : ℕ) := by
  rw [prob]
  congr 1
  · simp

/-- Indexed completeness is exactly the zero-missed-nonzero-target event. -/
lemma indexedCompleteEvent_eq_zeroMiss
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    IIDModel.indexedCompleteEvent G k =
      {a | IIDModel.missedNonzeroCount a = 0} := by
  ext a
  exact IIDModel.indexedComplete_iff_missedNonzeroCount_eq_zero a

lemma prob_indexedCompleteEvent_eq_prob_zeroMiss
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    prob (IIDModel.indexedCompleteEvent G k) =
      prob ({a : IIDModel.IIDSpace G k |
        IIDModel.missedNonzeroCount a = 0} : Set (IIDModel.IIDSpace G k)) := by
  rw [indexedCompleteEvent_eq_zeroMiss]

/-- The `iidGoodCount` ratio is bounded by the indexed zero-miss
probability. -/
lemma iidGoodCount_div_le_prob_indexedCompleteEvent
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    (IIDTransfer.iidGoodCount (α := G) Model.SubsetSumComplete k : ℝ) /
        (Fintype.card G ^ k : ℕ) ≤
      prob (IIDModel.indexedCompleteEvent G k) := by
  rw [← prob_underlyingCompleteEvent_eq_iidGoodCount_div]
  exact IIDModel.prob_underlyingCompleteEvent_le_prob_indexedCompleteEvent G k

/-! ## From real ratios to the strict natural count inequality -/

/-- A real probability bound plus the exact collision ratio implies the
strict natural-number inequality consumed by `IIDTransfer`. -/
theorem not_halfComplete_of_two_mul_prob_add_collision_ratio_lt_one
    (G : Type*) [AddCommGroup G] [Fintype G] [Nonempty G] (k : ℕ)
    (h : 2 * prob (IIDModel.indexedCompleteEvent G k) +
        ((IIDTransfer.collisionTuples G k).card : ℝ) /
          (Fintype.card G ^ k : ℕ) < 1) :
    ¬ Model.HalfComplete G k := by
  apply IIDTransfer.not_halfComplete_of_iidCompleteCount_add_collision_lt
  let T : ℕ := Fintype.card G ^ k
  let C : ℕ := IIDTransfer.iidGoodCount (α := G) Model.SubsetSumComplete k
  let D : ℕ := (IIDTransfer.collisionTuples G k).card
  have hTnat : 0 < T := pow_pos Fintype.card_pos _
  have hT : (0 : ℝ) < T := by exact_mod_cast hTnat
  have hgood : (C : ℝ) / T ≤
      prob (IIDModel.indexedCompleteEvent G k) := by
    simpa [C, T] using iidGoodCount_div_le_prob_indexedCompleteEvent G k
  have hratio : (2 : ℝ) * (C / T) + D / T < 1 := by
    have hupper : (2 : ℝ) * prob (IIDModel.indexedCompleteEvent G k) +
        D / T < 1 := by simpa [C, D, T] using h
    nlinarith
  have hratio' : (((2 * C + D : ℕ) : ℝ) / T) < 1 := by
    have heq : (((2 * C + D : ℕ) : ℝ) / T) =
        (2 : ℝ) * (C / T) + D / T := by
      push_cast
      field_simp [hT.ne']
    rw [heq]
    exact hratio
  have hreal : ((2 * C + D : ℕ) : ℝ) < T := by
    exact (div_lt_one hT).mp hratio'
  change 2 * C + D < T
  exact_mod_cast hreal

/-- Convenient separated margins.  The constants leave a factor-two reserve
after both the good-tuple and collision masses are inserted. -/
theorem not_halfComplete_of_prob_indexed_lt_eighth_of_collision_lt_quarter
    (G : Type*) [AddCommGroup G] [Fintype G] [Nonempty G] (k : ℕ)
    (hcomplete : prob (IIDModel.indexedCompleteEvent G k) < 1 / 8)
    (hcollision :
      ((IIDTransfer.collisionTuples G k).card : ℝ) /
        (Fintype.card G ^ k : ℕ) < 1 / 4) :
    ¬ Model.HalfComplete G k := by
  apply not_halfComplete_of_two_mul_prob_add_collision_ratio_lt_one
  nlinarith

/-! ## Collision ratios -/

/-- The pairwise union bound, normalized by the full tuple sample space. -/
lemma collision_ratio_le_sq_div_card
    (G : Type*) [Fintype G] [Nonempty G] (k : ℕ) :
    ((IIDTransfer.collisionTuples G k).card : ℝ) /
        (Fintype.card G ^ k : ℕ) ≤
      (k : ℝ) ^ 2 / Fintype.card G := by
  let n := Fintype.card G
  have hnNat : 0 < n := Fintype.card_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hcount := IIDTransfer.card_collisionTuples_le_choose_mul_pow G k
  rw [Nat.cast_pow]
  change ((IIDTransfer.collisionTuples G k).card : ℝ) / (n : ℝ) ^ k ≤
    (k : ℝ) ^ 2 / n
  by_cases hk : k = 0
  · subst k
    have hzero : (IIDTransfer.collisionTuples G 0).card = 0 := by
      simpa using hcount
    rw [hzero]
    simp
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hcountR : ((IIDTransfer.collisionTuples G k).card : ℝ) ≤
        (k.choose 2 : ℝ) * (n : ℝ) ^ (k - 1) := by
      exact_mod_cast hcount
    have hpow : (n : ℝ) ^ k = (n : ℝ) ^ (k - 1) * n := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ]
    have hchoose : (k.choose 2 : ℝ) ≤ (k : ℝ) ^ 2 := by
      rw [Nat.cast_choose_two]
      have hkmul : (k : ℝ) * ((k : ℝ) - 1) ≤ (k : ℝ) * k := by
        gcongr
        linarith
      nlinarith [sq_nonneg (k : ℝ)]
    calc
      ((IIDTransfer.collisionTuples G k).card : ℝ) / (n : ℝ) ^ k ≤
          ((k.choose 2 : ℝ) * (n : ℝ) ^ (k - 1)) /
            (n : ℝ) ^ k :=
        div_le_div_of_nonneg_right hcountR (by positivity)
      _ = (k.choose 2 : ℝ) / n := by
        rw [hpow]
        field_simp [hn.ne']
      _ ≤ (k : ℝ) ^ 2 / n :=
        div_le_div_of_nonneg_right hchoose hn.le

/-- Pointwise `ZMod` form used at the rounded cutoff. -/
theorem not_halfComplete_zmod_of_prob_indexed_lt_eighth_of_sq_div_lt_quarter
    {p k : ℕ} [NeZero p]
    (hcomplete :
      prob (IIDModel.indexedCompleteEvent (ZMod p) k) < 1 / 8)
    (hcollision : (k : ℝ) ^ 2 / p < 1 / 4) :
    ¬ Model.HalfComplete (ZMod p) k := by
  apply not_halfComplete_of_prob_indexed_lt_eighth_of_collision_lt_quarter
  · exact hcomplete
  · exact lt_of_le_of_lt (by
      simpa [ZMod.card p] using
        collision_ratio_le_sq_div_card (ZMod p) k) hcollision

/-! ## Eventual prime-cyclic transfer -/

/-- Sampling collisions disappear at every proposed `o(log log)` cutoff. -/
lemma tendsto_cutoffSize_sq_div_nat_zero
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ (cutoffSize g N : ℝ) ^ 2 / (N : ℝ))
      atTop (𝓝 0) := by
  have hk : (fun N : ℕ ↦ (cutoffSize g N : ℝ) ^ 2) =O[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ 2) :=
    (cutoffSize_isBigO_log hg).pow 2
  have hlog : (fun N : ℕ ↦ Real.log (N : ℝ) ^ 2) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
    simpa only [Function.comp_def, Real.rpow_one, Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop 2
        (by norm_num : (0 : ℝ) < 1)).comp_tendsto
          tendsto_natCast_atTop_atTop
  exact (hk.trans_isLittleO hlog).tendsto_div_nhds_zero

/-- Along the canonical prime sequence, convergence of the indexed
zero-miss probability to zero forces eventual failure of half completeness
at every proposed `o(log log)` cutoff. -/
theorem eventually_not_halfComplete_primeSeq_of_tendsto_prob_indexed_zero
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0))
    (hprob : Tendsto (fun i : ℕ ↦
      prob (IIDModel.indexedCompleteEvent
        (ZMod (PrimeSequence.primeSeq i))
        (cutoffSize g (PrimeSequence.primeSeq i)))) atTop (𝓝 0)) :
    ∀ᶠ i : ℕ in atTop,
      ¬ Model.HalfComplete (ZMod (PrimeSequence.primeSeq i))
        (cutoffSize g (PrimeSequence.primeSeq i)) := by
  have hprobSmall : ∀ᶠ i : ℕ in atTop,
      prob (IIDModel.indexedCompleteEvent
        (ZMod (PrimeSequence.primeSeq i))
        (cutoffSize g (PrimeSequence.primeSeq i))) < 1 / 8 :=
    (tendsto_order.1 hprob).2 _ (by norm_num)
  have hcollisionZero :=
    (tendsto_cutoffSize_sq_div_nat_zero hg).comp
      PrimeSequence.tendsto_primeSeq_atTop
  have hcollisionSmall : ∀ᶠ i : ℕ in atTop,
      (cutoffSize g (PrimeSequence.primeSeq i) : ℝ) ^ 2 /
        (PrimeSequence.primeSeq i : ℝ) < 1 / 4 :=
    (tendsto_order.1 hcollisionZero).2 _ (by norm_num)
  filter_upwards [hprobSmall, hcollisionSmall] with i hcomplete hcollision
  exact not_halfComplete_zmod_of_prob_indexed_lt_eighth_of_sq_div_lt_quarter
    hcomplete hcollision

/-- Equivalent zero-miss formulation of the preceding transfer theorem. -/
theorem eventually_not_halfComplete_primeSeq_of_tendsto_prob_zeroMiss_zero
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0))
    (hprob : Tendsto (fun i : ℕ ↦
      prob {a : IIDModel.IIDSpace (ZMod (PrimeSequence.primeSeq i))
          (cutoffSize g (PrimeSequence.primeSeq i)) |
        IIDModel.missedNonzeroCount a = 0}) atTop (𝓝 0)) :
    ∀ᶠ i : ℕ in atTop,
      ¬ Model.HalfComplete (ZMod (PrimeSequence.primeSeq i))
        (cutoffSize g (PrimeSequence.primeSeq i)) := by
  apply eventually_not_halfComplete_primeSeq_of_tendsto_prob_indexed_zero hg
  convert hprob using 1
  funext i
  exact prob_indexedCompleteEvent_eq_prob_zeroMiss _ _

end Erdos543.HalfTransfer
