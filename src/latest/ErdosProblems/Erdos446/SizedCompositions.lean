/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.CappedCompositions

/-!
# Erdős Problem 446: size-truncated compositions

The block construction also needs the selected products to lie below one
fixed doubly exponential endpoint.  A pointwise right-hand cap is not needed:
decreasing one positive coordinate relates its cyclic weight to a composition
of total mass `K - 1`, and cyclic averaging bounds the latter family.  This
gives a first moment of order `2^K`, so a fixed Markov truncation retains a
constant fraction of Ford's already capped cyclic mass.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem prefixProductMass_mono_of_forall₂ {l m : List ℝ}
    (h : List.Forall₂ (fun x y ↦ 0 ≤ x ∧ x ≤ y) l m) :
    prefixProductMass l ≤ prefixProductMass m := by
  have hstrong : 0 ≤ prefixProductMass l ∧
      prefixProductMass l ≤ prefixProductMass m := by
    induction h with
    | nil => simp
    | @cons x y l m hxy htail ih =>
      rw [prefixProductMass_cons, prefixProductMass_cons]
      have hx : 0 ≤ x := hxy.1
      have hy : 0 ≤ y := hxy.1.trans hxy.2
      constructor
      · exact mul_nonneg hx (by linarith [ih.1])
      · exact mul_le_mul hxy.2 (by linarith [ih.2])
          (by linarith [ih.1]) hy
  exact hstrong.2

/-- Add one unit in the distinguished coordinate. -/
def incrementComposition {K : ℕ} (i : Fin K) (b : Fin K → ℕ) : Fin K → ℕ :=
  Function.update b i (b i + 1)

/-- Remove one unit in the distinguished coordinate. -/
def decrementComposition {K : ℕ} (i : Fin K) (b : Fin K → ℕ) : Fin K → ℕ :=
  Function.update b i (b i - 1)

@[simp] theorem incrementComposition_same {K : ℕ} (i : Fin K)
    (b : Fin K → ℕ) : incrementComposition i b i = b i + 1 := by
  simp [incrementComposition]

@[simp] theorem incrementComposition_of_ne {K : ℕ} {i q : Fin K}
    (hiq : q ≠ i) (b : Fin K → ℕ) : incrementComposition i b q = b q := by
  simp [incrementComposition, hiq]

@[simp] theorem decrementComposition_same {K : ℕ} (i : Fin K)
    (b : Fin K → ℕ) : decrementComposition i b i = b i - 1 := by
  simp [decrementComposition]

@[simp] theorem decrementComposition_of_ne {K : ℕ} {i q : Fin K}
    (hiq : q ≠ i) (b : Fin K → ℕ) : decrementComposition i b q = b q := by
  simp [decrementComposition, hiq]

theorem sum_incrementComposition {K : ℕ} (i : Fin K) (b : Fin K → ℕ) :
    (∑ q : Fin K, incrementComposition i b q) =
      (∑ q : Fin K, b q) + 1 := by
  classical
  rw [show (∑ q : Fin K, incrementComposition i b q) =
      b i + 1 + ∑ q ∈ (Finset.univ : Finset (Fin K)) \ {i}, b q by
    simpa [incrementComposition] using
      Finset.sum_update_of_mem (Finset.mem_univ i) b (b i + 1)]
  rw [show (∑ q : Fin K, b q) =
      b i + ∑ q ∈ (Finset.univ : Finset (Fin K)) \ {i}, b q by
    simpa using Finset.sum_update_of_mem
      (Finset.mem_univ i) b (b i)]
  omega

theorem sum_decrementComposition {K : ℕ} (i : Fin K) (b : Fin K → ℕ)
    (hi : 0 < b i) :
    (∑ q : Fin K, decrementComposition i b q) + 1 =
      ∑ q : Fin K, b q := by
  classical
  rw [show (∑ q : Fin K, decrementComposition i b q) =
      (b i - 1) + ∑ q ∈ (Finset.univ : Finset (Fin K)) \ {i}, b q by
    simpa [decrementComposition] using
      Finset.sum_update_of_mem (Finset.mem_univ i) b (b i - 1)]
  rw [show (∑ q : Fin K, b q) =
      b i + ∑ q ∈ (Finset.univ : Finset (Fin K)) \ {i}, b q by
    simpa using Finset.sum_update_of_mem
      (Finset.mem_univ i) b (b i)]
  omega

theorem decrement_incrementComposition {K : ℕ} (i : Fin K)
    (b : Fin K → ℕ) :
    decrementComposition i (incrementComposition i b) = b := by
  funext q
  by_cases hqi : q = i
  · subst q
    simp
  · simp [hqi]

theorem increment_decrementComposition {K : ℕ} (i : Fin K)
    (b : Fin K → ℕ) (hi : 0 < b i) :
    incrementComposition i (decrementComposition i b) = b := by
  funext q
  by_cases hqi : q = i
  · subst q
    simp [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi.ne')]
  · simp [hqi]

theorem incrementComposition_mem_compositions {K : ℕ} (hK : 0 < K)
    (i : Fin K) {b : Fin K → ℕ} (hb : b ∈ compositionsOf K (K - 1)) :
    incrementComposition i b ∈ compositions K := by
  rw [mem_compositions, sum_incrementComposition,
    mem_compositionsOf.mp hb, Nat.sub_add_cancel (by omega : 1 ≤ K)]

theorem decrementComposition_mem_compositionsOf {K : ℕ} (hK : 0 < K)
    (i : Fin K) {b : Fin K → ℕ} (hb : b ∈ compositions K)
    (hi : 0 < b i) :
    decrementComposition i b ∈ compositionsOf K (K - 1) := by
  rw [mem_compositionsOf]
  have hsum := sum_decrementComposition i b hi
  rw [mem_compositions.mp hb] at hsum
  omega

theorem compositionFactor_le_increment {K : ℕ} (i : Fin K)
    (b : Fin K → ℕ) (q : Fin K) :
    compositionFactor b q ≤ compositionFactor (incrementComposition i b) q := by
  by_cases hqi : q = i
  · subst q
    simp only [compositionFactor, incrementComposition_same, pow_succ]
    have hp : 0 ≤ (2 : ℝ) ^ b i := by positivity
    nlinarith
  · simp [compositionFactor, incrementComposition, hqi]

theorem compositionPenalty_le_increment {K : ℕ} (i : Fin K)
    (b : Fin K → ℕ) :
    compositionPenalty b ≤ compositionPenalty (incrementComposition i b) := by
  rw [compositionPenalty, compositionPenalty]
  apply prefixProductMass_mono_of_forall₂
  rw [List.forall₂_iff_get]
  constructor
  · simp
  · intro q hq₁ hq₂
    simp only [List.length_ofFn] at hq₁ hq₂
    simp only [List.get_ofFn]
    exact ⟨(compositionFactor_pos b ⟨q, hq₁⟩).le,
      compositionFactor_le_increment i b ⟨q, hq₁⟩⟩

theorem compositionFactorial_increment {K : ℕ} (i : Fin K)
    (b : Fin K → ℕ) :
    compositionFactorial (incrementComposition i b) =
      (b i + 1 : ℕ) * compositionFactorial b := by
  classical
  dsimp [compositionFactorial]
  have hupd :
      (fun q : Fin K ↦ ((incrementComposition i b q).factorial : ℝ)) =
        Function.update (fun q : Fin K ↦ ((b q).factorial : ℝ)) i
          (((b i + 1).factorial : ℕ) : ℝ) := by
    funext q
    by_cases hqi : q = i
    · subst q
      simp
    · simp [incrementComposition, hqi]
  rw [hupd]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [show (∏ q : Fin K, ((b q).factorial : ℝ)) =
      ((b i).factorial : ℝ) *
        ∏ q ∈ (Finset.univ : Finset (Fin K)) \ {i}, (b q).factorial by
    simpa using Finset.prod_update_of_mem (Finset.mem_univ i)
      (fun q : Fin K ↦ ((b q).factorial : ℝ)) ((b i).factorial : ℝ)]
  rw [Nat.factorial_succ]
  push_cast
  ring

theorem coordinate_mul_cycleWeight_increment_le {K : ℕ} (hK : 0 < K)
    (i : Fin K) (b : Fin K → ℕ) :
    ((incrementComposition i b i : ℕ) : ℝ) *
        compositionCycleWeight (incrementComposition i b) ≤
      compositionCycleWeight b := by
  have hfac : 0 < compositionFactorial b := by
    dsimp [compositionFactorial]
    positivity
  have hpen : 0 < compositionPenalty b :=
    compositionPenalty_pos_of_pos_length hK b
  have hpenInc : 0 < compositionPenalty (incrementComposition i b) :=
    compositionPenalty_pos_of_pos_length hK _
  have hmono := compositionPenalty_le_increment i b
  rw [compositionCycleWeight, compositionCycleWeight,
    compositionFactorial_increment, incrementComposition_same]
  push_cast
  have hb : (0 : ℝ) < b i + 1 := by positivity
  calc
    ((b i : ℝ) + 1) *
        (1 / (((b i : ℝ) + 1) * compositionFactorial b *
          compositionPenalty (incrementComposition i b))) =
        1 / (compositionFactorial b *
          compositionPenalty (incrementComposition i b)) := by
      field_simp [hb.ne', hfac.ne', hpenInc.ne']
    _ ≤ 1 / (compositionFactorial b * compositionPenalty b) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact mul_le_mul_of_nonneg_left hmono hfac.le

theorem sum_cycleWeight_rotations_pred_le {K : ℕ} (hK : 0 < K)
    {b : Fin K → ℕ} (hb : b ∈ compositionsOf K (K - 1)) :
    (∑ r : Fin K, compositionCycleWeight (rotateComposition r b)) ≤
      2 / compositionFactorial b := by
  let l := List.ofFn (compositionFactor b)
  have hl : l ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    simp [l, hK.ne'] at this
  have hpos : ∀ x ∈ l, 0 < x := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact compositionFactor_pos b i
  have hprodLe : l.prod ≤ 1 :=
    prod_compositionFactor_le_one (by omega : K - 1 ≤ K) hb
  have hcycle := sum_inv_prefixProductMass_rotate_le_inv_prod hl hpos hprodLe
  have hinvProd : 1 / l.prod = 2 := by
    have h := inv_prod_compositionFactor_eq_pow_sub
      (b := b) (by omega : K - 1 ≤ K) hb
    rw [show K - (K - 1) = 1 by omega] at h
    norm_num at h ⊢
    simpa [l] using h
  have hfac : 0 ≤ 1 / compositionFactorial b := by
    exact div_nonneg zero_le_one (by
      dsimp [compositionFactorial]
      positivity)
  calc
    (∑ r : Fin K, compositionCycleWeight (rotateComposition r b)) =
        (1 / compositionFactorial b) *
          ∑ r : Fin K,
            1 / compositionPenalty (rotateComposition r b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [compositionCycleWeight, compositionFactorial_rotate]
      field_simp
    _ ≤ (1 / compositionFactorial b) * (1 / l.prod) := by
      apply mul_le_mul_of_nonneg_left _ hfac
      calc
        (∑ r : Fin K,
            1 / compositionPenalty (rotateComposition r b)) =
            ∑ r : Fin K,
              1 / prefixProductMass (l.rotate r.val) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [compositionPenalty]
          have hfactor :
              compositionFactor (rotateComposition r b) =
                rotateComposition r (compositionFactor b) := by
            funext q
            rfl
          rw [hfactor, ofFn_rotateComposition]
        _ =
            ∑ r ∈ Finset.range K,
              1 / prefixProductMass (l.rotate r) := by
          exact (Finset.sum_range
            (fun r : ℕ ↦ 1 / prefixProductMass (l.rotate r))).symm
        _ ≤ 1 / l.prod := by simpa [l] using hcycle
    _ = 2 / compositionFactorial b := by rw [hinvProd]; ring

theorem card_mul_sum_cycleWeight_pred_le {K : ℕ} (hK : 0 < K) :
    (K : ℝ) *
        (∑ b ∈ compositionsOf K (K - 1), compositionCycleWeight b) ≤
      2 * ((K : ℝ) ^ (K - 1) / ((K - 1).factorial : ℝ)) := by
  calc
    (K : ℝ) *
        (∑ b ∈ compositionsOf K (K - 1), compositionCycleWeight b) =
        ∑ r : Fin K,
          ∑ b ∈ compositionsOf K (K - 1), compositionCycleWeight b := by simp
    _ = ∑ r : Fin K,
          ∑ b ∈ compositionsOf K (K - 1),
            compositionCycleWeight (rotateComposition r b) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_equiv (rotateComposition r)
        (fun b ↦ by simp only [mem_compositionsOf, sum_rotateComposition])
        (fun b hb ↦ rfl) |>.symm
    _ = ∑ b ∈ compositionsOf K (K - 1),
          ∑ r : Fin K,
            compositionCycleWeight (rotateComposition r b) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ b ∈ compositionsOf K (K - 1),
          2 / compositionFactorial b := by
      exact Finset.sum_le_sum fun b hb ↦ sum_cycleWeight_rotations_pred_le hK hb
    _ = 2 * ((K : ℝ) ^ (K - 1) / ((K - 1).factorial : ℝ)) := by
      calc
        (∑ b ∈ compositionsOf K (K - 1),
            2 / compositionFactorial b) =
            2 * ∑ b ∈ compositionsOf K (K - 1),
              1 / compositionFactorial b := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
        _ = _ := by rw [sum_inv_compositionFactorial_compositionsOf]

theorem sum_cycleWeight_pred_le_two_cycleMass {K : ℕ} (hK : 0 < K) :
    (∑ b ∈ compositionsOf K (K - 1), compositionCycleWeight b) ≤
      2 * ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by
  have hmain := card_mul_sum_cycleWeight_pred_le hK
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hmul : (K : ℝ) *
      (∑ b ∈ compositionsOf K (K - 1), compositionCycleWeight b) ≤
      (K : ℝ) *
        (2 * ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ))) := calc
    (K : ℝ) *
        (∑ b ∈ compositionsOf K (K - 1), compositionCycleWeight b) ≤
        2 * ((K : ℝ) ^ (K - 1) / ((K - 1).factorial : ℝ)) := hmain
    _ = (K : ℝ) *
        (2 * ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ))) := by
      have hfac : (K.factorial : ℝ) =
          (K : ℝ) * ((K - 1).factorial : ℝ) := by
        conv_lhs => rw [show K = (K - 1) + 1 by omega]
        rw [Nat.factorial_succ, Nat.cast_mul]
        have hkcast : (((K - 1) + 1 : ℕ) : ℝ) = (K : ℝ) := by
          norm_cast
          omega
        rw [hkcast]
      rw [hfac]
      field_simp
  nlinarith

theorem sum_coordinate_mul_cycleWeight_le {K : ℕ} (hK : 0 < K)
    (i : Fin K) :
    (∑ b ∈ compositions K,
        (b i : ℝ) * compositionCycleWeight b) ≤
      2 * ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by
  classical
  let P := (compositions K).filter (fun b ↦ 0 < b i)
  let Q := compositionsOf K (K - 1)
  have hfilter :
      (∑ b ∈ compositions K,
          (b i : ℝ) * compositionCycleWeight b) =
        ∑ b ∈ P, (b i : ℝ) * compositionCycleWeight b := by
    symm
    apply Finset.sum_subset
    · intro b hb
      exact (Finset.mem_filter.mp hb).1
    · intro b hb hnot
      have hzero : b i = 0 := by
        by_contra hne
        have hpos : 0 < b i := Nat.pos_of_ne_zero hne
        exact hnot (Finset.mem_filter.mpr ⟨hb, hpos⟩)
      simp [hzero]
  have hreindex :
      (∑ b ∈ P, (b i : ℝ) * compositionCycleWeight b) =
        ∑ c ∈ Q,
          ((incrementComposition i c i : ℕ) : ℝ) *
            compositionCycleWeight (incrementComposition i c) := by
    symm
    refine Finset.sum_bij'
      (fun c _hc ↦ incrementComposition i c)
      (fun b _hb ↦ decrementComposition i b) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      have hcQ : c ∈ compositionsOf K (K - 1) := hc
      apply Finset.mem_filter.mpr
      exact ⟨incrementComposition_mem_compositions hK i hcQ, by simp⟩
    · intro b hb
      have hbData := Finset.mem_filter.mp hb
      exact decrementComposition_mem_compositionsOf hK i hbData.1 hbData.2
    · intro c hc
      exact decrement_incrementComposition i c
    · intro b hb
      exact increment_decrementComposition i b (Finset.mem_filter.mp hb).2
    · intro c hc
      rfl
  rw [hfilter, hreindex]
  calc
    (∑ c ∈ Q,
        ((incrementComposition i c i : ℕ) : ℝ) *
          compositionCycleWeight (incrementComposition i c)) ≤
        ∑ c ∈ Q, compositionCycleWeight c := by
      exact Finset.sum_le_sum fun c hc ↦
        coordinate_mul_cycleWeight_increment_le hK i c
    _ ≤ 2 * ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by
      simpa [Q] using sum_cycleWeight_pred_le_two_cycleMass hK

/-- The logarithmic size cost of a block-cardinality vector. -/
noncomputable def compositionSizeCost {K : ℕ} (b : Fin K → ℕ) : ℝ :=
  ∑ i : Fin K, (b i : ℝ) * (2 : ℝ) ^ i.val

theorem compositionSizeCost_nonneg {K : ℕ} (b : Fin K → ℕ) :
    0 ≤ compositionSizeCost b := by
  apply Finset.sum_nonneg
  intro i hi
  positivity

theorem sum_two_pow_fin_le (K : ℕ) :
    (∑ i : Fin K, (2 : ℝ) ^ i.val) ≤ (2 : ℝ) ^ K := by
  have heq : ∀ n : ℕ,
      (∑ i : Fin n, (2 : ℝ) ^ i.val) = (2 : ℝ) ^ n - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ]
        rw [← Finset.sum_mul, ih]
        ring
  rw [heq K]
  exact sub_le_self _ zero_le_one

theorem compositionSizeCost_firstMoment_le {K : ℕ} (hK : 0 < K) :
    (∑ b ∈ compositions K,
        compositionCycleWeight b * compositionSizeCost b) ≤
      (2 : ℝ) ^ (K + 1) *
        ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by
  let S : ℝ := (K : ℝ) ^ (K - 1) / (K.factorial : ℝ)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  calc
    (∑ b ∈ compositions K,
        compositionCycleWeight b * compositionSizeCost b) =
        ∑ i : Fin K, (2 : ℝ) ^ i.val *
          ∑ b ∈ compositions K,
            (b i : ℝ) * compositionCycleWeight b := by
      calc
        (∑ b ∈ compositions K,
            compositionCycleWeight b * compositionSizeCost b) =
            ∑ b ∈ compositions K, ∑ i : Fin K,
              compositionCycleWeight b *
                ((b i : ℝ) * (2 : ℝ) ^ i.val) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [compositionSizeCost, Finset.mul_sum]
        _ = ∑ i : Fin K, ∑ b ∈ compositions K,
              compositionCycleWeight b *
                ((b i : ℝ) * (2 : ℝ) ^ i.val) := by
          rw [Finset.sum_comm]
        _ = ∑ i : Fin K, (2 : ℝ) ^ i.val *
              ∑ b ∈ compositions K,
                (b i : ℝ) * compositionCycleWeight b := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ ≤ ∑ i : Fin K, (2 : ℝ) ^ i.val * (2 * S) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (by simpa [S] using sum_coordinate_mul_cycleWeight_le hK i)
        (by positivity)
    _ = (2 * S) * ∑ i : Fin K, (2 : ℝ) ^ i.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (2 * S) * (2 : ℝ) ^ K :=
      mul_le_mul_of_nonneg_left (sum_two_pow_fin_le K)
        (mul_nonneg (by norm_num) hS)
    _ = (2 : ℝ) ^ (K + 1) * S := by rw [pow_succ]; ring

/-- Ford-capped compositions whose whole block product fits in a fixed
constant multiple of the final double-exponential scale. -/
noncomputable def sizedCappedCompositions (M K : ℕ) :
    Finset (Fin K → ℕ) :=
  (cappedCompositions M K).filter fun b ↦
    compositionSizeCost b ≤ 16 * (2 : ℝ) ^ K

theorem mem_sizedCappedCompositions {M K : ℕ} {b : Fin K → ℕ} :
    b ∈ sizedCappedCompositions M K ↔
      b ∈ cappedCompositions M K ∧
        compositionSizeCost b ≤ 16 * (2 : ℝ) ^ K := by
  simp [sizedCappedCompositions]

theorem sizedCappedCompositions_subset_capped (M K : ℕ) :
    sizedCappedCompositions M K ⊆ cappedCompositions M K := by
  intro b hb
  exact (mem_sizedCappedCompositions.mp hb).1

theorem badSize_cycleWeight_le_eighth {K : ℕ} (hK : 0 < K) :
    (∑ b ∈ (compositions K).filter
        (fun b ↦ 16 * (2 : ℝ) ^ K < compositionSizeCost b),
      compositionCycleWeight b) ≤
      (1 / 8 : ℝ) *
        ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) := by
  let S : ℝ := (K : ℝ) ^ (K - 1) / (K.factorial : ℝ)
  let T : ℝ := 16 * (2 : ℝ) ^ K
  let B := (compositions K).filter
    (fun b ↦ T < compositionSizeCost b)
  have hT : 0 < T := by dsimp [T]; positivity
  have hw : ∀ b : Fin K → ℕ, 0 ≤ compositionCycleWeight b :=
    compositionCycleWeight_nonneg
  have hmarkov : T * (∑ b ∈ B, compositionCycleWeight b) ≤
      ∑ b ∈ compositions K,
        compositionCycleWeight b * compositionSizeCost b := by
    calc
      T * (∑ b ∈ B, compositionCycleWeight b) =
          ∑ b ∈ B, T * compositionCycleWeight b := by
        rw [Finset.mul_sum]
      _ ≤ ∑ b ∈ B,
          compositionCycleWeight b * compositionSizeCost b := by
        apply Finset.sum_le_sum
        intro b hb
        have hbT := (Finset.mem_filter.mp hb).2.le
        nlinarith [hw b]
      _ ≤ ∑ b ∈ compositions K,
          compositionCycleWeight b * compositionSizeCost b := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro b hb
          exact (Finset.mem_filter.mp hb).1
        · intro b hb hnot
          exact mul_nonneg (hw b) (compositionSizeCost_nonneg b)
  have hmoment := compositionSizeCost_firstMoment_le hK
  have hbound : T * (∑ b ∈ B, compositionCycleWeight b) ≤
      T * ((1 / 8 : ℝ) * S) := by
    calc
      T * (∑ b ∈ B, compositionCycleWeight b) ≤
          (2 : ℝ) ^ (K + 1) * S := hmarkov.trans (by simpa [S] using hmoment)
      _ = T * ((1 / 8 : ℝ) * S) := by
        dsimp [T]
        rw [pow_succ]
        ring
  have hfinal : (∑ b ∈ B, compositionCycleWeight b) ≤
      (1 / 8 : ℝ) * S := by
    nlinarith
  simpa [B, T, S] using hfinal

theorem sizedCappedComposition_cycleWeight_lower {M K : ℕ}
    (hM : 3 ≤ M) (hK : 0 < K) :
    (1 / 2 : ℝ) *
        ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ)) ≤
      ∑ b ∈ sizedCappedCompositions M K, compositionCycleWeight b := by
  let S : ℝ := (K : ℝ) ^ (K - 1) / (K.factorial : ℝ)
  let G : ℝ := ∑ b ∈ sizedCappedCompositions M K,
    compositionCycleWeight b
  let C : ℝ := ∑ b ∈ cappedCompositions M K,
    compositionCycleWeight b
  let D : ℝ := ∑ b ∈ (compositions K).filter
      (fun b ↦ 16 * (2 : ℝ) ^ K < compositionSizeCost b),
    compositionCycleWeight b
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hcap : (1 / 2 : ℝ) * S ≤ C := by
    simpa [S, C] using cappedComposition_cycleWeight_lower hM hK
  have hsplit : C ≤ G + D := by
    calc
      C = ∑ b ∈ cappedCompositions M K,
          ((if compositionSizeCost b ≤ 16 * (2 : ℝ) ^ K
            then compositionCycleWeight b else 0) +
          if 16 * (2 : ℝ) ^ K < compositionSizeCost b
            then compositionCycleWeight b else 0) := by
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hs : compositionSizeCost b ≤ 16 * (2 : ℝ) ^ K
        · simp [hs, not_lt_of_ge hs]
        · have : 16 * (2 : ℝ) ^ K < compositionSizeCost b := lt_of_not_ge hs
          simp [hs, this]
      _ = G + ∑ b ∈ cappedCompositions M K,
          if 16 * (2 : ℝ) ^ K < compositionSizeCost b
            then compositionCycleWeight b else 0 := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp [G, sizedCappedCompositions, Finset.sum_filter]
      _ ≤ G + D := by
        have htail :
            (∑ b ∈ cappedCompositions M K,
              if 16 * (2 : ℝ) ^ K < compositionSizeCost b
                then compositionCycleWeight b else 0) ≤ D := by
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro b hb
            have hbData := Finset.mem_filter.mp hb
            exact Finset.mem_filter.mpr
              ⟨(mem_cappedCompositions.mp hbData.1).1, hbData.2⟩
          · intro b hb hnot
            exact compositionCycleWeight_nonneg b
        linarith
  have hbad : D ≤ (1 / 8 : ℝ) * S := by
    simpa [D, S] using badSize_cycleWeight_le_eighth hK
  have : (3 / 8 : ℝ) * S ≤ G := by linarith
  have hwrong : (1 / 2 : ℝ) * S ≤ G := by
    -- The one-sided cap loses at most `1/32`, not merely one half.
    have hcover := sum_cycleWeight_le_capped_add_bad M K
    have hunrestricted :
        (∑ b ∈ compositions K, compositionCycleWeight b) = S := by
      simpa [S] using sum_compositionCycleWeight K hK
    have hcapBad := sum_badFordCoordinateWeight_le
      (K := K) (by omega : 2 ≤ M)
    have hcoeff : 16 / (2 : ℝ) ^ (M * M) ≤ 1 / 8 := by
      have hsq : 9 ≤ M * M := by nlinarith
      have hp : (128 : ℝ) ≤ (2 : ℝ) ^ (M * M) := by
        calc
          (128 : ℝ) ≤ (512 : ℝ) := by norm_num
          _ = (2 : ℝ) ^ 9 := by norm_num
          _ ≤ (2 : ℝ) ^ (M * M) := by gcongr <;> norm_num
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (M * M))).2
      nlinarith
    have hcapBad' :
        (∑ i : Fin K,
            ∑ b ∈ (compositions K).filter
                (fun b ↦ M * (M + i.val) < b i),
              compositionCycleWeight b) ≤ (1 / 8 : ℝ) * S := by
      have hcapRaw :
          (∑ i : Fin K,
              ∑ b ∈ (compositions K).filter
                  (fun b ↦ M * (M + i.val) < b i),
                compositionCycleWeight b) ≤
            (16 / (2 : ℝ) ^ (M * M)) * S := by
        simpa [S] using hcapBad
      exact hcapRaw.trans (mul_le_mul_of_nonneg_right hcoeff hS)
    rw [hunrestricted] at hcover
    linarith
  simpa [G, S] using hwrong

end Erdos446
