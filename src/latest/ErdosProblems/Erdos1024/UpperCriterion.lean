/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1024.UpperCounts
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.BigOperators

/-!
# A two-charge local-lemma criterion

This file isolates the elementary product estimates used by the random
construction.  Overlap events receive one common charge, while hole events
may receive charges depending on the hole.
-/

open scoped BigOperators

namespace Erdos1024
namespace Upper

/-- The overlap coordinates occurring in a finset of bad indices. -/
noncomputable def overlapProjection {n t : ℕ} (N : Finset (BadIndex n t)) :
    Finset (OverlapIndex n) := by
  classical
  exact Finset.univ.filter fun a ↦ Sum.inl a ∈ N

/-- The hole coordinates occurring in a finset of bad indices. -/
noncomputable def holeProjection {n t : ℕ} (N : Finset (BadIndex n t)) :
    Finset (HoleIndex n t) := by
  classical
  exact Finset.univ.filter fun S ↦ Sum.inr S ∈ N

lemma prod_badIndex_eq_projections {n t : ℕ}
    (N : Finset (BadIndex n t)) (f : BadIndex n t → ℝ) :
    (∏ i ∈ N, f i) =
      (∏ a ∈ overlapProjection N, f (Sum.inl a)) *
        ∏ S ∈ holeProjection N, f (Sum.inr S) := by
  classical
  calc
    (∏ i ∈ N, f i) = ∏ i : BadIndex n t, if i ∈ N then f i else 1 := by
      simpa using (Finset.prod_filter (s := (Finset.univ : Finset (BadIndex n t)))
        (p := fun i ↦ i ∈ N) f).symm
    _ = (∏ a : OverlapIndex n,
          if Sum.inl a ∈ N then f (Sum.inl a) else 1) *
        ∏ S : HoleIndex n t,
          if Sum.inr S ∈ N then f (Sum.inr S) else 1 :=
      Fintype.prod_sum_type _
    _ = (∏ a ∈ overlapProjection N, f (Sum.inl a)) *
        ∏ S ∈ holeProjection N, f (Sum.inr S) := by
      congr 1
      · symm
        unfold overlapProjection
        rw [Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro a _ha
        by_cases h : Sum.inl a ∈ N <;> simp [h]
      · symm
        unfold holeProjection
        rw [Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro S _hS
        by_cases h : Sum.inr S ∈ N <;> simp [h]

/-- The elementary union-bound lower estimate
`1 - sum y ≤ product (1-y)` for numbers in `[0,1]`. -/
lemma one_sub_sum_le_prod_one_sub {ι : Type*} {s : Finset ι} {y : ι → ℝ}
    (hy0 : ∀ i ∈ s, 0 ≤ y i) (hy1 : ∀ i ∈ s, y i ≤ 1) :
    1 - ∑ i ∈ s, y i ≤ ∏ i ∈ s, (1 - y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hya0 := hy0 a (Finset.mem_insert_self _ _)
      have hya1 := hy1 a (Finset.mem_insert_self _ _)
      have hsum0 : 0 ≤ ∑ i ∈ s, y i :=
        Finset.sum_nonneg fun i hi ↦ hy0 i (Finset.mem_insert_of_mem hi)
      have hih := ih
        (fun i hi ↦ hy0 i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hy1 i (Finset.mem_insert_of_mem hi))
      have hfac : 0 ≤ 1 - y a := sub_nonneg.mpr hya1
      calc
        1 - (y a + ∑ i ∈ s, y i) ≤
            (1 - y a) * (1 - ∑ i ∈ s, y i) := by nlinarith
        _ ≤ (1 - y a) * ∏ i ∈ s, (1 - y i) :=
          mul_le_mul_of_nonneg_left hih hfac

/-- A common charge on overlaps and an indexed charge on holes. -/
def twoCharge {n t : ℕ} (xA : ℝ) (xB : HoleIndex n t → ℝ) :
    BadIndex n t → ℝ
  | Sum.inl _ => xA
  | Sum.inr S => xB S

lemma product_twoCharge_lower {n t : ℕ}
    (N : Finset (BadIndex n t)) (xA : ℝ) (xB : HoleIndex n t → ℝ)
    (hxA0 : 0 ≤ xA) (hxA1 : xA ≤ 1)
    (hxB0 : ∀ S, 0 ≤ xB S) (hxB1 : ∀ S, xB S ≤ 1)
    (htotal : ∑ S, xB S ≤ 1) :
    (1 - xA) ^ (overlapProjection N).card *
        (1 - ∑ S, xB S) ≤
      ∏ i ∈ N, (1 - twoCharge xA xB i) := by
  classical
  rw [prod_badIndex_eq_projections]
  have hA : (∏ a ∈ overlapProjection N,
      (1 - twoCharge xA xB (Sum.inl a))) =
      (1 - xA) ^ (overlapProjection N).card := by
    simp [twoCharge]
  rw [hA]
  have hB := one_sub_sum_le_prod_one_sub
    (s := holeProjection N) (y := xB)
    (fun S _ ↦ hxB0 S) (fun S _ ↦ hxB1 S)
  have hsubset : holeProjection N ⊆ Finset.univ := Finset.subset_univ _
  have hsum : (∑ S ∈ holeProjection N, xB S) ≤ ∑ S, xB S :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset fun S _ _ ↦ hxB0 S
  have htotal0 : 0 ≤ 1 - ∑ S, xB S := sub_nonneg.mpr htotal
  have hbase0 : 0 ≤ (1 - xA) ^ (overlapProjection N).card :=
    pow_nonneg (sub_nonneg.mpr hxA1) _
  apply mul_le_mul_of_nonneg_left _ hbase0
  exact (sub_le_sub_left hsum 1).trans hB

lemma overlapProjection_neighbors_subset {n t : ℕ}
    (i : BadIndex n t) (J : Finset (BadIndex n t)) :
    overlapProjection (J.filter (Dependent i)) ⊆ neighboringOverlaps i := by
  intro a ha
  have ha' : Sum.inl a ∈ J.filter (Dependent i) := by
    simpa [overlapProjection] using ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha').2⟩

/-- Exact cancellation form of the local-lemma criterion. -/
theorem twoCharge_criterion
    {n t K : ℕ} [NeZero K]
    (xA : ℝ) (xB : HoleIndex n t → ℝ)
    (hxAprob : 3 * (((1 : ℝ) / K) ^ 2) = xA)
    (hxA0 : 0 ≤ xA) (hxA1 : xA ≤ 1)
    (hxB0 : ∀ S, 0 ≤ xB S) (hxB1 : ∀ S, xB S ≤ 1)
    (htotal : ∑ S, xB S ≤ 1 / 4)
    (hoverlapLoss : (12 * n : ℝ) * xA ≤ 1 / 4)
    (hholes : ∀ S : HoleIndex n t,
      2 * badProbability K (Sum.inr S) ≤
        xB S * (1 - xA) ^ (6 * n * t.choose 3)) :
    ∀ i (J : Finset (BadIndex n t)), i ∉ J →
      badProbability K i ≤
        twoCharge xA xB i *
          ∏ j ∈ J.filter (Dependent i), (1 - twoCharge xA xB j) := by
  classical
  intro i J _hiJ
  let N := J.filter (Dependent i)
  have htotal' : ∑ S, xB S ≤ 1 := htotal.trans (by norm_num)
  have hprod := product_twoCharge_lower N xA xB hxA0 hxA1 hxB0 hxB1 htotal'
  have hbase0 : 0 ≤ 1 - xA := sub_nonneg.mpr hxA1
  have hholeFactor : 3 / 4 ≤ 1 - ∑ S, xB S := by linarith
  cases i with
  | inl a =>
      have hcard : (overlapProjection N).card ≤ 12 * n :=
        (Finset.card_le_card (overlapProjection_neighbors_subset _ _)).trans
          (card_overlap_neighbors_of_overlap_le a)
      have hpowmono : (1 - xA) ^ (12 * n) ≤
          (1 - xA) ^ (overlapProjection N).card := by
        exact pow_le_pow_of_le_one hbase0 (sub_le_self (1 : ℝ) hxA0) hcard
      have hbern : 1 - (12 * n : ℝ) * xA ≤ (1 - xA) ^ (12 * n) := by
        simpa [sub_eq_add_neg, mul_neg, Nat.cast_mul] using
          (one_add_mul_le_pow (a := -xA) (by linarith [hxA1]) (12 * n))
      have hAfac : 3 / 4 ≤ (1 - xA) ^ (overlapProjection N).card := by
        calc
          3 / 4 ≤ 1 - (12 * n : ℝ) * xA := by linarith
          _ ≤ (1 - xA) ^ (12 * n) := hbern
          _ ≤ _ := hpowmono
      have hprodThird : 1 / 3 ≤
          ∏ j ∈ N, (1 - twoCharge xA xB j) := by
        calc
          1 / 3 ≤ (3 / 4 : ℝ) * (3 / 4) := by norm_num
          _ ≤ (1 - xA) ^ (overlapProjection N).card *
              (1 - ∑ S, xB S) :=
            mul_le_mul hAfac hholeFactor (by norm_num) (pow_nonneg hbase0 _)
          _ ≤ _ := hprod
      change ((1 : ℝ) / K) ^ 2 ≤ xA * ∏ j ∈ N,
        (1 - twoCharge xA xB j)
      have hmul := mul_le_mul_of_nonneg_left hprodThird hxA0
      nlinarith [sq_nonneg ((1 : ℝ) / (K : ℝ))]
  | inr S =>
      have hcard : (overlapProjection N).card ≤ 6 * n * t.choose 3 :=
        (Finset.card_le_card (overlapProjection_neighbors_subset _ _)).trans
          (card_overlap_neighbors_of_hole_le S)
      have hpowmono : (1 - xA) ^ (6 * n * t.choose 3) ≤
          (1 - xA) ^ (overlapProjection N).card := by
        exact pow_le_pow_of_le_one hbase0 (sub_le_self (1 : ℝ) hxA0) hcard
      have hprodHole : (1 - xA) ^ (6 * n * t.choose 3) * (3 / 4) ≤
          ∏ j ∈ N, (1 - twoCharge xA xB j) := by
        calc
          _ ≤ (1 - xA) ^ (overlapProjection N).card *
              (1 - ∑ S, xB S) :=
            mul_le_mul hpowmono hholeFactor (by norm_num) (pow_nonneg hbase0 _)
          _ ≤ _ := hprod
      change badProbability K (Sum.inr S) ≤
        xB S * ∏ j ∈ N, (1 - twoCharge xA xB j)
      have hxB := hxB0 S
      have hscaled := mul_le_mul_of_nonneg_left hprodHole hxB
      have hq0 : 0 ≤ badProbability K (Sum.inr S) := by
        simp [badProbability]
        positivity
      nlinarith [hholes S]

end Upper
end Erdos1024
