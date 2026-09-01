/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.NumberTheory.WellApproximable

/-!
# Geometric reduction of two approximation layers to a finite pair count

This file contains the measure-theoretic and circle-geometric part of the
Pollington--Vaughan overlap estimate.  The remaining estimate is purely a
finite count of pairs of reduced residues whose associated balls meet.
-/

open Filter Metric Set MeasureTheory
open scoped BigOperators ENNReal MeasureTheory Topology

namespace Erdos999

noncomputable section

private def residueBall (q : ℕ) (L : ℝ) (a : Fin q) : Set UnitAddCircle :=
  ball (↑((a : ℝ) / q) : UnitAddCircle) (L / q)

private def isRelevantPair (q r : ℕ) (L M : ℝ)
    (z : Fin q × Fin r) : Prop :=
  q.Coprime z.1 ∧ r.Coprime z.2 ∧
    ¬Disjoint (residueBall q L z.1) (residueBall r M z.2)

private noncomputable local instance relevantPairDecidable
    (q r : ℕ) (L M : ℝ) (z : Fin q × Fin r) :
    Decidable (isRelevantPair q r L M z) :=
  Classical.propDecidable _

/-- The number of pairs of reduced residues whose open approximation balls
meet. -/
def overlapPairCount (q r : ℕ) (L M : ℝ) : ℕ :=
  by
    classical
    exact ((Finset.univ : Finset (Fin q × Fin r)).filter
      (isRelevantPair q r L M)).card

/-- A nonpositive left radius contributes no relevant pair. -/
theorem overlapPairCount_eq_zero_of_left_nonpos
    (q r : ℕ) {L M : ℝ} (hL : L ≤ 0) :
    overlapPairCount q r L M = 0 := by
  classical
  rw [overlapPairCount, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro z hz hrel
  apply hrel.2.2
  have hradius : L / (q : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hL (by positivity)
  have hempty : residueBall q L z.1 = ∅ :=
    Metric.ball_eq_empty.mpr hradius
  rw [hempty]
  exact empty_disjoint _

/-- A nonpositive right radius contributes no relevant pair. -/
theorem overlapPairCount_eq_zero_of_right_nonpos
    (q r : ℕ) {L M : ℝ} (hM : M ≤ 0) :
    overlapPairCount q r L M = 0 := by
  classical
  rw [overlapPairCount, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro z hz hrel
  apply hrel.2.2
  have hradius : M / (r : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hM (by positivity)
  have hempty : residueBall r M z.2 = ∅ :=
    Metric.ball_eq_empty.mpr hradius
  rw [hempty]
  exact disjoint_empty _

/-- A purely arithmetic relaxation of relevance: the two reduced rational
centres are close after an integral translation. -/
def isNearbyReducedPair (q r : ℕ) (L M : ℝ)
    (z : Fin q × Fin r) : Prop :=
  q.Coprime z.1 ∧ r.Coprime z.2 ∧
    ∃ k : ℤ,
      |(z.1 : ℝ) / q - (z.2 : ℝ) / r - k| < L / q + M / r

private noncomputable local instance nearbyReducedPairDecidable
    (q r : ℕ) (L M : ℝ) (z : Fin q × Fin r) :
    Decidable (isNearbyReducedPair q r L M z) :=
  Classical.propDecidable _

/-- The number of arithmetically nearby pairs of reduced residues. -/
def nearbyReducedPairCount (q r : ℕ) (L M : ℝ) : ℕ :=
  by
    classical
    exact ((Finset.univ : Finset (Fin q × Fin r)).filter
      (isNearbyReducedPair q r L M)).card

private lemma approxAddOrderOf_eq_iUnion_residueBall
    {q : ℕ} (hq : 0 < q) (L : ℝ) :
    approxAddOrderOf UnitAddCircle q (L / q) =
      ⋃ a : Fin q, if q.Coprime a then residueBall q L a else ∅ := by
  ext x
  rw [UnitAddCircle.mem_approxAddOrderOf_iff hq]
  simp only [mem_iUnion]
  constructor
  · rintro ⟨a, ha, hcop, hx⟩
    let z : Fin q := ⟨a, ha⟩
    refine ⟨z, ?_⟩
    rw [if_pos]
    · simpa [residueBall, z, dist_eq_norm] using hx
    · exact (show a.Coprime q from hcop).symm
  · rintro ⟨a, hx⟩
    by_cases hcop : q.Coprime (a : ℕ)
    · rw [if_pos hcop] at hx
      exact ⟨a, a.isLt, hcop.symm.gcd_eq_one,
        by simpa [residueBall, dist_eq_norm] using hx⟩
    · simp [hcop] at hx

private lemma volumeReal_ball_unitAddCircle_le (x : UnitAddCircle) (rho : ℝ)
    (hrho : 0 ≤ rho) :
    volume.real (ball x rho) ≤ 2 * rho := by
  rw [measureReal_def]
  have hvolume : volume (ball x rho) =
      ENNReal.ofReal (min 1 (2 * rho)) := by
    rw [measure_congr AddCircle.closedBall_ae_eq_ball.symm,
      AddCircle.volume_closedBall]
  rw [hvolume, ENNReal.toReal_ofReal]
  · exact min_le_right _ _
  · exact le_min (by norm_num) (mul_nonneg (by norm_num) hrho)

private lemma volumeReal_residueBall_inter_le
    {q r : ℕ} {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (a : Fin q) (b : Fin r) :
    volume.real ((if q.Coprime a then residueBall q L a else ∅) ∩
        (if r.Coprime b then residueBall r M b else ∅)) ≤
      if isRelevantPair q r L M (a, b) then
        2 * min (L / q) (M / r) else 0 := by
  by_cases hqcop : q.Coprime (a : ℕ)
  · by_cases hrcop : r.Coprime (b : ℕ)
    · by_cases hinter : Disjoint (residueBall q L a) (residueBall r M b)
      · rw [if_pos hqcop, if_pos hrcop,
          if_neg (fun h ↦ h.2.2 hinter), hinter.inter_eq, measureReal_empty]
      · have hrel : isRelevantPair q r L M (a, b) :=
          ⟨hqcop, hrcop, hinter⟩
        rw [if_pos hqcop, if_pos hrcop, if_pos hrel]
        rcases le_total (L / q) (M / r) with hle | hle
        · calc
            volume.real (residueBall q L a ∩ residueBall r M b) ≤
                volume.real (residueBall q L a) :=
              measureReal_mono inter_subset_left (measure_ne_top _ _)
            _ ≤ 2 * (L / q) := volumeReal_ball_unitAddCircle_le _ _
              (div_nonneg hL (by positivity))
            _ = 2 * min (L / q) (M / r) := by rw [min_eq_left hle]
        · calc
            volume.real (residueBall q L a ∩ residueBall r M b) ≤
                volume.real (residueBall r M b) :=
              measureReal_mono inter_subset_right (measure_ne_top _ _)
            _ ≤ 2 * (M / r) := volumeReal_ball_unitAddCircle_le _ _
              (div_nonneg hM (by positivity))
            _ = 2 * min (L / q) (M / r) := by rw [min_eq_right hle]
    · rw [if_neg hrcop, inter_empty, measureReal_empty,
        if_neg (fun h ↦ hrcop h.2.1)]
  · rw [if_neg hqcop, empty_inter, measureReal_empty,
      if_neg (fun h ↦ hqcop h.1)]

/-- The overlap measure is bounded by twice the smaller physical radius
times the finite number of intersecting reduced-residue ball pairs. -/
theorem volumeReal_approxAddOrderOf_inter_le_pairCount
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r) {L M : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) :
    volume.real (approxAddOrderOf UnitAddCircle q (L / q) ∩
        approxAddOrderOf UnitAddCircle r (M / r)) ≤
      2 * min (L / q) (M / r) * overlapPairCount q r L M := by
  rw [approxAddOrderOf_eq_iUnion_residueBall hq,
    approxAddOrderOf_eq_iUnion_residueBall hr]
  have hset :
      (⋃ a : Fin q, if q.Coprime a then residueBall q L a else ∅) ∩
          (⋃ b : Fin r, if r.Coprime b then residueBall r M b else ∅) =
        ⋃ a : Fin q, ⋃ b : Fin r,
          (if q.Coprime a then residueBall q L a else ∅) ∩
            (if r.Coprime b then residueBall r M b else ∅) := by
    ext x
    simp only [mem_inter_iff, mem_iUnion]
    aesop
  rw [hset]
  calc
    volume.real (⋃ a : Fin q, ⋃ b : Fin r,
        (if q.Coprime a then residueBall q L a else ∅) ∩
          (if r.Coprime b then residueBall r M b else ∅)) ≤
        ∑ a : Fin q, ∑ b : Fin r,
          volume.real ((if q.Coprime a then residueBall q L a else ∅) ∩
            (if r.Coprime b then residueBall r M b else ∅)) := by
      refine (measureReal_iUnion_fintype_le _).trans ?_
      exact Finset.sum_le_sum fun a _ ↦
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ a : Fin q, ∑ b : Fin r,
        if isRelevantPair q r L M (a, b) then
          2 * min (L / q) (M / r) else 0 :=
      Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦
        volumeReal_residueBall_inter_le hL hM a b
    _ = 2 * min (L / q) (M / r) * overlapPairCount q r L M := by
      classical
      rw [← Finset.sum_product', Finset.univ_product_univ,
        ← Finset.sum_filter]
      simp only [overlapPairCount, Finset.sum_const, nsmul_eq_mul]
      ring

/-- A bound for the finite relevant-pair count with the expected local
densities immediately gives the desired product bound for the overlap
measure. -/
theorem volumeReal_approxAddOrderOf_inter_le_of_pairCount
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r) {L M K : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hcount : (overlapPairCount q r L M : ℝ) ≤
      K * (q.totient : ℝ) * (r.totient : ℝ) *
        max (L / q) (M / r)) :
    volume.real (approxAddOrderOf UnitAddCircle q (L / q) ∩
        approxAddOrderOf UnitAddCircle r (M / r)) ≤
      (2 * K) * ((q.totient : ℝ) * L / q) *
        ((r.totient : ℝ) * M / r) := by
  have hmin : 0 ≤ min (L / q) (M / r) :=
    le_min (div_nonneg hL (by positivity)) (div_nonneg hM (by positivity))
  calc
    volume.real (approxAddOrderOf UnitAddCircle q (L / q) ∩
        approxAddOrderOf UnitAddCircle r (M / r)) ≤
        2 * min (L / q) (M / r) * overlapPairCount q r L M :=
      volumeReal_approxAddOrderOf_inter_le_pairCount hq hr hL hM
    _ ≤ 2 * min (L / q) (M / r) *
        (K * (q.totient : ℝ) * (r.totient : ℝ) *
          max (L / q) (M / r)) := by
      exact mul_le_mul_of_nonneg_left hcount (mul_nonneg (by norm_num) hmin)
    _ = (2 * K) * ((q.totient : ℝ) * L / q) *
        ((r.totient : ℝ) * M / r) := by
      rw [show 2 * min (L / q) (M / r) *
          (K * (q.totient : ℝ) * (r.totient : ℝ) *
            max (L / q) (M / r)) =
        (2 * K * (q.totient : ℝ) * (r.totient : ℝ)) *
          (min (L / q) (M / r) * max (L / q) (M / r)) by ring]
      rw [min_mul_max]
      ring

private lemma dist_residue_centers_lt_add_of_relevant
    {q r : ℕ} {L M : ℝ} {a : Fin q} {b : Fin r}
    (h : isRelevantPair q r L M (a, b)) :
    dist (↑((a : ℝ) / q) : UnitAddCircle)
        (↑((b : ℝ) / r) : UnitAddCircle) < L / q + M / r := by
  rcases h with ⟨hqcop, hrcop, hinter⟩
  rw [Set.not_disjoint_iff] at hinter
  rcases hinter with ⟨x, hxa, hxb⟩
  change dist x (↑((a : ℝ) / q) : UnitAddCircle) < L / q at hxa
  change dist x (↑((b : ℝ) / r) : UnitAddCircle) < M / r at hxb
  calc
    dist (↑((a : ℝ) / q) : UnitAddCircle)
        (↑((b : ℝ) / r) : UnitAddCircle) ≤
        dist (↑((a : ℝ) / q) : UnitAddCircle) x +
          dist x (↑((b : ℝ) / r) : UnitAddCircle) := dist_triangle _ _ _
    _ < L / q + M / r := add_lt_add (by simpa [dist_comm] using hxa) hxb

/-- Every relevant pair yields an integer translate for which the ordinary
rational-center difference is smaller than the sum of the two radii. -/
theorem exists_int_abs_centerDifference_lt_of_mem_overlapPair
    {q r : ℕ} {L M : ℝ} {z : Fin q × Fin r}
    (hz : z ∈ (Finset.univ.filter (isRelevantPair q r L M) :
      Finset (Fin q × Fin r))) :
    ∃ k : ℤ,
      |(z.1 : ℝ) / q - (z.2 : ℝ) / r - k| < L / q + M / r := by
  classical
  have hrel : isRelevantPair q r L M z := (Finset.mem_filter.mp hz).2
  have hdist := dist_residue_centers_lt_add_of_relevant hrel
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq] at hdist
  exact ⟨round ((z.1 : ℝ) / q - (z.2 : ℝ) / r), by simpa using hdist⟩

/-- Forgetting the actual intersection point and retaining only the nearby
centres can only enlarge the finite pair count. -/
theorem overlapPairCount_le_nearbyReducedPairCount
    (q r : ℕ) (L M : ℝ) :
    overlapPairCount q r L M ≤ nearbyReducedPairCount q r L M := by
  classical
  apply Finset.card_le_card
  intro z hzmem
  have hclose := exists_int_abs_centerDifference_lt_of_mem_overlapPair hzmem
  rw [Finset.mem_filter] at hzmem ⊢
  refine ⟨Finset.mem_univ z, ?_⟩
  have hrel : isRelevantPair q r L M z := hzmem.2
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  exact hclose

end

end Erdos999
