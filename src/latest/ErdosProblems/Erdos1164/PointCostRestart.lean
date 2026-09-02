import ErdosProblems.Erdos1164.PointCost
import ErdosProblems.Erdos1164.HitRace

/-! # Restarting the origin-visit cost at the first visit to zero -/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1164

open Erdos1165 Erdos1165.PlanarPotential Erdos1165.PointBeforeReturn

/-- The first visit to zero occurs at `n`, before the target has been visited. -/
def firstOriginBeforePointAt (x y : Point) (n : ℕ) : Set StepPath :=
  {w | trajectoryFrom x w n = 0 ∧
    ∀ j < n, trajectoryFrom x w j ≠ 0 ∧ trajectoryFrom x w j ≠ y}

private theorem measurableSet_translated_position (x y : Point) (n : ℕ) :
    MeasurableSet[incrementFiltration n] {w : StepPath | trajectoryFrom x w n = y} := by
  have heq : {w : StepPath | trajectoryFrom x w n = y} =
      {w : StepPath | trajectory w n = y - x} := by
    ext w
    simp only [Set.mem_ofPred_eq, trajectoryFrom, eq_sub_iff_add_eq, add_comm]
  rw [heq]
  exact measurableSet_trajectory_eq_filtration n (y - x)

theorem measurableSet_firstOriginBeforePointAt_filtration (x y : Point) (n : ℕ) :
    MeasurableSet[incrementFiltration n] (firstOriginBeforePointAt x y n) := by
  have hp := measurableSet_translated_position x 0 n
  have hbefore : MeasurableSet[incrementFiltration n]
      {w : StepPath | ∀ j < n, trajectoryFrom x w j ≠ 0 ∧ trajectoryFrom x w j ≠ y} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro hj
    exact (incrementFiltration.mono hj.le) _
      (((measurableSet_translated_position x 0 j).compl).inter
        ((measurableSet_translated_position x y j).compl))
  exact hp.inter hbefore

theorem measurableSet_firstOriginBeforePointAt (x y : Point) (n : ℕ) :
    MeasurableSet (firstOriginBeforePointAt x y n) :=
  incrementFiltration.le n _ (measurableSet_firstOriginBeforePointAt_filtration x y n)

theorem firstOriginBeforePointAt_pairwise (x y : Point) :
    Pairwise fun n m ↦
      Disjoint (firstOriginBeforePointAt x y n) (firstOriginBeforePointAt x y m) := by
  intro n m hnm
  rw [Set.disjoint_left]
  intro w hn hm
  rcases lt_or_gt_of_ne hnm with h | h
  · exact (hm.2 n h).1 hn.1
  · exact (hn.2 m h).1 hm.1

theorem firstOriginBeforePointAt_union (x y : Point) :
    (⋃ n, firstOriginBeforePointAt x y n) = hitBeforePoint x 0 y := by
  ext w
  constructor
  · intro hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
    exact ⟨n, hn.1, fun j hj ↦ (hn.2 j hj).2⟩
  · rintro ⟨n, hn, hno⟩
    have hex : ∃ j, trajectoryFrom x w j = 0 := ⟨n, hn⟩
    let j := Nat.find hex
    have hj : trajectoryFrom x w j = 0 := Nat.find_spec hex
    have hjn : j ≤ n := Nat.find_min' hex hn
    refine Set.mem_iUnion.mpr ⟨j, hj, ?_⟩
    intro l hl
    exact ⟨Nat.find_min hex hl, hno l (hl.trans_le hjn)⟩

/-- Shifting time only discards visits from a prefix. -/
theorem originVisits_shift_le (s : WalkPath) (n m : ℕ) :
    originVisits (fun j ↦ s (n + j)) m ≤ originVisits s (n + m) := by
  classical
  apply Finset.card_le_card_of_injOn (fun j ↦ n + j)
  · intro j hj
    have hh := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.add_lt_add_left (Finset.mem_range.mp hh.1) n), hh.2⟩
  · intro i _ j _ hij
    exact Nat.add_left_cancel hij

private theorem restart_at_origin (x : Point) (w : StepPath) (n : ℕ)
    (hn : trajectoryFrom x w n = 0) (j : ℕ) :
    trajectoryFrom 0 (shiftSteps n w) j = trajectoryFrom x w (n + j) := by
  simp only [trajectoryFrom, zero_add]
  rw [← trajectory_add_sub_trajectory]
  have hzero : x + trajectory w n = 0 := hn
  have hx : x = -trajectory w n := eq_neg_of_add_eq_zero_left hzero
  rw [hx]
  abel

private theorem origin_restart_cost_subset (x y : Point) (k n : ℕ) :
    firstOriginBeforePointAt x y n ∩ shiftSteps n ⁻¹' beforePointVisits 0 y k ⊆
      beforePointVisits x y k := by
  rintro w ⟨hw, m, hcount, havoid⟩
  have hrestart : trajectoryFrom 0 (shiftSteps n w) = fun j ↦ trajectoryFrom x w (n + j) :=
    funext (restart_at_origin x w n hw.1)
  rw [hrestart] at hcount
  refine ⟨n + m, hcount.trans (originVisits_shift_le (trajectoryFrom x w) n m), ?_⟩
  intro j hj
  by_cases hjn : j < n
  · exact (hw.2 j hjn).2
  · have h := havoid (j - n) (by omega)
    rw [restart_at_origin x w n hw.1, Nat.add_sub_of_le (by omega : n ≤ j)] at h
    exact h

private theorem origin_restart_cost_factor (x y : Point) (k n : ℕ) :
    fairSteps (firstOriginBeforePointAt x y n ∩ shiftSteps n ⁻¹' beforePointVisits 0 y k) =
      fairSteps (firstOriginBeforePointAt x y n) * fairSteps (beforePointVisits 0 y k) := by
  have hobs : IsMeasurableAtStopping (fun _ : StepPath ↦ n) (firstOriginBeforePointAt x y n) := by
    intro m
    by_cases hm : n = m
    · subst m
      simpa only [Set.ofPred_true, Set.inter_univ] using
        measurableSet_firstOriginBeforePointAt_filtration x y n
    · simp only [hm, Set.ofPred_false, Set.inter_empty, MeasurableSet.empty]
  exact strongMarkov_fullTail (isFiniteStoppingTime_const n) hobs
    (measurableSet_beforePointVisits 0 y k)

/-- The race probability multiplies the fresh origin-started cost probability. -/
theorem beforePointVisits_race_product (x y : Point) (k : ℕ) :
    fairSteps (hitBeforePoint x 0 y) * fairSteps (beforePointVisits 0 y k) ≤
      fairSteps (beforePointVisits x y k) := by
  let pieces : ℕ → Set StepPath := fun n ↦ firstOriginBeforePointAt x y n ∩
    shiftSteps n ⁻¹' beforePointVisits 0 y k
  have hd : Pairwise fun n m ↦ Disjoint (pieces n) (pieces m) := by
    intro n m hnm
    exact (firstOriginBeforePointAt_pairwise x y hnm).mono
      Set.inter_subset_left Set.inter_subset_left
  have hm : ∀ n, MeasurableSet (pieces n) := fun n ↦
    (measurableSet_firstOriginBeforePointAt x y n).inter
      ((measurableSet_beforePointVisits 0 y k).preimage (measurable_shiftSteps n))
  have hsub : (⋃ n, pieces n) ⊆ beforePointVisits x y k :=
    Set.iUnion_subset fun n ↦ origin_restart_cost_subset x y k n
  calc
    fairSteps (hitBeforePoint x 0 y) * fairSteps (beforePointVisits 0 y k) =
        (∑' n, fairSteps (firstOriginBeforePointAt x y n)) *
          fairSteps (beforePointVisits 0 y k) := by
      rw [← measure_iUnion (firstOriginBeforePointAt_pairwise x y)
        (measurableSet_firstOriginBeforePointAt x y), firstOriginBeforePointAt_union]
    _ = ∑' n, fairSteps (pieces n) := by
      rw [← ENNReal.tsum_mul_right]
      congr 1
      funext n
      exact (origin_restart_cost_factor x y k n).symm
    _ = fairSteps (⋃ n, pieces n) := (measure_iUnion hd hm).symm
    _ ≤ _ := measure_mono hsub

theorem beforePointVisits_race_product_real (x y : Point) (k : ℕ) :
    fairSteps.real (hitBeforePoint x 0 y) * fairSteps.real (beforePointVisits 0 y k) ≤
      fairSteps.real (beforePointVisits x y k) := by
  have h := ENNReal.toReal_mono (by finiteness) (beforePointVisits_race_product x y k)
  simpa only [ENNReal.toReal_mul, measureReal_def] using h

end Erdos1164
