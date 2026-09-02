import ErdosProblems.Erdos1164.CoverIteration
import ErdosProblems.Erdos1164.RecordCost

/-! # Averaging the deterministic-order cover estimate -/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1164

open Erdos1165 Erdos1165.PlanarPotential

/-- Extend a permutation of the selected targets to a natural-indexed list.
Only the first `m` entries are used. -/
def orderedTargets (m : ℕ) (p : Equiv.Perm (Fin m)) (k : ℕ) : Point :=
  if h : k < m then separatedTarget m (p ⟨k, h⟩) else 0

theorem orderedTargets_eq {m k : ℕ} (p : Equiv.Perm (Fin m)) (hk : k < m) :
    orderedTargets m p k = separatedTarget m (p ⟨k, hk⟩) := by
  simp only [orderedTargets, dif_pos hk]

/-- The expected amplified cover weight is at most one for every fixed ordering. -/
theorem ordered_coverWeight_bound {m N : ℕ} (hm : LargeTargetScale m) (hN : 0 < N)
    (p : Equiv.Perm (Fin m)) :
    ∀ k ≤ m, (∫⁻ w, coverWeight (orderedTargets m p) N (targetVisitCost m) k w ∂fairSteps) ≤ 1 := by
  intro k hk
  induction k with
  | zero => simp only [coverWeight_zero _ hN, lintegral_one, measure_univ, le_refl]
  | succ k ih =>
    have hkm : k < m := by omega
    have hprev : ∀ i < k, ∃ a : Fin m, a ≠ p ⟨k, hkm⟩ ∧
        orderedTargets m p i = separatedTarget m a := by
      intro i hi
      have him : i < m := by omega
      refine ⟨p ⟨i, him⟩, ?_, orderedTargets_eq p him⟩
      intro heq
      have hv := congrArg Fin.val (p.injective heq)
      dsimp only at hv
      omega
    exact (coverWeight_step hm (orderedTargets m p) N k (p ⟨k, hkm⟩)
      (orderedTargets_eq p hkm) hprev).trans (ih (by omega))

/-- All selected sites have been visited strictly before the deadline. -/
def selectedCovered (m N : ℕ) : Set StepPath :=
  {w | ∀ i : Fin m, pointHitClock 0 (separatedTarget m i) N w < N}

theorem measurableSet_selectedCovered (m N : ℕ) : MeasurableSet (selectedCovered m N) := by
  simp only [selectedCovered, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_lt (measurable_pointHitClock 0 (separatedTarget m i) N) measurable_const

theorem ordered_clock_alive_iff {m N : ℕ} (hN : 0 < N) (p : Equiv.Perm (Fin m)) (w : StepPath) :
    prefixCoverClock (orderedTargets m p) N m w < N ↔ w ∈ selectedCovered m N := by
  rw [prefixCoverClock_lt_iff hN]
  constructor
  · intro h i
    have hi := h (p.symm i) (p.symm i).isLt
    rw [orderedTargets_eq p (p.symm i).isLt, Equiv.apply_symm_apply] at hi
    exact hi
  · intro h i hi
    rw [orderedTargets_eq p hi]
    exact h (p ⟨i, hi⟩)

/-- The rank function used in the finite record identity is the actual capped
hitting time, not an auxiliary independent variable. -/
noncomputable def selectedHitRank (m N : ℕ) (i : Fin m) (w : StepPath) : ℝ :=
  pointHitClock 0 (separatedTarget m i) N w

theorem measurable_selectedHitRank (m N : ℕ) (i : Fin m) :
    Measurable (selectedHitRank m N i) :=
  (measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
    (measurable_pointHitClock 0 (separatedTarget m i) N)

theorem selectedHitRank_injective {m N : ℕ} (hm : 1 ≤ m) {w : StepPath}
    (hw : w ∈ selectedCovered m N) : Function.Injective (fun i ↦ selectedHitRank m N i w) := by
  intro i j hij
  have ht : pointHitClock 0 (separatedTarget m i) N w = pointHitClock 0 (separatedTarget m j) N w :=
    Nat.cast_injective hij
  have hi := pointHitClock_hit (hw i)
  have hj := pointHitClock_hit (hw j)
  rw [ht] at hi
  exact separatedTarget_injective hm (hi.symm.trans hj)

theorem ordered_record_count {m N : ℕ} (hN : 0 < N) (p : Equiv.Perm (Fin m)) (w : StepPath) :
    coverRecordCount (orderedTargets m p) N m w =
      leftRecordCount (fun i ↦ selectedHitRank m N (p i) w) := by
  rw [coverRecordCount_eq_leftRecordCount _ hN]
  congr 1
  funext i
  rw [orderedTargets_eq p i.isLt]
  rfl

/-- Use the deterministic deadline's local time for the terminal cost, which
only decreases the discounted weight relative to stopping at the cover time. -/
noncomputable def normalizedOriginCost (m N : ℕ) (w : StepPath) : ℝ :=
  (originVisits (trajectory w) N : ℝ) / (targetVisitCost m : ℝ)

theorem measurable_normalizedOriginCost (m N : ℕ) : Measurable (normalizedOriginCost m N) :=
  ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
    ((measurable_originVisits N).comp measurable_trajectory)).div_const _

private theorem ordered_record_weight_le {m N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin m)) (w : StepPath) :
    recordCostWeight (selectedCovered m N) (normalizedOriginCost m N)
        (selectedHitRank m N) recordAmplification p w ≤
      coverWeight (orderedTargets m p) N (targetVisitCost m) m w := by
  by_cases hw : w ∈ selectedCovered m N
  · have ha := (ordered_clock_alive_iff hN p w).mpr hw
    rw [coverWeight_of_alive ha]
    rw [recordCostWeight, discountedCost, Set.indicator_of_mem hw]
    rw [← ordered_record_count hN p w, ENNReal.ofReal_pow recordAmplification_pos.le]
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    unfold normalizedOriginCost
    have hcount := originVisits_mono (trajectory w)
      (prefixCoverClock_le_deadline (orderedTargets m p) N m w)
    have hcast : (originVisits (trajectory w) (prefixCoverClock (orderedTargets m p) N m w) : ℝ) ≤
        (originVisits (trajectory w) N : ℝ) := by exact_mod_cast hcount
    have hell : 0 < (targetVisitCost m : ℝ) := by exact_mod_cast targetVisitCost_pos m
    rw [← neg_div]
    apply (div_le_div_iff_of_pos_right hell).mpr
    linarith
  · rw [recordCostWeight, discountedCost, Set.indicator_of_notMem hw, zero_mul]
    exact zero_le

/-- The discounted covering-cost tail, with every probabilistic input discharged. -/
theorem selected_cover_cost_tail {m N : ℕ} (hm : LargeTargetScale m) (hN : 0 < N) (u : ℝ) :
    fairSteps (selectedCovered m N ∩ {w | normalizedOriginCost m N w ≤ u}) ≤
      ENNReal.ofReal (Real.exp (u - (1 - targetCostDiscount) * (harmonic m : ℝ))) := by
  have horders (p : Equiv.Perm (Fin m)) :
      (∫⁻ w, recordCostWeight (selectedCovered m N) (normalizedOriginCost m N)
        (selectedHitRank m N) recordAmplification p w ∂fairSteps) ≤ 1 :=
    (lintegral_mono (ordered_record_weight_le hN p)).trans
      (ordered_coverWeight_bound hm hN p m le_rfl)
  have h := record_cost_lower_tail fairSteps (measurableSet_selectedCovered m N)
    (measurable_normalizedOriginCost m N) (selectedHitRank m N) (measurable_selectedHitRank m N)
    recordAmplification recordAmplification_ge_one
    (fun _ hw ↦ selectedHitRank_injective (by have := hm.1; omega) hw) horders u
  have hrec : 1 / recordAmplification = targetCostDiscount := by
    simp only [recordAmplification, one_div, inv_inv]
  simpa only [hrec] using h

end Erdos1164
