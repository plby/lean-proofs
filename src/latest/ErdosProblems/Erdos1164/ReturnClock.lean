import ErdosProblems.Erdos1164.ReturnTail
import ErdosProblems.Erdos1165.HLOZGapReturn
import ErdosProblems.Erdos1165.StrongMarkovFullTail

/-! # A union bound for long return gaps -/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1164

open Erdos1165 Erdos1165.HLOZGapEstimate Erdos1165.HLOZGapReturn
open Erdos1165.TwoPointLogAvoidance

/-- Successive returns to zero, capped at a deterministic deadline. -/
noncomputable abbrev originReturnClock (N r : ℕ) : StepPath → ℕ :=
  returnLadder (fun _ ↦ 0) (fun _ ↦ 0) N r

theorem originReturnClock_stopping (N r : ℕ) :
    IsFiniteStoppingTime (originReturnClock N r) := by
  apply returnLadder_isFiniteStoppingTime (isFiniteStoppingTime_const 0)
    (fun _ ↦ Nat.zero_le _)
  intro x n
  by_cases hx : (0 : Point) = x
  · simpa only [hx, Set.ofPred_true, Set.univ_inter] using
      (isFiniteStoppingTime_const 0).measurableSet_eq n
  · simp only [hx, Set.ofPred_false, Set.empty_inter, MeasurableSet.empty]

theorem originReturnClock_mono (N : ℕ) (w : StepPath) :
    Monotone fun r ↦ originReturnClock N r w := by
  apply monotone_nat_of_le_succ
  intro r
  exact returnLadder_mono_step (fun _ ↦ Nat.zero_le _) w

theorem originReturnClock_position {N r : ℕ} {w : StepPath}
    (h : originReturnClock N r w < N) :
    trajectory w (originReturnClock N r w) = 0 := by
  apply returnLadder_eq_target_of_stage (fun v ↦ trajectory_zero v) r
  cases r with
  | zero => trivial
  | succ r => exact h

theorem originReturnClock_strict_step {N r : ℕ} {w : StepPath}
    (h : originReturnClock N (r + 1) w < N) :
    originReturnClock N r w < originReturnClock N (r + 1) w := by
  change nextVisitBefore (originReturnClock N r) (fun _ ↦ 0) N w < N at h
  have hex := (nextVisitBefore_lt_deadline_iff w).mp h
  change originReturnClock N r w < nextVisitBefore (originReturnClock N r) (fun _ ↦ 0) N w
  unfold nextVisitBefore
  rw [dif_pos hex]
  exact (Nat.find_spec hex).2.1

/-- A completed `r`-th return supplies `r+1` distinct visits, including time zero. -/
theorem originReturnClock_count_before {N r T : ℕ} {w : StepPath}
    (h : originReturnClock N r w < N) (hT : originReturnClock N r w < T) :
    r + 1 ≤ originVisits (trajectory w) T := by
  classical
  have hsmall (j : ℕ) (hj : j ≤ r) : originReturnClock N j w < N :=
    (originReturnClock_mono N w hj).trans_lt h
  have hstrict {i j : ℕ} (hij : i < j) (hj : j ≤ r) :
      originReturnClock N i w < originReturnClock N j w := by
    exact (originReturnClock_strict_step (hsmall (i + 1) (by omega))).trans_le
      (originReturnClock_mono N w (by omega))
  have hcard := Finset.card_le_card_of_injOn (fun j ↦ originReturnClock N j w)
    (s := Finset.range (r + 1))
    (t := (Finset.range T).filter fun j ↦ trajectory w j = 0)
    (by
      intro j hj
      have hjr : j ≤ r := by simpa only [Finset.mem_coe, Finset.mem_range,
        Nat.lt_succ_iff] using hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        ((originReturnClock_mono N w hjr).trans_lt hT),
        originReturnClock_position (hsmall j hjr)⟩)
    (by
      intro i hi j hj heq
      have hir : i ≤ r := by simpa only [Finset.mem_coe, Finset.mem_range,
        Nat.lt_succ_iff] using hi
      have hjr : j ≤ r := by simpa only [Finset.mem_coe, Finset.mem_range,
        Nat.lt_succ_iff] using hj
      rcases lt_trichotomy i j with hij | hij | hij
      · exact False.elim ((ne_of_lt (hstrict hij hjr)) heq)
      · exact hij
      · exact False.elim ((ne_of_lt (hstrict hij hir)) heq.symm))
  simpa only [Finset.card_range, originVisits] using hcard

theorem originReturnClock_count {N r : ℕ} {w : StepPath}
    (h : originReturnClock N r w < N) :
    r + 1 ≤ originVisits (trajectory w) N :=
  originReturnClock_count_before h h

/-- If every exposed gap is at most `t`, the `k`-th return is at most `k*t`. -/
theorem originReturnClock_le_of_short_gaps {N k t : ℕ} (hkt : k * t < N)
    {w : StepPath}
    (hgap : ∀ r < k, postStoppingSteps (originReturnClock N r) w ∉ avoidsPair 0 t) :
    originReturnClock N k w ≤ k * t := by
  have hbound : ∀ r ≤ k, originReturnClock N r w ≤ r * t := by
    intro r hr
    induction r with
    | zero => simp [originReturnClock, returnLadder_zero]
    | succ r ih =>
      have hrk : r < k := by omega
      have hprev := ih (by omega)
      have hrt : r * t < N := (Nat.mul_le_mul_right t (by omega : r ≤ k)).trans_lt hkt
      have hpos := originReturnClock_position (hprev.trans_lt hrt)
      have hex : ∃ j, 0 < j ∧ j ≤ t ∧
          trajectory (postStoppingSteps (originReturnClock N r) w) j = 0 := by
        by_contra! hn
        apply hgap r hrk
        intro j hj hjt
        exact ⟨hn j hj hjt, hn j hj hjt⟩
      obtain ⟨j, hj, hjt, hjzero⟩ := hex
      have htime : originReturnClock N r w + j ≤ (r + 1) * t := by
        nlinarith
      have hdeadline : (r + 1) * t < N :=
        (Nat.mul_le_mul_right t hr).trans_lt hkt
      change nextVisitBefore (originReturnClock N r) (fun _ ↦ 0) N w ≤ (r + 1) * t
      apply (nextVisitBefore_le_iff hdeadline w).mpr
      refine ⟨originReturnClock N r w + j, htime, by omega, ?_⟩
      change trajectory (shiftSteps (originReturnClock N r w) w) j = 0 at hjzero
      rw [← trajectory_add_sub_trajectory, hpos, sub_zero] at hjzero
      exact hjzero
  exact hbound k le_rfl

private theorem shifted_avoidance_measure (N r t : ℕ) :
    fairSteps (postStoppingSteps (originReturnClock N r) ⁻¹' avoidsPair 0 t) =
      ENNReal.ofReal (noReturnProbability t) := by
  have hs := originReturnClock_stopping N r
  have hu : IsMeasurableAtStopping (originReturnClock N r) Set.univ := by
    intro n
    simpa only [Set.univ_inter] using hs.measurableSet_eq n
  have h := strongMarkov_fullTail hs hu (measurableSet_avoidsPair 0 t)
  rw [Set.univ_inter, measure_univ, one_mul] at h
  rw [h, noReturnProbability, avoidanceProbability, measureReal_def,
    ENNReal.ofReal_toReal (by finiteness)]

/-- A small origin clock forces a long gap. This finite-horizon estimate uses
only strong Markov and a union bound; no moment or renewal limit theorem. -/
theorem originVisits_lower_tail_gap {N k t : ℕ} (hkt : k * t < N) :
    walkLaw {s | originVisits s N < k + 1} ≤
      (k : ℝ≥0∞) * ENNReal.ofReal (noReturnProbability t) := by
  classical
  have hevent : MeasurableSet {s : WalkPath | originVisits s N < k + 1} :=
    measurableSet_lt (measurable_originVisits N) measurable_const
  have hsub : trajectory ⁻¹' {s : WalkPath | originVisits s N < k + 1} ⊆
      ⋃ r ∈ Finset.range k,
        postStoppingSteps (originReturnClock N r) ⁻¹' avoidsPair 0 t := by
    intro w hw
    by_contra hn
    have hgap : ∀ r < k,
        postStoppingSteps (originReturnClock N r) w ∉ avoidsPair 0 t := by
      intro r hr hav
      exact hn (Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr hr, hav⟩⟩)
    have hclock := (originReturnClock_le_of_short_gaps hkt hgap).trans_lt hkt
    exact (Nat.not_lt_of_ge (originReturnClock_count hclock)) hw
  change simpleRandomWalk _ ≤ _
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory hevent]
  calc
    fairSteps (trajectory ⁻¹' {s : WalkPath | originVisits s N < k + 1}) ≤
        fairSteps (⋃ r ∈ Finset.range k,
          postStoppingSteps (originReturnClock N r) ⁻¹' avoidsPair 0 t) := measure_mono hsub
    _ ≤ ∑ r ∈ Finset.range k,
        fairSteps (postStoppingSteps (originReturnClock N r) ⁻¹' avoidsPair 0 t) :=
      measure_biUnion_finset_le _ _
    _ = _ := by simp only [shifted_avoidance_measure, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]

/-- The explicit logarithmic form of the long-gap estimate. -/
theorem originVisits_lower_tail_log {N k t : ℕ} (hkt : k * t < N) :
    walkLaw {s | originVisits s N < k + 1} ≤
      ENNReal.ofReal (12 * k / Real.log ((t + 2 : ℕ) : ℝ)) := by
  calc
    walkLaw {s | originVisits s N < k + 1} ≤
        (k : ℝ≥0∞) * ENNReal.ofReal (noReturnProbability t) := originVisits_lower_tail_gap hkt
    _ ≤ (k : ℝ≥0∞) * ENNReal.ofReal (12 / Real.log ((t + 2 : ℕ) : ℝ)) := by
      gcongr
      exact noReturnProbability_le t
    _ = _ := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- For at most square-root many visits, the deterministic-time clock lower
bound has the expected inverse-logarithmic scale. -/
theorem originVisits_lower_tail {N k : ℕ} (hN : 2 ≤ N)
    (hk : (k + 1) ^ 2 ≤ N) :
    walkLaw {s | originVisits s N < k + 1} ≤
      ENNReal.ofReal (24 * k / Real.log (N : ℝ)) := by
  let t := N / (k + 1)
  have hdiv : t * (k + 1) ≤ N := Nat.div_mul_le_self N (k + 1)
  have hlow : k + 1 ≤ t := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < k + 1)).mpr
    simpa only [pow_two] using hk
  have hkt : k * t < N := by nlinarith
  have hupper : N < (t + 1) * (k + 1) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < k + 1)).mp (Nat.lt_succ_self t)
  have hsquare : N ≤ (t + 2) ^ 2 := by nlinarith
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogt : 0 < Real.log ((t + 2 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < t + 2))
  have hlogs : Real.log (N : ℝ) ≤ 2 * Real.log ((t + 2 : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < N)
      (show (N : ℝ) ≤ (((t + 2 : ℕ) : ℝ) ^ 2) by exact_mod_cast hsquare)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  apply (originVisits_lower_tail_log hkt).trans
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff₀ hlogt hlogN).mpr
  have hmul := mul_le_mul_of_nonneg_left hlogs (by positivity : (0 : ℝ) ≤ 12 * k)
  nlinarith

end Erdos1164
