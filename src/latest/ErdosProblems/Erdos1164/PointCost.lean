import ErdosProblems.Erdos1164.ReturnClock
import ErdosProblems.Erdos1165.PointBeforeReturn

/-! # Origin visits accumulated before hitting a fixed point -/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace Erdos1164

open Erdos1165 Erdos1165.PlanarPotential Erdos1165.PointBeforeReturn
open Erdos1165.HLOZGapEstimate Erdos1165.TwoPointLogAvoidance

/-- Before reaching `y`, the walk started at `x` has accumulated `k` visits to zero. -/
def beforePointVisits (x y : Point) (k : ℕ) : Set StepPath :=
  {w | ∃ n, k ≤ originVisits (trajectoryFrom x w) n ∧
    ∀ j < n, trajectoryFrom x w j ≠ y}

theorem measurableSet_beforePointVisits (x y : Point) (k : ℕ) :
    MeasurableSet (beforePointVisits x y k) := by
  have hc : ∀ n, Measurable fun w : StepPath ↦ originVisits (trajectoryFrom x w) n :=
    fun n ↦ (measurable_originVisits n).comp (measurable_trajectoryFrom x)
  have ht : ∀ n, Measurable fun w : StepPath ↦ trajectoryFrom x w n :=
    fun n ↦ (measurable_pi_apply n).comp (measurable_trajectoryFrom x)
  unfold beforePointVisits
  measurability

private theorem pointBeforeReturn_of_hit {y : Point} (hy : y ≠ 0)
    {w : StepPath} {n : ℕ} (hn : trajectory w n = y)
    (hno : ∀ j, 0 < j → j < n → trajectory w j ≠ 0) :
    w ∈ pointBeforePositiveReturn y := by
  have hex : ∃ j, trajectory w j = y := ⟨n, hn⟩
  let j := Nat.find hex
  have hj : trajectory w j = y := Nat.find_spec hex
  have hjn : j ≤ n := Nat.find_min' hex hn
  have hjpos : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    rw [hj0, trajectory_zero] at hj
    exact hy hj.symm
  refine Set.mem_iUnion.mpr ⟨j, hjpos, hj, ?_⟩
  intro l hl hlj
  exact ⟨hno l hl (hlj.trans_le hjn), Nat.find_min hex hlj⟩

/-- No origin lies strictly between two successive capped return times when
the latter is a completed return. -/
theorem no_origin_between_returns {N r j : ℕ} {w : StepPath}
    (hnext : originReturnClock N (r + 1) w < N)
    (hj : originReturnClock N r w < j)
    (hjnext : j < originReturnClock N (r + 1) w) : trajectory w j ≠ 0 := by
  intro hzero
  have hle : originReturnClock N (r + 1) w ≤ j := by
    apply (nextVisitBefore_le_iff (hjnext.trans hnext) w).mpr
    exact ⟨j, le_rfl, hj, hzero⟩
  omega

/-- If none of the first `r` excursions hits `y` before returning, the whole
path through the `r`-th return avoids `y`. -/
theorem originReturnClock_avoids_point {N r : ℕ} {y : Point} (hy : y ≠ 0)
    {w : StepPath} (hr : originReturnClock N r w < N)
    (hmiss : ∀ i < r,
      postStoppingSteps (originReturnClock N i) w ∉ pointBeforePositiveReturn y) :
    ∀ j ≤ originReturnClock N r w, trajectory w j ≠ y := by
  induction r with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by simpa only [originReturnClock, returnLadder_zero] using Nat.eq_zero_of_le_zero hj
    rw [hj0, trajectory_zero]
    exact Ne.symm hy
  | succ r ih =>
    have hprev : originReturnClock N r w < N :=
      (originReturnClock_mono N w (Nat.le_succ r)).trans_lt hr
    have hold := ih hprev (fun i hi ↦ hmiss i (by omega))
    intro j hj hity
    have hjprev : originReturnClock N r w < j := by
      by_contra h
      exact hold j (by omega) hity
    have hpos := originReturnClock_position hprev
    apply hmiss r (by omega)
    apply pointBeforeReturn_of_hit hy (n := j - originReturnClock N r w)
    · change trajectory (shiftSteps (originReturnClock N r w) w) _ = y
      rw [← trajectory_add_sub_trajectory, Nat.add_sub_of_le hjprev.le, hpos, sub_zero]
      exact hity
    · intro l hl hlj
      change trajectory (shiftSteps (originReturnClock N r w) w) l ≠ 0
      rw [← trajectory_add_sub_trajectory, hpos, sub_zero]
      exact no_origin_between_returns hr (by omega) (by omega)

private theorem good_gaps_supply_cost (y : Point) (hy : y ≠ 0) (k t : ℕ) {w : StepPath}
    (hg : ∀ r < k, postStoppingSteps (originReturnClock (k * t + 1) r) w ∉
      avoidsPair 0 t ∪ pointBeforePositiveReturn y) :
    w ∈ beforePointVisits 0 y (k + 1) := by
  have hclock := originReturnClock_le_of_short_gaps
    (by omega : k * t < k * t + 1) (fun r hr hav ↦ hg r hr (Or.inl hav))
  have hc : originReturnClock (k * t + 1) k w < k * t + 1 := by omega
  have hmiss := originReturnClock_avoids_point hy hc
    (fun r hr hav ↦ hg r hr (Or.inr hav))
  refine ⟨originReturnClock (k * t + 1) k w + 1, ?_, ?_⟩
  · have hz : trajectoryFrom 0 w = trajectory w := by
      funext j
      simp only [trajectoryFrom, zero_add]
    rw [hz]
    exact originReturnClock_count_before hc (Nat.lt_succ_self _)
  · intro j hj
    simpa only [trajectoryFrom, zero_add] using hmiss j (by omega)

private theorem shifted_bad_gap_measure (N r t : ℕ) (y : Point) :
    fairSteps (postStoppingSteps (originReturnClock N r) ⁻¹'
      (avoidsPair 0 t ∪ pointBeforePositiveReturn y)) ≤
      ENNReal.ofReal (noReturnProbability t) + ENNReal.ofReal (pointBeforeReturnProbability y) := by
  have hs := originReturnClock_stopping N r
  have hu : IsMeasurableAtStopping (originReturnClock N r) Set.univ := by
    intro n
    simpa only [Set.univ_inter] using hs.measurableSet_eq n
  have h := strongMarkov_fullTail hs hu
    ((measurableSet_avoidsPair 0 t).union (measurableSet_pointBeforePositiveReturn y))
  rw [Set.univ_inter, measure_univ, one_mul] at h
  rw [h]
  have hq : ENNReal.ofReal (noReturnProbability t) = fairSteps (avoidsPair 0 t) := by
    exact ENNReal.ofReal_toReal (by finiteness)
  have hp : ENNReal.ofReal (pointBeforeReturnProbability y) = fairSteps (pointBeforePositiveReturn y) := by
    exact ENNReal.ofReal_toReal (by finiteness)
  rw [hq, hp]
  exact measure_union_le _ _

/-- A purely finite-horizon bound on failure to accumulate the desired cost. -/
theorem beforePointVisits_compl_le (y : Point) (hy : y ≠ 0) (k t : ℕ) :
    fairSteps (beforePointVisits 0 y (k + 1))ᶜ ≤
      (k : ℝ≥0∞) * (ENNReal.ofReal (noReturnProbability t) +
        ENNReal.ofReal (pointBeforeReturnProbability y)) := by
  classical
  have hsub : (beforePointVisits 0 y (k + 1))ᶜ ⊆ ⋃ r ∈ Finset.range k,
      postStoppingSteps (originReturnClock (k * t + 1) r) ⁻¹'
        (avoidsPair 0 t ∪ pointBeforePositiveReturn y) := by
    intro w hw
    by_contra hn
    apply hw
    apply good_gaps_supply_cost y hy k t
    intro r hr hav
    exact hn (Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hr, hav⟩⟩)
  calc
    fairSteps (beforePointVisits 0 y (k + 1))ᶜ ≤ fairSteps (⋃ r ∈ Finset.range k,
        postStoppingSteps (originReturnClock (k * t + 1) r) ⁻¹'
          (avoidsPair 0 t ∪ pointBeforePositiveReturn y)) := measure_mono hsub
    _ ≤ ∑ r ∈ Finset.range k, fairSteps (postStoppingSteps (originReturnClock (k * t + 1) r) ⁻¹'
        (avoidsPair 0 t ∪ pointBeforePositiveReturn y)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _r ∈ Finset.range k, (ENNReal.ofReal (noReturnProbability t) +
        ENNReal.ofReal (pointBeforeReturnProbability y)) :=
      Finset.sum_le_sum (fun r _ ↦ shifted_bad_gap_measure _ r t y)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem noReturnProbability_tendsto_zero : Tendsto noReturnProbability atTop (𝓝 0) := by
  have harg : Tendsto (fun n : ℕ ↦ ((n + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hlog := Real.tendsto_log_atTop.comp harg
  have hdiv : Tendsto (fun n : ℕ ↦ 12 / Real.log ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  exact squeeze_zero (fun n ↦ avoidanceProbability_nonneg 0 n) noReturnProbability_le hdiv

/-- At least `k+1` origin visits occur before hitting `y` with probability at
least `1-k*p_y`. This is sufficient in place of the exact geometric law. -/
theorem beforePointVisits_origin_lower (y : Point) (hy : y ≠ 0) (k : ℕ) :
    1 - (k : ℝ) * pointBeforeReturnProbability y ≤ fairSteps.real (beforePointVisits 0 y (k + 1)) := by
  have hfinite (t : ℕ) : fairSteps.real (beforePointVisits 0 y (k + 1))ᶜ ≤
      (k : ℝ) * (noReturnProbability t + pointBeforeReturnProbability y) := by
    have h := ENNReal.toReal_mono (by finiteness) (beforePointVisits_compl_le y hy k t)
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_add (by finiteness) (by finiteness)] at h
    simpa only [ENNReal.toReal_ofReal (avoidanceProbability_nonneg 0 t),
      ENNReal.toReal_ofReal (pointBeforeReturnProbability_nonneg y), measureReal_def] using h
  have hlim : Tendsto (fun t : ℕ ↦ (k : ℝ) *
      (noReturnProbability t + pointBeforeReturnProbability y)) atTop
        (𝓝 ((k : ℝ) * pointBeforeReturnProbability y)) := by
    simpa only [zero_add] using
      (noReturnProbability_tendsto_zero.add_const (pointBeforeReturnProbability y)).const_mul (k : ℝ)
  have hle := ge_of_tendsto hlim (Eventually.of_forall hfinite)
  have hcompl := measureReal_compl (μ := fairSteps) (measurableSet_beforePointVisits 0 y (k + 1))
  rw [hcompl] at hle
  have huniv : fairSteps.real (Set.univ : Set StepPath) = 1 := by
    simp [measureReal_def]
  rw [huniv] at hle
  linarith

end Erdos1164
