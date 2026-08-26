import ErdosProblems.Erdos1165.GreenProbability
import ErdosProblems.Erdos1165.StrongMarkovFullTail

/-! # A two-point race bound from killed-domain hitting probabilities

This avoids an additional infinite-domain optional-stopping argument. A path
which hits `a` before exiting either hits `a` before `b`, or first hits `b` and
then succeeds in a fresh killed-domain walk from `b`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1164

open Erdos1165 Erdos1165.PlanarPotential Erdos1165.GreenProbability

/-- The translated walk reaches `a` without an earlier visit to `b`. -/
def hitBeforePoint (x a b : Point) : Set StepPath :=
  {w | ∃ n, trajectoryFrom x w n = a ∧ ∀ j < n, trajectoryFrom x w j ≠ b}

theorem measurableSet_hitBeforePoint (x a b : Point) :
    MeasurableSet (hitBeforePoint x a b) := by
  unfold hitBeforePoint
  have hm : ∀ n, Measurable fun w : StepPath ↦ trajectoryFrom x w n :=
    fun n ↦ (measurable_pi_apply n).comp (measurable_trajectoryFrom x)
  measurability

private theorem trajectoryFrom_restart (x : Point) (w : StepPath) (k j : ℕ) :
    trajectoryFrom (trajectoryFrom x w k) (shiftSteps k w) j =
      trajectoryFrom x w (k + j) := by
  simp only [trajectoryFrom]
  rw [← trajectory_add_sub_trajectory]
  abel

private theorem hitBeforeExit_split (D : Finset Point) (x a b : Point) :
    hitBeforeExitEvent D x a ⊆ hitBeforePoint x a b ∪
      ⋃ k : ℕ, firstHitPathEvent D k x b ∩
        shiftSteps k ⁻¹' hitBeforeExitEvent D b a := by
  intro w hw
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
  have hstay : ∀ j ≤ n, trajectoryFrom x w j ∈ D := hn.1.1
  have hend : trajectoryFrom x w n = a := hn.1.2
  by_cases havoid : ∀ j < n, trajectoryFrom x w j ≠ b
  · exact Or.inl ⟨n, hend, havoid⟩
  · push Not at havoid
    obtain ⟨j, hjn, hjb⟩ := havoid
    have hex : ∃ k, trajectoryFrom x w k = b := ⟨j, hjb⟩
    let k := Nat.find hex
    have hk : trajectoryFrom x w k = b := Nat.find_spec hex
    have hkj : k ≤ j := Nat.find_min' hex hjb
    have hkn : k < n := hkj.trans_lt hjn
    have hfirst : w ∈ firstHitPathEvent D k x b := by
      refine ⟨⟨fun l hl ↦ hstay l (hl.trans hkn.le), hk⟩, ?_⟩
      intro l hl
      exact Nat.find_min hex hl
    refine Or.inr (Set.mem_iUnion.mpr ⟨k, hfirst, ?_⟩)
    apply Set.mem_iUnion.mpr
    refine ⟨n - k, ?_⟩
    have hshift (l : ℕ) : trajectoryFrom b (shiftSteps k w) l = trajectoryFrom x w (k + l) := by
      rw [← hk]
      exact trajectoryFrom_restart x w k l
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro l hl
      change trajectoryFrom b (shiftSteps k w) l ∈ D
      rw [hshift]
      exact hstay _ (by omega)
    · change trajectoryFrom b (shiftSteps k w) (n - k) = a
      rw [hshift, Nat.add_sub_of_le hkn.le]
      exact hend
    · intro l hl
      change trajectoryFrom b (shiftSteps k w) l ≠ a
      rw [hshift]
      exact hn.2 _ (by omega)

private theorem firstHit_future_factor (D : Finset Point) (x a b : Point) (k : ℕ) :
    fairSteps (firstHitPathEvent D k x b ∩ shiftSteps k ⁻¹' hitBeforeExitEvent D b a) =
      fairSteps (firstHitPathEvent D k x b) * fairSteps (hitBeforeExitEvent D b a) := by
  have hobs : IsMeasurableAtStopping (fun _ : StepPath ↦ k) (firstHitPathEvent D k x b) := by
    intro n
    by_cases hn : k = n
    · subst n
      simpa only [Set.ofPred_true, Set.inter_univ] using
        measurableSet_firstHitPathEvent_filtration D k x b
    · simp only [hn, Set.ofPred_false, Set.inter_empty, MeasurableSet.empty]
  exact strongMarkov_fullTail (isFiniteStoppingTime_const k) hobs
    (measurableSet_hitBeforeExitEvent D b a)

/-- A killed-domain lower bound for the probability of winning a two-point race.
All terms are actual random-walk probabilities. -/
theorem hitBeforeExit_le_race_add_product (D : Finset Point) (x a b : Point) :
    fairSteps (hitBeforeExitEvent D x a) ≤
      fairSteps (hitBeforePoint x a b) +
        fairSteps (hitBeforeExitEvent D x b) * fairSteps (hitBeforeExitEvent D b a) := by
  calc
    fairSteps (hitBeforeExitEvent D x a) ≤ fairSteps (hitBeforePoint x a b ∪
        ⋃ k : ℕ, firstHitPathEvent D k x b ∩ shiftSteps k ⁻¹' hitBeforeExitEvent D b a) :=
      measure_mono (hitBeforeExit_split D x a b)
    _ ≤ fairSteps (hitBeforePoint x a b) +
        fairSteps (⋃ k : ℕ, firstHitPathEvent D k x b ∩
          shiftSteps k ⁻¹' hitBeforeExitEvent D b a) := measure_union_le _ _
    _ ≤ fairSteps (hitBeforePoint x a b) +
        ∑' k : ℕ, fairSteps (firstHitPathEvent D k x b ∩
          shiftSteps k ⁻¹' hitBeforeExitEvent D b a) :=
      add_le_add le_rfl (measure_iUnion_le _)
    _ = _ := by
      simp_rw [firstHit_future_factor D x a b]
      rw [ENNReal.tsum_mul_right, ← measure_iUnion
        (firstHitPathEvent_pairwise_disjoint D x b)
        (measurableSet_firstHitPathEvent D · x b)]
      rfl

/-- Real-valued form, useful when the three killed hitting probabilities have
been estimated by Green functions. -/
theorem raceProbability_lower (D : Finset Point) (x a b : Point) :
    fairSteps.real (hitBeforeExitEvent D x a) -
      fairSteps.real (hitBeforeExitEvent D x b) * fairSteps.real (hitBeforeExitEvent D b a) ≤
      fairSteps.real (hitBeforePoint x a b) := by
  have h := ENNReal.toReal_mono (by finiteness) (hitBeforeExit_le_race_add_product D x a b)
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul] at h
  simp only [measureReal_def]
  linarith

end Erdos1164
