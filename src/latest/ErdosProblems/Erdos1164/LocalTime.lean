import ErdosProblems.Erdos1164.Definitions
import ErdosProblems.Erdos1165.HLOZFixedPointLocalTimeTail

/-! # The origin clock and its unconditional exponential upper tail -/

open MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos1164

/-- Visits to zero strictly before time `n`. -/
def originVisits (s : WalkPath) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun j ↦ s j = 0).card

@[simp] theorem originVisits_zero (s : WalkPath) : originVisits s 0 = 0 := by
  simp [originVisits]

theorem originVisits_mono (s : WalkPath) : Monotone (originVisits s) := by
  intro m n hmn
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hmn))

theorem originVisits_succ_eq_localTime (s : WalkPath) (n : ℕ) :
    originVisits s (n + 1) = Erdos1165.localTime s n 0 := by
  exact (Erdos1165.localTime_eq_card_filter_range s n 0).symm

theorem originVisits_le_localTime (s : WalkPath) (n : ℕ) :
    originVisits s n ≤ Erdos1165.localTime s n 0 := by
  rw [← originVisits_succ_eq_localTime]
  exact originVisits_mono s (Nat.le_succ n)

theorem measurable_originVisits (n : ℕ) :
    Measurable fun s : WalkPath ↦ originVisits s n := by
  cases n with
  | zero =>
      simpa only [originVisits_zero] using
        (measurable_const : Measurable fun _ : WalkPath ↦ (0 : ℕ))
  | succ n =>
    simp only [originVisits_succ_eq_localTime]
    exact Erdos1165.HLOZGapCandidateMeasurability.measurable_localTime_fixed n 0

theorem half_le_log_succ {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  exact htwo.trans (Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n + 1)))

/-- Exponential tail at deterministic time, obtained from the checked planar
return estimate. No assumptions on recurrence, hitting probabilities, or
martingales are arguments to this theorem. -/
theorem originVisits_tail {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) :
    walkLaw {s | k ≤ originVisits s n} ≤
      ENNReal.ofReal (Real.exp (-((k - 1 : ℕ) : ℝ) /
        (100 * Real.log ((n + 1 : ℕ) : ℝ)))) := by
  have hlog := half_le_log_succ hn
  have hden : 1 ≤ 100 * Real.log ((n + 1 : ℕ) : ℝ) := by linarith
  have hzero : 0 ≤ 1 / (100 * Real.log ((n + 1 : ℕ) : ℝ)) := by positivity
  have hone : 1 / (100 * Real.log ((n + 1 : ℕ) : ℝ)) ≤ 1 := by
    exact (div_le_one (by linarith)).mpr hden
  have hsub : {s : WalkPath | k ≤ originVisits s n} ⊆
      Erdos1165.HLOZFixedPointLocalTimeTail.originLocalTimeEvent n k := by
    intro s hs
    exact hs.trans (originVisits_le_localTime s n)
  calc
    walkLaw {s | k ≤ originVisits s n} ≤
        walkLaw (Erdos1165.HLOZFixedPointLocalTimeTail.originLocalTimeEvent n k) :=
      measure_mono hsub
    _ ≤ Erdos1165.Gap.geometricReturnCost
        (1 / (100 * Real.log ((n + 1 : ℕ) : ℝ))) (k - 1) :=
      Erdos1165.HLOZFixedPointLocalTimeTail.simpleRandomWalk_originLocalTimeEvent_le hn hk
    _ ≤ Erdos1165.Gap.exponentialReturnCost
        (1 / (100 * Real.log ((n + 1 : ℕ) : ℝ))) (k - 1) :=
      Erdos1165.Gap.geometricReturnCost_le_exponentialReturnCost hzero hone (k - 1)
    _ = _ := by
      unfold Erdos1165.Gap.exponentialReturnCost
      congr 2
      ring

end Erdos1164
