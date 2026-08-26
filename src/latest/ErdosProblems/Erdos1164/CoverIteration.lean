import ErdosProblems.Erdos1164.CoverWeights
import ErdosProblems.Erdos1164.CoverObservables
import ErdosProblems.Erdos1164.StoppedWeights

/-! # The discounted partial-cover iteration -/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1164

open Erdos1165 Erdos1165.PlanarPotential Erdos1165.HLOZGapPointReturn

noncomputable def coverPastWeight (ell : ℕ) (s : ℕ × ℕ × ℕ × Point) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(s.2.1 : ℝ) / (ell : ℝ))) *
    ENNReal.ofReal recordAmplification ^ s.2.2.1

noncomputable def coverFutureWeight (N ell : ℕ) (y : Point)
    (s : ℕ × ℕ × ℕ × Point) : StepPath → ℝ≥0∞ :=
  fun w ↦ ENNReal.ofReal recordAmplification *
    discountedHitAt s.2.2.2 ell (pointHitClock s.2.2.2 y (N - s.1))
      {z | pointHitClock s.2.2.2 y (N - s.1) z < N - s.1} w

theorem measurable_coverFutureWeight (N ell : ℕ) (y : Point) (s : ℕ × ℕ × ℕ × Point) :
    Measurable (coverFutureWeight N ell y s) := by
  apply measurable_const.mul
  exact measurable_discountedHitAt _ _ (measurable_pointHitClock _ _ _)
    (measurableSet_lt (measurable_pointHitClock _ _ _) measurable_const)

private theorem coverFutureWeight_bound {m : ℕ} (hm : LargeTargetScale m) (j : Fin m)
    (N : ℕ) (s : ℕ × ℕ × ℕ × Point)
    (hx : s.2.2.2 = 0 ∨ ∃ i : Fin m, i ≠ j ∧ s.2.2.2 = separatedTarget m i) :
    (∫⁻ w, coverFutureWeight N (targetVisitCost m) (separatedTarget m j) s w ∂fairSteps) ≤ 1 := by
  unfold coverFutureWeight
  rw [lintegral_const_mul'' _
    (measurable_discountedHitAt _ _ (measurable_pointHitClock _ _ _)
      (measurableSet_lt (measurable_pointHitClock _ _ _) measurable_const)).aemeasurable]
  calc
    _ ≤ ENNReal.ofReal recordAmplification * ENNReal.ofReal targetCostDiscount := by
      apply mul_le_mul' le_rfl
      apply selected_discounted_hit_bound hm j hx
      intro w hw
      exact pointHitClock_hit hw
    _ = 1 := recordAmplification_discount

private theorem coverPastWeight_eq {v : ℕ → Point} {N ell k : ℕ} {w : StepPath}
    (h : w ∈ coverExtension v N k) :
    coverPastWeight ell (coverState v N k w) = coverWeight v N ell k w := by
  have ha : prefixCoverClock v N k w < N := h.trans_le (pointHitClock_le 0 (v k) N w)
  rw [coverWeight_of_alive ha]
  rfl

private theorem coverWeight_extension_state {v : ℕ → Point} {N ell k : ℕ} {w : StepPath}
    (hy : v k ≠ 0) (h : w ∈ coverExtension v N k) :
    coverWeight v N ell (k + 1) w =
      coverPastWeight ell (coverState v N k w) *
        coverFutureWeight N ell (v k) (coverState v N k w)
          (postStoppingSteps (prefixCoverClock v N k) w) := by
  rw [coverPastWeight_eq h, coverWeight_extension hy h]
  dsimp only [coverFutureWeight, coverState, postStoppingSteps]
  rw [mul_assoc]

/-- One deterministic target-list step. The earlier listed targets must be
selected sites distinct from the current one; no randomness of the ordering
is used in this estimate. -/
theorem coverWeight_step {m : ℕ} (hm : LargeTargetScale m)
    (v : ℕ → Point) (N k : ℕ) (j : Fin m) (hj : v k = separatedTarget m j)
    (hprev : ∀ i < k, ∃ a : Fin m, a ≠ j ∧ v i = separatedTarget m a) :
    (∫⁻ w, coverWeight v N (targetVisitCost m) (k + 1) w ∂fairSteps) ≤
      ∫⁻ w, coverWeight v N (targetVisitCost m) k w ∂fairSteps := by
  let A := coverExtension v N k
  let τ := prefixCoverClock v N k
  let loc := coverState v N k
  let ell := targetVisitCost m
  have hτ := prefixCoverClock_stopping v N k
  have hA := coverExtension_observable v N k
  have hAm := measurableSet_coverExtension v N k
  have hobs (s : ℕ × ℕ × ℕ × Point) :
      IsMeasurableAtStopping τ (A ∩ {w | loc w = s}) :=
    isMeasurableAtStopping_inter hA (coverState_observable v N k s)
  have hy : v k ≠ 0 := by rw [hj]; exact separatedTarget_ne_zero (by have := hm.1; omega) j
  have hfuture (s : ℕ × ℕ × ℕ × Point) (hs : (A ∩ {w | loc w = s}).Nonempty) :
      (∫⁻ w, coverFutureWeight N ell (v k) s w ∂fairSteps) ≤ 1 := by
    obtain ⟨w, hw, heq⟩ := hs
    have ha : prefixCoverClock v N k w < N := hw.trans_le (pointHitClock_le 0 (v k) N w)
    have hxw : (loc w).2.2.2 = 0 ∨
        ∃ i : Fin m, i ≠ j ∧ (loc w).2.2.2 = separatedTarget m i := by
      rcases prefixCoverClock_position ha with hz | ⟨i, hi, hpi⟩
      · exact Or.inl hz
      · obtain ⟨a, haj, hia⟩ := hprev i hi
        exact Or.inr ⟨a, haj, hpi.trans hia⟩
    have hx : s.2.2.2 = 0 ∨ ∃ i : Fin m, i ≠ j ∧ s.2.2.2 = separatedTarget m i := by
      rw [← heq]
      exact hxw
    rw [hj]
    exact coverFutureWeight_bound hm j N s hx
  have hmarkov := strongMarkov_weighted_le hτ loc hobs (coverPastWeight ell)
    (coverFutureWeight N ell (v k)) (measurable_coverFutureWeight N ell (v k)) 1 hfuture
  rw [mul_one] at hmarkov
  have hleft : (∫⁻ w in A, coverWeight v N ell (k + 1) w ∂fairSteps) =
      ∫⁻ w in A, coverPastWeight ell (loc w) *
        coverFutureWeight N ell (v k) (loc w) (postStoppingSteps τ w) ∂fairSteps := by
    apply setLIntegral_congr_fun hAm
    intro w hw
    exact coverWeight_extension_state hy hw
  have hright : (∫⁻ w in A, coverPastWeight ell (loc w) ∂fairSteps) =
      ∫⁻ w in A, coverWeight v N ell k w ∂fairSteps := by
    apply setLIntegral_congr_fun hAm
    intro w hw
    exact coverPastWeight_eq hw
  rw [← hleft, hright] at hmarkov
  have hcompl : (∫⁻ w in Aᶜ, coverWeight v N ell (k + 1) w ∂fairSteps) =
      ∫⁻ w in Aᶜ, coverWeight v N ell k w ∂fairSteps := by
    apply setLIntegral_congr_fun hAm.compl
    intro w hw
    exact coverWeight_no_extension hw
  calc
    (∫⁻ w, coverWeight v N ell (k + 1) w ∂fairSteps) =
        (∫⁻ w in A, coverWeight v N ell (k + 1) w ∂fairSteps) +
          (∫⁻ w in Aᶜ, coverWeight v N ell (k + 1) w ∂fairSteps) :=
      (lintegral_add_compl _ hAm).symm
    _ ≤ (∫⁻ w in A, coverWeight v N ell k w ∂fairSteps) +
        (∫⁻ w in Aᶜ, coverWeight v N ell k w ∂fairSteps) :=
      add_le_add hmarkov hcompl.le
    _ = _ := lintegral_add_compl _ hAm

end Erdos1164
