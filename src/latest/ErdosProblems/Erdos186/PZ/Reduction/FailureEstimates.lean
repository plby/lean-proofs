/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.BoundedContext
import ErdosProblems.Erdos186.PZ.Reduction.Estimates

/-!
# Size estimates for a failing coordinate replacement

An identified retained set and its translation both lie in the explicit
difference GAP of the current coefficient box.  This supplies the comparison
progression required by Lemma 6 and makes the upward-rank saving automatic.
-/

namespace Erdos186.PZ.Reduction

noncomputable section

variable {β η : ℝ} {C : HigherDimensionalContext β η}
  {selector : BoundedCFPSelector C} {d : ℕ}
  {A : Finset (LatticePoint d)} {hA : selector.Eligible A} {δ γ : ℝ}

namespace BoundedIrreducibilityFailure

variable (F : BoundedIrreducibilityFailure selector A hA δ γ)

/-- The whole next input lies in the standard difference GAP of the current
coefficient box. -/
theorem nextPoints_subset_differenceGAP :
    F.nextPoints ⊆
      (GAP.differenceCoefficientGAP
        (selector.chosen A hA).progression).carrier := by
  exact GAP.translate_subset_differenceCoefficientGAP
    (selector.chosen A hA).progression
    (F.retained_subset.trans
      (selector.chosen A hA).identifiedCore_subset_coefficientBox)
    F.translationPoint_mem

/-- Hence the next CFP core, together with zero, lies in the same comparison
GAP. -/
theorem nextCore_subset_differenceGAP :
    insert 0 (selector.chosen F.nextPoints F.shifted_eligible).core ⊆
      (GAP.differenceCoefficientGAP
        (selector.chosen A hA).progression).carrier := by
  intro z hz
  rw [Finset.mem_insert] at hz
  rcases hz with rfl | hz
  · exact GAP.zero_mem_differenceCoefficientGAP
      (selector.chosen A hA).progression
  · exact F.nextPoints_subset_differenceGAP
      ((selector.chosen F.nextPoints F.shifted_eligible).witness.core_subset hz)

/-- Exact Lemma-6 saving for a coordinate replacement whose selected rank
rises.  All constants are displayed; the final factor `2^current.dimension`
is the volume cost of the coefficient-box difference GAP. -/
theorem dimensionIncrease
    (hrank : (selector.chosen A hA).dimension ≤
      (selector.chosen F.nextPoints F.shifted_eligible).dimension) :
    (selector.chosen F.nextPoints F.shifted_eligible).dilation ^
          ((selector.chosen F.nextPoints F.shifted_eligible).dimension -
            (selector.chosen A hA).dimension) *
        (selector.chosen F.nextPoints F.shifted_eligible).progression.volume ≤
      2 ^ (selector.chosen F.nextPoints F.shifted_eligible).dimension *
        (2 * (selector.chosen F.nextPoints
          F.shifted_eligible).witness.scaleDen) ^
            (selector.chosen A hA).dimension *
          (2 ^ (selector.chosen A hA).dimension *
            (selector.chosen A hA).progression.volume) := by
  calc
    (selector.chosen F.nextPoints F.shifted_eligible).dilation ^
          ((selector.chosen F.nextPoints F.shifted_eligible).dimension -
            (selector.chosen A hA).dimension) *
          (selector.chosen F.nextPoints F.shifted_eligible).progression.volume
        ≤ 2 ^ (selector.chosen F.nextPoints
              F.shifted_eligible).dimension *
            (2 * (selector.chosen F.nextPoints
              F.shifted_eligible).witness.scaleDen) ^
              (selector.chosen A hA).dimension *
              (GAP.differenceCoefficientGAP
                (selector.chosen A hA).progression).volume :=
      Estimates.cfpWitness_dimensionIncrease
        (selector.chosen F.nextPoints F.shifted_eligible).witness
        (GAP.differenceCoefficientGAP (selector.chosen A hA).progression)
        F.nextCore_subset_differenceGAP hrank
    _ ≤ 2 ^ (selector.chosen F.nextPoints F.shifted_eligible).dimension *
          (2 * (selector.chosen F.nextPoints
            F.shifted_eligible).witness.scaleDen) ^
              (selector.chosen A hA).dimension *
            (2 ^ (selector.chosen A hA).dimension *
              (selector.chosen A hA).progression.volume) :=
      Nat.mul_le_mul_left _
        (GAP.differenceCoefficientGAP_volume_le
          (selector.chosen A hA).progression)

/-- If the selected dimension does not change, failure is exactly the strict
`gamma` shrink alternative. -/
theorem volume_lt_of_dimension_eq
    (hdim : (selector.chosen F.nextPoints F.shifted_eligible).dimension =
      (selector.chosen A hA).dimension) :
    ((selector.chosen F.nextPoints
      F.shifted_eligible).progression.volume : ℝ) <
      γ * ((selector.chosen A hA).progression.volume : ℝ) := by
  rcases F.fails with hne | hshrink
  · exact False.elim (hne hdim)
  · exact hshrink

end BoundedIrreducibilityFailure

end

end Erdos186.PZ.Reduction
