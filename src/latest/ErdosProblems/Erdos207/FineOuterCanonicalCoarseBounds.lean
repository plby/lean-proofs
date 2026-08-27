/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOuterStaticArithmetic

/-!
# Coarse integral bounds for the canonical corridor

The analytic corridor naturally produces a real floor at scale
`outside/(8t²)`.  The later scalar hierarchy is cleaner with the explicit
integer quotient `outside/(16t²)`.  This file performs that one-time
weakening, including the corresponding availability floor.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

def fineOuterCoarseAvailabilityFloor (outside t : ℕ) : ℕ :=
  fineOuterReserve outside t * fineOuterCoarseDegreeFloor outside t / 3

theorem fineOuterCanonical_coarse_uniform_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t K : ℕ)
    (houtside : 0 < outside) (ht : 0 < t)
    (hreservePos : 0 < fineOuterReserve outside t)
    (hreserveInitial : fineOuterReserve outside t ≤
      outerSharpEligiblePairs H X 0)
    (hpairUpper : 2 * (outerSharpEligiblePairs H X 0 : ℕ) ≤
      (outside : ℝ) ^ 2)
    (hsmallPower : 12800 ≤ t ^ 31)
    (hoffsetPower : t ^ fineOuterCorridorExponent ≤ 16 * outside)
    (hclockPower : 50 * t ^ 101 ≤ outside ^ 2)
    (haggregatePower : t ^ 102 * K ≤ 8 * outside ^ 2)
    (hinitialOrder : lower₀ ≤ outside)
    (hinitial :
      (outside : ℝ) ≤
          quadraticPairBarrier (outside : ℝ≥0)
            (fineOffsetUpperCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 +
              fineOuterInitialOffset outside t ∧
        quadraticPairBarrier (outside : ℝ≥0)
            (fineOffsetLowerCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 -
              fineOuterInitialOffset outside t ≤ (lower₀ : ℝ))
    (hfour : 4 ≤ fineOuterReserve outside t)
    (hdegreePos : 0 < fineOuterCoarseDegreeFloor outside t) :
    let fuel := outerSharpStopFuel H X (fineOuterReserve outside t)
    ∀ i, i ≤ fuel →
      fineOuterCoarseDegreeFloor outside t ≤
          outerSharpLowerSchedule H X
            (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i ∧
      outerSharpUpperSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i ≤
          5 * outside ∧
      fineOuterCoarseAvailabilityFloor outside t ≤
          outerSharpLowerAvailability H X
            (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i ∧
      0 ≤ (outerSharpEnvelope H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i).2 -
            fineOuterBuffer outside t := by
  dsimp only
  have hdegreeFine : 0 < fineOuterDegreeFloor outside t :=
    hdegreePos.trans_le (fineOuterCoarseDegreeFloor_le ht)
  have hb := fineOuterCanonical_uniform_bounds H X lower₀ outside t K
    houtside ht hreservePos hreserveInitial hpairUpper hsmallPower
    hoffsetPower hclockPower haggregatePower hinitialOrder hinitial hfour
    hdegreeFine
  intro i hi
  have hbi := hb i hi
  refine ⟨(fineOuterCoarseDegreeFloor_le ht).trans hbi.1, ?_, ?_, hbi.2.2.2⟩
  · simpa only [fineOuterDegreeCeil_eq] using hbi.2.1
  · exact (show fineOuterCoarseAvailabilityFloor outside t ≤
        fineOuterAvailabilityFloor outside t by
      unfold fineOuterCoarseAvailabilityFloor fineOuterAvailabilityFloor
      exact Nat.div_le_div_right (Nat.mul_le_mul_left _
        (fineOuterCoarseDegreeFloor_le ht))).trans hbi.2.2.1

end

end Erdos207
