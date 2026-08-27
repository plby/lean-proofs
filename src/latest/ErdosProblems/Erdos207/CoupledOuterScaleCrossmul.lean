/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoupledOuterInitialBridge

/-!
# Cross-multiplied scale certificate for the coupled corridor

All relative-window hypotheses are stated without division.  This is the
form in which the dyadic power hierarchy proves them.
-/

namespace Erdos207

noncomputable section

/-- Cross-multiplied inequalities package the relative parameter
`z = window / centre` required by `CoupledOuterScaleFacts`. -/
theorem coupledOuterScaleFacts_of_crossmul
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside K : ℕ)
    (A : ℝ) (k i : ℕ) (buffer : ℝ)
    (hy : 0 < outerCoupledCenter H X outside i)
    (hw : 0 ≤ outerCoupledWindow H X A k i)
    (hsmall : 100 * outerCoupledWindow H X A k i ≤
      outerCoupledCenter H X outside i)
    (hroundBuffer : buffer + 1 ≤ outerCoupledWindow H X A k i)
    (hroundTwo : 2 ≤ outerCoupledWindow H X A k i)
    (hlowerOne : 1 ≤ outerCoupledLowerBarrier H X outside A k i - buffer)
    (hclock : 100 * outerCoupledCenter H X outside i ≤
      outerCoupledWindow H X A k i * outerSharpEligiblePairs H X i)
    (haggregate : (K : ℝ) ≤ outerCoupledWindow H X A k i *
      outerCoupledCenter H X outside i) :
    CoupledOuterScaleFacts H X outside K A k i buffer
      (outerCoupledWindow H X A k i /
        outerCoupledCenter H X outside i) := by
  let y := outerCoupledCenter H X outside i
  let w := outerCoupledWindow H X A k i
  have hy0 : y ≠ 0 := hy.ne'
  have hznonneg : 0 ≤ w / y := div_nonneg hw hy.le
  refine ⟨hznonneg, ?_, ?_, hroundBuffer, hroundTwo, hlowerOne, ?_, ?_⟩
  · apply (div_le_iff₀ hy).2
    nlinarith
  · change w = w / y * y
    field_simp
  · change 100 ≤ (w / y) * (outerSharpEligiblePairs H X i : ℝ)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hy).2
    simpa only [w, y] using hclock
  · change (K : ℝ) ≤ (w / y) * y ^ 2
    rw [show (w / y) * y ^ 2 = w * y by field_simp]
    simpa only [w, y] using haggregate

/-- A coarse lower/upper sandwich is sufficient for all cross-multiplied
scale inequalities.  This isolates the later power arithmetic from the
analytic corridor API. -/
theorem coupledOuterScaleFacts_of_sandwich
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside K : ℕ)
    (A : ℝ) (k i : ℕ) (buffer wLower wUpper yLower yUpper : ℝ)
    (hA : 0 ≤ A)
    (hy : 0 < yLower)
    (hwLower : wLower ≤ outerCoupledWindow H X A k i)
    (hwUpper : outerCoupledWindow H X A k i ≤ wUpper)
    (hyLower : yLower ≤ outerCoupledCenter H X outside i)
    (hyUpper : outerCoupledCenter H X outside i ≤ yUpper)
    (hsmall : 100 * wUpper ≤ yLower)
    (hroundBuffer : buffer + 1 ≤ wLower)
    (hroundTwo : 2 ≤ wLower)
    (hlowerOne : 1 + buffer + wUpper ≤ yLower)
    (hclock : 100 * yUpper ≤
      wLower * outerSharpEligiblePairs H X i)
    (haggregate : (K : ℝ) ≤ wLower * yLower) :
    CoupledOuterScaleFacts H X outside K A k i buffer
      (outerCoupledWindow H X A k i /
        outerCoupledCenter H X outside i) := by
  have hyCenter : 0 < outerCoupledCenter H X outside i :=
    hy.trans_le hyLower
  have hw : 0 ≤ outerCoupledWindow H X A k i := by
    unfold outerCoupledWindow coupledOuterWindow
    exact div_nonneg hA (by positivity)
  apply coupledOuterScaleFacts_of_crossmul H X outside K A k i buffer
    hyCenter hw
  · exact (mul_le_mul_of_nonneg_left hwUpper (by norm_num)).trans
      (hsmall.trans hyLower)
  · exact hroundBuffer.trans hwLower
  · exact hroundTwo.trans hwLower
  · unfold outerCoupledLowerBarrier
    linarith
  · calc
      100 * outerCoupledCenter H X outside i ≤ 100 * yUpper := by gcongr
      _ ≤ wLower * outerSharpEligiblePairs H X i := hclock
      _ ≤ outerCoupledWindow H X A k i *
          outerSharpEligiblePairs H X i := by gcongr
  · calc
      (K : ℝ) ≤ wLower * yLower := haggregate
      _ ≤ outerCoupledWindow H X A k i *
          outerCoupledCenter H X outside i := by
        exact mul_le_mul hwLower hyLower hy.le (by linarith)

end

end Erdos207
