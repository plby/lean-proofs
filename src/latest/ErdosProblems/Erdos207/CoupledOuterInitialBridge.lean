/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoupledOuterCorridor
import ErdosProblems.Erdos207.FineOffsetOuterQuadraticBarrier

/-!
# Initializing the coupled outer corridor

The fine time-zero estimate was originally phrased using coefficients
`4 - epsilon` and `4 + epsilon` and a fixed offset.  This file converts that
estimate to the common-centre corridor used by the valid recursive barrier.
The inverse-power window is normalized to equal the old offset at time zero.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

lemma coupledOuterWindow_normalized
    {A E : ℝ} {k : ℕ} (hE : E ≠ 0) :
    coupledOuterWindow (A * E ^ k) k E = A := by
  unfold coupledOuterWindow
  rw [mul_div_cancel_right₀ A (pow_ne_zero _ hE)]

/-- The old fine offset bounds imply the time-zero coupled bounds.  No
quantitative information is lost: the new window is exactly the old offset
at the initial eligible-pair clock. -/
theorem fineOffset_initial_bounds_to_coupled
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside lower₀ t k : ℕ)
    (hE : 0 < outerSharpEligiblePairs H X 0)
    (he : fineOuterCorridorError t ≤ 4)
    (hinitial :
      (outside : ℝ) ≤
          quadraticPairBarrier (outside : ℝ≥0)
            (fineOffsetUpperCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 +
              fineOuterInitialOffset outside t ∧
        quadraticPairBarrier (outside : ℝ≥0)
            (fineOffsetLowerCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 -
              fineOuterInitialOffset outside t ≤ (lower₀ : ℝ)) :
    let A := fineOuterInitialOffset outside t *
      (outerSharpEligiblePairs H X 0 : ℝ) ^ k
    (outside : ℝ) ≤ outerCoupledUpperBarrier H X outside A k 0 ∧
      outerCoupledLowerBarrier H X outside A k 0 ≤ (lower₀ : ℝ) := by
  dsimp only
  let E : ℝ := outerSharpEligiblePairs H X 0
  let N : ℝ := outside
  let epsilon : ℝ := fineOuterCorridorError t
  let base : ℝ := E ^ 2 * N⁻¹ ^ 3
  have hE0 : E ≠ 0 := by
    dsimp only [E]
    exact_mod_cast hE.ne'
  have hbase : 0 ≤ base := by
    dsimp only [base]
    positivity
  have hwindow : outerCoupledWindow H X
      (fineOuterInitialOffset outside t * E ^ k) k 0 =
        fineOuterInitialOffset outside t := by
    change coupledOuterWindow
      (fineOuterInitialOffset outside t * E ^ k) k E = _
    exact coupledOuterWindow_normalized hE0
  have hcenter : outerCoupledCenter H X outside 0 = 4 * base := by
    change 4 * E ^ 2 * N⁻¹ ^ 3 = 4 * (E ^ 2 * N⁻¹ ^ 3)
    ring
  have hcastBase :
      (((outerSharpEligiblePairs H X 0 : ℝ≥0) ^ 2 *
        (outside : ℝ≥0)⁻¹ ^ 3 : ℝ≥0) : ℝ) = base := by
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv,
      NNReal.coe_natCast, E, N, base]
  have hupperQuadratic :
      quadraticPairBarrier (outside : ℝ≥0)
          (fineOffsetUpperCoefficient t)
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 =
        (4 - epsilon) * base := by
    rw [show quadraticPairBarrier (outside : ℝ≥0)
          (fineOffsetUpperCoefficient t)
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 =
        ((fineOffsetUpperCoefficient t *
          (outerSharpEligiblePairs H X 0 : ℝ≥0) ^ 2 *
            (outside : ℝ≥0)⁻¹ ^ 3 : ℝ≥0) : ℝ) by
      simp [quadraticPairBarrier, affineSurvivalEnvelope]]
    calc
      (((fineOffsetUpperCoefficient t *
          (outerSharpEligiblePairs H X 0 : ℝ≥0) ^ 2 *
            (outside : ℝ≥0)⁻¹ ^ 3 : ℝ≥0) : ℝ)) =
          (4 - epsilon) *
            (((outerSharpEligiblePairs H X 0 : ℝ≥0) ^ 2 *
              (outside : ℝ≥0)⁻¹ ^ 3 : ℝ≥0) : ℝ) := by
        simpa only [epsilon] using fineOffsetUpper_liveQuadratic_eq he
          (outerSharpEligiblePairs H X 0 : ℝ≥0) (outside : ℝ≥0)
      _ = (4 - epsilon) * base := by rw [hcastBase]
  have hlowerQuadratic :
      quadraticPairBarrier (outside : ℝ≥0)
          (fineOffsetLowerCoefficient t)
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 =
        (4 + epsilon) * base := by
    rw [show quadraticPairBarrier (outside : ℝ≥0)
          (fineOffsetLowerCoefficient t)
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 =
        ((fineOffsetLowerCoefficient t *
          (outerSharpEligiblePairs H X 0 : ℝ≥0) ^ 2 *
            (outside : ℝ≥0)⁻¹ ^ 3 : ℝ≥0) : ℝ) by
      simp [quadraticPairBarrier, affineSurvivalEnvelope]]
    calc
      (((fineOffsetLowerCoefficient t *
          (outerSharpEligiblePairs H X 0 : ℝ≥0) ^ 2 *
            (outside : ℝ≥0)⁻¹ ^ 3 : ℝ≥0) : ℝ)) =
          (4 + epsilon) *
            (((outerSharpEligiblePairs H X 0 : ℝ≥0) ^ 2 *
              (outside : ℝ≥0)⁻¹ ^ 3 : ℝ≥0) : ℝ) := by
        simpa only [epsilon] using fineOffsetLower_liveQuadratic_eq t
          (outerSharpEligiblePairs H X 0 : ℝ≥0) (outside : ℝ≥0)
      _ = (4 + epsilon) * base := by rw [hcastBase]
  have hepsilon : 0 ≤ epsilon := by positivity
  constructor
  · rw [outerCoupledUpperBarrier, hcenter, hwindow]
    calc
      (outside : ℝ) ≤ (4 - epsilon) * base +
          fineOuterInitialOffset outside t := by
        simpa only [hupperQuadratic] using hinitial.1
      _ ≤ 4 * base + fineOuterInitialOffset outside t := by
        gcongr
        linarith
  · rw [outerCoupledLowerBarrier, hcenter, hwindow]
    calc
      4 * base - fineOuterInitialOffset outside t ≤
          (4 + epsilon) * base - fineOuterInitialOffset outside t := by
        gcongr
        linarith
      _ ≤ (lower₀ : ℝ) := by
        simpa only [hlowerQuadratic] using hinitial.2

end

end Erdos207
