import ErdosProblems.Erdos1002.GaussMovingSignedMarkedFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The zero mode of the moving signed marked coefficient

This module connects the marked Fourier interface to the moving-scale
factorial theorem.  The statement is deliberately separate from nonzero
mode cancellation: at frequency zero it is an exact finite identity
followed by the proved unmarked limit.
-/

open Filter MeasureTheory
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- The zero torus Fourier mode has the exact signed factorial limit at an
arbitrary real scale. -/
theorem tendsto_gaussMovingSignedMarkedFourierTupleSum_zero
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (N : ℕ → ℕ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (signedLower signedUpper : Fin r → ℝ)
    (parity : Fin r → Fin 2)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 <
      gaussPrescribedParityOrientedLower
        parity signedLower signedUpper i)
    (hupper : ∀ i,
      gaussPrescribedParityOrientedLower
          parity signedLower signedUpper i <
        gaussPrescribedParityOrientedUpper
          parity signedLower signedUpper i)
    (hupperA : ∀ i,
      gaussPrescribedParityOrientedUpper
        parity signedLower signedUpper i ≤ A)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ n : ℕ in atTop, 0 < gap n)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (hchronological : ∀ n, ∀ t ∈ tuples n,
      IsChronologicalNatTuple t)
    (hparity : ∀ n, ∀ t ∈ tuples n, ∀ i,
      t i % 2 = (parity i).1)
    (htotalDensity : Tendsto
      (fun n : ℕ ↦ ((tuples n).card : ℝ) / (scale n) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun n : ℕ ↦
        ((shortNatTupleFamily (gap n) (tuples n)).card : ℝ) /
          (scale n) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦
        gaussMovingSignedMarkedFourierTupleSum
          (N n) (scale n) signedLower signedUpper
          (fun _i ↦ 0) (tuples n))
      atTop
      (𝓝 ((density *
        ∏ i,
          (gaussPrescribedParityOrientedUpper
              parity signedLower signedUpper i -
            gaussPrescribedParityOrientedLower
              parity signedLower signedUpper i) / Real.log 2 : ℝ) : ℂ)) := by
  have hreal :=
    tendsto_gaussMovingSignedApproximationTupleSum
      hr scale hscale signedLower signedUpper parity hA
        hlower hupper hupperA gap hgapTop hgapPos tuples
        hchronological hparity htotalDensity hshortDensity
  have hcomplex := hreal.ofReal
  apply hcomplex.congr'
  filter_upwards with n
  exact
    (gaussMovingSignedMarkedFourierTupleSum_zero
      (N n) (scale n) signedLower signedUpper (tuples n)).symm

/-- Convergence of the unmarked signed mass also supplies the uniform
boundedness used in finite Fourier approximation. -/
theorem exists_uniform_gaussMovingSignedApproximationTupleSum_bound
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (signedLower signedUpper : Fin r → ℝ)
    (parity : Fin r → Fin 2)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 <
      gaussPrescribedParityOrientedLower
        parity signedLower signedUpper i)
    (hupper : ∀ i,
      gaussPrescribedParityOrientedLower
          parity signedLower signedUpper i <
        gaussPrescribedParityOrientedUpper
          parity signedLower signedUpper i)
    (hupperA : ∀ i,
      gaussPrescribedParityOrientedUpper
        parity signedLower signedUpper i ≤ A)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ n : ℕ in atTop, 0 < gap n)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (hchronological : ∀ n, ∀ t ∈ tuples n,
      IsChronologicalNatTuple t)
    (hparity : ∀ n, ∀ t ∈ tuples n, ∀ i,
      t i % 2 = (parity i).1)
    (htotalDensity : Tendsto
      (fun n : ℕ ↦ ((tuples n).card : ℝ) / (scale n) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun n : ℕ ↦
        ((shortNatTupleFamily (gap n) (tuples n)).card : ℝ) /
          (scale n) ^ r)
      atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ n : ℕ,
      |gaussMovingSignedApproximationTupleSum
        (scale n) signedLower signedUpper (tuples n)| ≤ C := by
  have hlimit :=
    tendsto_gaussMovingSignedApproximationTupleSum
      hr scale hscale signedLower signedUpper parity hA
        hlower hupper hupperA gap hgapTop hgapPos tuples
        hchronological hparity htotalDensity hshortDensity
  have hbounded := Metric.isBounded_range_of_tendsto
    (fun n : ℕ ↦
      gaussMovingSignedApproximationTupleSum
        (scale n) signedLower signedUpper (tuples n))
    hlimit
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbounded
  refine ⟨C, fun n ↦ ?_⟩
  simpa only [Real.norm_eq_abs] using! hC _ ⟨n, rfl⟩

/-- Absolute continuity is summed before any limiting argument: the
uniform-Lebesgue signed mass is at most `2 log 2` times its Gauss mass. -/
theorem movingSignedApproximationTupleMassSum_uniform_le_gauss
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) :
    movingSignedApproximationTupleMassSum
        uniform01Measure scale lower upper tuples ≤
      (2 * Real.log 2) *
        gaussMovingSignedApproximationTupleSum
          scale lower upper tuples := by
  classical
  unfold movingSignedApproximationTupleMassSum
    gaussMovingSignedApproximationTupleSum
  calc
    (∑ times ∈ tuples,
        uniform01Measure.real
          (gaussSignedApproximationTupleEvent
            scale lower upper times)) ≤
        ∑ times ∈ tuples,
          (2 * Real.log 2) *
            gaussMeasure.real
              (gaussSignedApproximationTupleEvent
                scale lower upper times) := by
      apply Finset.sum_le_sum
      intro times _htimes
      exact uniform01MeasureReal_le_gaussMeasureReal
        (measurableSet_gaussSignedApproximationTupleEvent
          scale lower upper times)
    _ = (2 * Real.log 2) *
        ∑ times ∈ tuples,
          gaussMeasure.real
            (gaussSignedApproximationTupleEvent
              scale lower upper times) := by
      rw [Finset.mul_sum]

/-- The original uniform-Lebesgue zero modes are uniformly bounded as
well.  This is the domination required when a torus indicator is
approximated uniformly by trigonometric polynomials. -/
theorem exists_uniform_uniformMovingSignedApproximationTupleMassSum_bound
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (signedLower signedUpper : Fin r → ℝ)
    (parity : Fin r → Fin 2)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 <
      gaussPrescribedParityOrientedLower
        parity signedLower signedUpper i)
    (hupper : ∀ i,
      gaussPrescribedParityOrientedLower
          parity signedLower signedUpper i <
        gaussPrescribedParityOrientedUpper
          parity signedLower signedUpper i)
    (hupperA : ∀ i,
      gaussPrescribedParityOrientedUpper
        parity signedLower signedUpper i ≤ A)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ n : ℕ in atTop, 0 < gap n)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (hchronological : ∀ n, ∀ t ∈ tuples n,
      IsChronologicalNatTuple t)
    (hparity : ∀ n, ∀ t ∈ tuples n, ∀ i,
      t i % 2 = (parity i).1)
    (htotalDensity : Tendsto
      (fun n : ℕ ↦ ((tuples n).card : ℝ) / (scale n) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun n : ℕ ↦
        ((shortNatTupleFamily (gap n) (tuples n)).card : ℝ) /
          (scale n) ^ r)
      atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ n : ℕ,
      movingSignedApproximationTupleMassSum
        uniform01Measure (scale n) signedLower signedUpper
          (tuples n) ≤ C := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_gaussMovingSignedApproximationTupleSum_bound
      hr scale hscale signedLower signedUpper parity hA
        hlower hupper hupperA gap hgapTop hgapPos tuples
        hchronological hparity htotalDensity hshortDensity
  refine ⟨(2 * Real.log 2) * C, fun n ↦ ?_⟩
  calc
    movingSignedApproximationTupleMassSum
        uniform01Measure (scale n) signedLower signedUpper (tuples n) ≤
        (2 * Real.log 2) *
          gaussMovingSignedApproximationTupleSum
            (scale n) signedLower signedUpper (tuples n) :=
      movingSignedApproximationTupleMassSum_uniform_le_gauss
        (scale n) signedLower signedUpper (tuples n)
    _ ≤ (2 * Real.log 2) * C := by
      apply mul_le_mul_of_nonneg_left
      · exact (le_abs_self _).trans (hC n)
      · positivity

end

end Erdos1002
