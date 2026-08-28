import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrameBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransportSmooth

/-!
# Actual smoothness of the constructed radial frame coefficients

Although preferred chart indices need not vary continuously, the independence
of the actual integral transport identifies the global scalar with a fixed
finite chain near each endpoint. The chain's fixed-coordinate formula is
smooth, so the genuine frame coefficients are smooth in every original chart.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrame

open HolomorphicCharacterBundle PeriodTorusLineBundleClassificationGlobalTransport
  PeriodTorusLineBundleClassificationTransport

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι) [A.IsHolomorphic Iℂ]

/-- The actual coefficient of the globally chosen radial section is smooth
near each point of its original chart. -/
theorem frameCoefficient_contDiffAt (i : ι) (x : ComplexPlane₂)
    (hx : x ∈ A.baseSet i) : ContDiffAt ℝ ∞ (frameCoefficient A i) x := by
  have h0 : radialCurve x 0 ∈ A.baseSet (A.indexAt 0) := by
    simpa only [radialCurve, zero_smul] using A.mem_baseSet_at 0
  have h1 : radialCurve x 1 ∈ A.baseSet i := by
    simpa only [radialCurve, one_smul] using hx
  obtain ⟨F, hF, U, hUo, hxU, hUF⟩ :=
    ChartChain.exists_contDiffAt_radial_scalar A (radialChain A x) (A.indexAt 0) i h0 h1
  apply hF.congr_of_eventuallyEq
  filter_upwards [hUo.mem_nhds hxU] with y hy
  obtain ⟨D, hD⟩ := hUF y hy
  simp only [radialCurve, one_smul, zero_smul] at hD
  rw [A.transition_self _ _ (A.mem_baseSet_at 0)] at hD
  simp only [Units.val_one, mul_one] at hD
  rw [frameCoefficient, globalRadialScalar_eq_chain A y D]
  exact hD.symm

theorem frameCoefficient_contDiffOn (i : ι) :
    ContDiffOn ℝ ∞ (frameCoefficient A i) (A.baseSet i) :=
  fun x hx => (frameCoefficient_contDiffAt A i x hx).contDiffWithinAt

/-- The constructed section is continuous into the actual scalar-core total
space, in addition to having real-smooth local coefficients. -/
theorem coreFrame_continuous :
    Continuous (fun x => (⟨x, coreFrame A x⟩ : A.core.TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [FiberBundle.continuousAt_section ℂ]
  exact (frameCoefficient_contDiffAt A (A.indexAt x) x (A.mem_baseSet_at x)).continuousAt

/-- Every actual holomorphic scalar cocycle on `ℂ²` has a genuinely
constructed nonzero section with smooth coefficients in its given charts. -/
theorem exists_smooth_core_frame :
    ∃ s : ∀ x, A.core.Fiber x, (∀ x, s x ≠ 0) ∧
      Continuous (fun x => (⟨x, s x⟩ : A.core.TotalSpace)) ∧
      ∀ i, ContDiffOn ℝ ∞ (A.localCoefficient s i) (A.baseSet i) :=
  ⟨coreFrame A, coreFrame_ne_zero A, coreFrame_continuous A,
    frameCoefficient_contDiffOn A⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrame
