import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrameNativeBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrameSmooth

/-!
# A global smooth nonzero frame in the original native bundle on `ℂ²`

The real-smooth coefficient claim refers literally to the original native
trivializations. Together with actual total-space continuity and pointwise
nonvanishing this provides the smooth frame needed for holomorphic correction.
No global frame, triviality premise, or new native atlas is supplied.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrame

open PeriodTorusLineBundleClassificationNative

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable (V : ComplexPlane₂ → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V Iℂ]

/-- The constructed section has real `C∞` coefficients in every original
native bundle chart, on that chart's whole base set. -/
theorem nativeFrameCoefficient_contDiffOn (i : ComplexPlane₂) :
    ContDiffOn ℝ ∞ (nativeFrameCoefficient V i) ((nativeTriv V i).baseSet) :=
  (frameCoefficient_contDiffOn (data V) i).congr
    (fun _ hx => nativeFrameCoefficient_eq V i hx)

theorem nativeFrameCoefficient_contDiffAt (i x : ComplexPlane₂)
    (hx : x ∈ (nativeTriv V i).baseSet) :
    ContDiffAt ℝ ∞ (nativeFrameCoefficient V i) x :=
  (nativeFrameCoefficient_contDiffOn V i).contDiffAt
    ((nativeTriv V i).open_baseSet.mem_nhds hx)

/-- Continuity is proved for the actual original native total-space topology. -/
theorem nativeFrame_continuous :
    Continuous (fun x => (⟨x, nativeFrame V x⟩ : TotalSpace ℂ V)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [FiberBundle.continuousAt_section ℂ]
  exact (nativeFrameCoefficient_contDiffAt V x x
    (FiberBundle.mem_baseSet_trivializationAt ℂ V x)).continuousAt

/-- Every arbitrary native holomorphic complex line bundle on `ℂ²` has an
actual global nonzero section whose original native local coefficients are
real-smooth. The section and its regularity are conclusions, not input data. -/
theorem exists_native_smooth_frame :
    ∃ s : ∀ x, V x, (∀ x, s x ≠ 0) ∧
      Continuous (fun x => (⟨x, s x⟩ : TotalSpace ℂ V)) ∧
      ∀ i, ContDiffOn ℝ ∞
        (fun x => (nativeTriv V i (TotalSpace.mk x (s x))).2)
        ((nativeTriv V i).baseSet) :=
  ⟨nativeFrame V, nativeFrame_ne_zero V, nativeFrame_continuous V,
    nativeFrameCoefficient_contDiffOn V⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrame
