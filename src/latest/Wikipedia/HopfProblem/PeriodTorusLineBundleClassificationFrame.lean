import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrameNative
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopologicalCover

/-!
# A constructed smooth global frame of every native universal-cover pullback

An arbitrary native holomorphic complex line bundle on the actual period
torus is pulled back along the actual quotient map. The constructed radial
frame is a section of that original native pullback, nowhere zero and smooth
in its original trivializations. Holomorphic correction is a further step.
-/

noncomputable section

open Set Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrame

open PeriodTorusLineBundleClassificationNative
  PeriodTorusLineBundleClassificationTopological

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable (p : PeriodDomain) (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V Iℂ]

/-- A genuinely constructed section of Mathlib's original native pullback. -/
def pullbackFrame (x : ComplexPlane₂) : universalCoverPullback p V x :=
  nativeFrame (universalCoverPullback p V) x

omit [ContMDiffVectorBundle ω ℂ V Iℂ] in
theorem pullbackFrame_ne_zero (x : ComplexPlane₂) : pullbackFrame p V x ≠ 0 :=
  nativeFrame_ne_zero (universalCoverPullback p V) x

/-- The frame coefficient in the actual native pullback trivialization. -/
def pullbackFrameCoefficient (i x : ComplexPlane₂) : ℂ :=
  nativeFrameCoefficient (universalCoverPullback p V) i x

theorem pullbackFrameCoefficient_contDiffOn (i : ComplexPlane₂) :
    ContDiffOn ℝ ∞ (pullbackFrameCoefficient p V i)
      ((nativeTriv (universalCoverPullback p V) i).baseSet) :=
  nativeFrameCoefficient_contDiffOn (universalCoverPullback p V) i

omit [ContMDiffVectorBundle ω ℂ V Iℂ] in
theorem pullbackFrameCoefficient_ne_zero (i : ComplexPlane₂) {x : ComplexPlane₂}
    (hx : x ∈ (nativeTriv (universalCoverPullback p V) i).baseSet) :
    pullbackFrameCoefficient p V i x ≠ 0 :=
  nativeFrameCoefficient_ne_zero (universalCoverPullback p V) i hx

theorem pullbackFrame_continuous :
    Continuous (fun x => (⟨x, pullbackFrame p V x⟩ :
      TotalSpace ℂ (universalCoverPullback p V))) :=
  nativeFrame_continuous (universalCoverPullback p V)

/-- The same actual coefficients are smooth on the existing convex refinement. -/
theorem pullbackFrameCoefficient_contDiffOn_ball (i : ComplexPlane₂) :
    ContDiffOn ℝ ∞ (pullbackFrameCoefficient p V i) ((pullbackBallData p V).baseSet i) :=
  (pullbackFrameCoefficient_contDiffOn p V i).mono
    (ball_subset_nativeTriv (universalCoverPullback p V) i)

omit [ContMDiffVectorBundle ω ℂ V Iℂ] in
/-- The transformation law is the already extracted actual native transition,
restricted to the actual pullback balls. -/
theorem pullbackFrameCoefficient_change (i j : ComplexPlane₂) {x : ComplexPlane₂}
    (hi : x ∈ (pullbackBallData p V).baseSet i)
    (hj : x ∈ (pullbackBallData p V).baseSet j) :
    ((pullbackBallData p V).transition i j x : ℂ) * pullbackFrameCoefficient p V i x =
      pullbackFrameCoefficient p V j x :=
  nativeFrameCoefficient_change (universalCoverPullback p V) i j
    (ball_subset_nativeTriv (universalCoverPullback p V) i hi)
    (ball_subset_nativeTriv (universalCoverPullback p V) j hj)

/-- No global-triviality hypothesis: every actual native torus line bundle
has a global nonzero real-smooth frame on its actual universal-cover pullback. -/
theorem exists_pullback_smooth_frame :
    ∃ s : ∀ x, universalCoverPullback p V x, (∀ x, s x ≠ 0) ∧
      Continuous (fun x => (⟨x, s x⟩ : TotalSpace ℂ (universalCoverPullback p V))) ∧
      ∀ i, ContDiffOn ℝ ∞
        (fun x => (nativeTriv (universalCoverPullback p V) i (TotalSpace.mk x (s x))).2)
        ((nativeTriv (universalCoverPullback p V) i).baseSet) :=
  exists_native_smooth_frame (universalCoverPullback p V)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrame
