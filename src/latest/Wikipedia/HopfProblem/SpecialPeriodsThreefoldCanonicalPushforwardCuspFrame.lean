import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardCuspGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsBasic

/-!
# The full cusp frame on inverse images of arbitrary base opens

The existing nowhere-zero section of the original canonical bundle is
restricted along the genuine inclusion into the full cusp patch. Its
formula on the regular overlap is the actual reciprocal coordinate
times the original regular canonical section.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Cusp

attribute [local instance] Threefold.chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The original point over `U` underlying a point over the chosen cusp neighborhood. -/
def sourcePoint (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (localBase U)) : Threefold.basePreimage U :=
  ⟨x.val, Threefold.basePreimage_mono (localBase_le U) x.property⟩

theorem sourcePoint_holomorphic (U : Opens RiemannSphere) :
    ContMDiff IF IF ω (sourcePoint U) :=
  contMDiff_inclusion (Threefold.basePreimage_mono (localBase_le U))

/-- Actual restriction of an arbitrary native canonical section. -/
def restrictedSection (U : Opens RiemannSphere)
    (s : NativeBundleSections.Section bundle IF (Threefold.basePreimage U)) :
    NativeBundleSections.Section bundle IF (Threefold.basePreimage (localBase U)) :=
  NativeBundleSections.Section.restrict bundle IF
    (Threefold.basePreimage_mono (localBase_le U)) s

@[simp] theorem restrictedSection_apply (U : Opens RiemannSphere)
    (s : NativeBundleSections.Section bundle IF (Threefold.basePreimage U))
    (x : Threefold.basePreimage (localBase U)) :
    restrictedSection U s x = s (sourcePoint U x) := rfl

/-- The actual holomorphic unit frame from the full cusp canonical regularization. -/
def frame (U : Opens RiemannSphere) :
    NativeBundleSections.Section bundle IF (Threefold.basePreimage (localBase U)) where
  toFun x := GlobalCuspExtension.canonicalSection (cuspPoint U x)
  contMDiff_toFun := GlobalCuspExtension.canonicalSectionMap_holomorphic.comp
    (cuspPoint_holomorphic U)

@[simp] theorem frame_apply (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (localBase U)) :
    frame U x = GlobalCuspExtension.canonicalSection (cuspPoint U x) := rfl

theorem frame_ne_zero (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (localBase U)) : frame U x ≠ 0 :=
  GlobalCuspExtension.canonicalSection_ne_zero (cuspPoint U x)

/-- The comparison is in the actual original canonical fibre over every regular point. -/
theorem frame_regular (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (localBase U)) (hx : x.val ∈ Threefold.regularLocus) :
    frame U x = reciprocalSection U (Threefold.baseProjection (localBase U) x) •
      GlobalRegular.globalSection ⟨x.val, hx⟩ :=
  GlobalCuspExtension.canonicalSection_overlap (cuspPoint U x) hx

theorem regular_of_projection_ne_infty (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (localBase U))
    (hx : Threefold.projectionSphere x.val ≠ (∞ : RiemannSphere)) :
    x.val ∈ Threefold.regularLocus :=
  (Threefold.mem_regularLocus_iff_sphere x.val).mpr
    ((basePatch_regular_iff x.property.2).mpr hx)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Cusp
