import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalFiniteRegularSection
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalNativeCanonical

/-!
# The actual two frames on the prescribed generic open

The meromorphic section of the independently constructed divisor line
and the genuine nonvanishing canonical form are represented in their
original bundles.  The target section is transported through the proved
native canonical-bundle biholomorphism.  Its extension by zero outside
the specified open is only a raw fibre family; holomorphicity is asserted
and proved exactly on the original generic open.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonGeneric

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The independently constructed divisor-line transition data. -/
abbrev sourceData := GlobalPrescribedDivisor.cartier.transitions

/-- The transition presentation of the genuine native canonical bundle. -/
abbrev targetData := NativePresentation.transitionData

/-- Exactly the original divisor-generic open, with no additional deletion. -/
abbrev domain := GlobalFiniteRegularSection.domain

theorem sourceSection_ne_zero (x : Threefold.Space) (hx : x ∈ domain) :
    GlobalPrescribedDivisor.cartier.rawSection x ≠ 0 :=
  GlobalPrescribedDivisor.cartier.rawSection_ne_zero hx

theorem sourceSectionMap_holomorphicOn :
    ContMDiffOn IF Iᴷ ω GlobalPrescribedDivisor.cartier.rawSectionMap domain :=
  GlobalPrescribedDivisor.cartier.rawSectionMap_holomorphicOn

/-- The actual canonical vector in the native transition bundle on the
generic open, extended by zero only to provide a raw global fibre family. -/
def targetSection (x : Threefold.Space) : targetData.core.Fiber x := by
  classical
  exact if hx : x ∈ domain then
    NativePresentation.fiberEquiv x (GlobalFiniteRegularSection.genericSection ⟨x, hx⟩)
  else 0

theorem targetSection_eq (x : Threefold.Space) (hx : x ∈ domain) :
    targetSection x =
      NativePresentation.fiberEquiv x (GlobalFiniteRegularSection.genericSection ⟨x, hx⟩) := by
  classical
  exact dif_pos hx

theorem targetSection_of_notMem (x : Threefold.Space) (hx : x ∉ domain) :
    targetSection x = 0 := by
  classical
  exact dif_neg hx

theorem targetSection_ne_zero (x : Threefold.Space) (hx : x ∈ domain) :
    targetSection x ≠ 0 := by
  intro h
  have he : NativePresentation.fiberEquiv x
      (GlobalFiniteRegularSection.genericSection ⟨x, hx⟩) = 0 :=
    (targetSection_eq x hx).symm.trans h
  exact GlobalFiniteRegularSection.genericSection_ne_zero ⟨x, hx⟩
    ((NativePresentation.fiberEquiv x).map_eq_zero_iff.mp he)

def targetSectionMap (x : Threefold.Space) : targetData.core.TotalSpace := ⟨x, targetSection x⟩

@[simp] theorem targetSectionMap_proj (x : Threefold.Space) :
    (targetSectionMap x).proj = x := rfl

/-- This identifies the actual native total-space map, not just a ratio
of preferred scalar coordinates. -/
theorem targetSectionMap_on_domain (x : domain) :
    targetSectionMap x.val = NativePresentation.bundleBiholomorph
      (GlobalFiniteRegularSection.genericSectionMap x) :=
  congrArg (fun v : targetData.core.Fiber x.val =>
    (⟨x.val, v⟩ : targetData.core.TotalSpace)) (targetSection_eq x.val x.property)

theorem targetSectionMap_restrict_holomorphic :
    ContMDiff IF Iᴷ ω (fun x : domain => targetSectionMap x.val) := by
  have he : (fun x : domain => targetSectionMap x.val) =
      NativePresentation.bundleBiholomorph ∘ GlobalFiniteRegularSection.genericSectionMap :=
    funext targetSectionMap_on_domain
  rw [he]
  exact NativePresentation.bundleBiholomorph.contMDiff.comp
    GlobalFiniteRegularSection.genericSectionMap_holomorphic

theorem targetSectionMap_holomorphicAt (x : Threefold.Space) (hx : x ∈ domain) :
    ContMDiffAt IF Iᴷ ω targetSectionMap x :=
  (contMDiffAt_subtype_iff (I := IF) (I' := Iᴷ) (U := domain)
    (f := targetSectionMap) (x := ⟨x, hx⟩)).mp (targetSectionMap_restrict_holomorphic ⟨x, hx⟩)

theorem targetSectionMap_holomorphicOn : ContMDiffOn IF Iᴷ ω targetSectionMap domain :=
  fun x hx => (targetSectionMap_holomorphicAt x hx).contMDiffWithinAt

theorem targetSection_eq_regular (x : Threefold.Space) (hx : x ∈ domain)
    (hr : x ∈ regularLocus) :
    targetSection x = NativePresentation.fiberEquiv x
      (GlobalRegular.globalSection ⟨x, hr⟩) :=
  (targetSection_eq x hx).trans (congrArg (NativePresentation.fiberEquiv x)
    (GlobalFiniteRegularSection.genericSection_eq_regular ⟨x, hx⟩ hr))

theorem targetSection_eq_three (x : Threefold.Space) (hx : x ∈ domain)
    (h₃ : x ∈ Threefold.liftedPatch (some (some Elliptic.Kind.three))) :
    targetSection x = NativePresentation.fiberEquiv x
      (GlobalEllipticComparison.extendedSection .three ⟨x, h₃⟩) :=
  (targetSection_eq x hx).trans (congrArg (NativePresentation.fiberEquiv x)
    (GlobalFiniteRegularSection.genericSection_eq_three ⟨x, hx⟩ h₃))

theorem targetSection_eq_four (x : Threefold.Space) (hx : x ∈ domain)
    (h₄ : x ∈ Threefold.liftedPatch (some (some Elliptic.Kind.four))) :
    targetSection x = NativePresentation.fiberEquiv x
      (GlobalEllipticComparison.extendedSection .four ⟨x, h₄⟩) :=
  (targetSection_eq x hx).trans (congrArg (NativePresentation.fiberEquiv x)
    (GlobalFiniteRegularSection.genericSection_eq_four ⟨x, hx⟩ h₄))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonGeneric
