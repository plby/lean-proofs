import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwistIdealLinear
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsLinear

/-!
# Local ideal identification for the genuine native section interface

The general native bundle-section interface and the earlier base-twist
section interface store exactly the same fibre-valued functions and
holomorphic maps into the same total space. Their comparison preserves
the original pointwise operations. Composing this comparison with the
proved base-twist ideal identification gives local O-linear equivalences
which commute with literal restrictions and changes of valid chart.
-/

noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.BaseIdeal

open HolomorphicFunctionSheaf.SphereH1

local notation "𝒪" => HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere

/-- Actual native holomorphic sections of the original base-twist bundle. -/
abbrev BundleSection (U : Opens RiemannSphere) :=
  NativeBundleSections.Section CanonicalGlobal.BaseTwist.data.core 𝓘(ℂ) U

/-- Literal restriction of the original fibre-valued section. -/
def bundleRestrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : BundleSection V) : BundleSection U :=
  NativeBundleSections.Section.restrict CanonicalGlobal.BaseTwist.data.core 𝓘(ℂ) h s

@[simp] theorem bundleRestrict_apply {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : BundleSection V) (p : U) :
    bundleRestrict h s p = s ⟨(p : RiemannSphere), h p.property⟩ := rfl

@[simp] theorem bundleRestrict_refl {U : Opens RiemannSphere} (s : BundleSection U) :
    bundleRestrict le_rfl s = s :=
  NativeBundleSections.Section.restrict_refl _ _ s

@[simp] theorem bundleRestrict_restrict {U V W : Opens RiemannSphere}
    (hUV : U ≤ V) (hVW : V ≤ W) (s : BundleSection W) :
    bundleRestrict hUV (bundleRestrict hVW s) = bundleRestrict (hUV.trans hVW) s :=
  NativeBundleSections.Section.restrict_restrict _ _ hUV hVW s

/-- The two independently defined section structures contain literally
the same native fibre-valued function and holomorphicity proof. Both
module structures use their already constructed pointwise operations. -/
def legacyLinearEquiv (U : Opens RiemannSphere) :
    BundleSection U ≃ₗ[𝒪 U] CanonicalGlobal.BaseTwist.BundleSection U where
  toFun s := ⟨s.toFun, s.contMDiff_toFun⟩
  invFun s := ⟨s.toFun, s.contMDiff_toFun⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' s t := by
    apply CanonicalGlobal.BaseTwist.IdealBundleSections.Section.ext
    intro p
    rfl
  map_smul' f s := by
    apply CanonicalGlobal.BaseTwist.IdealBundleSections.Section.ext
    intro p
    rfl

@[simp] theorem legacyLinearEquiv_apply (U : Opens RiemannSphere)
    (s : BundleSection U) (p : U) : legacyLinearEquiv U s p = s p := rfl

@[simp] theorem legacyLinearEquiv_symm_apply (U : Opens RiemannSphere)
    (s : CanonicalGlobal.BaseTwist.BundleSection U) (p : U) :
    (legacyLinearEquiv U).symm s p = s p := rfl

/-- Passing between the two actual section structures commutes with
literal restriction without any change of fibre coordinates. -/
theorem legacyLinearEquiv_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : BundleSection V) :
    CanonicalGlobal.BaseTwist.bundleSectionRestrict h (legacyLinearEquiv V s) =
      legacyLinearEquiv U (bundleRestrict h s) := rfl

theorem legacyLinearEquiv_symm_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : CanonicalGlobal.BaseTwist.BundleSection V) :
    (legacyLinearEquiv U).symm (CanonicalGlobal.BaseTwist.bundleSectionRestrict h s) =
      bundleRestrict h ((legacyLinearEquiv V).symm s) := rfl

/-- The local O-linear identification of the original native bundle
sections with the actual ideal of functions vanishing at infinity. -/
def localLinearEquiv (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) :
    BundleSection U ≃ₗ[𝒪 U] NegativeOneSection U :=
  (legacyLinearEquiv U).trans (CanonicalGlobal.BaseTwist.idealLinearEquiv b U hU)

@[simp] theorem localLinearEquiv_apply (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (s : BundleSection U) :
    localLinearEquiv b U hU s =
      CanonicalGlobal.BaseTwist.idealLinearEquiv b U hU (legacyLinearEquiv U s) := rfl

@[simp] theorem localLinearEquiv_symm_apply (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (f : NegativeOneSection U) :
    (localLinearEquiv b U hU).symm f =
      (legacyLinearEquiv U).symm
        ((CanonicalGlobal.BaseTwist.idealLinearEquiv b U hU).symm f) := rfl

/-- The map reads the original bundle chart coefficient and multiplies
it by the actual ideal frame, also on the chart containing infinity. -/
theorem localLinearEquiv_value (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (s : BundleSection U) (p : U) :
    (localLinearEquiv b U hU s).val p =
      (CanonicalGlobal.BaseTwist.bundle.localTriv b
        ⟨(p : RiemannSphere), s p⟩).2 * CanonicalGlobal.BaseTwist.idealFrameValue b p :=
  CanonicalGlobal.BaseTwist.idealEquiv_apply b U hU (legacyLinearEquiv U s) p

/-- Reconstruction uses the original native inverse bundle chart. -/
theorem localLinearEquiv_symm_value (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (f : NegativeOneSection U) (p : U) :
    (localLinearEquiv b U hU).symm f p =
      (CanonicalGlobal.BaseTwist.bundle.localTriv b).symm (p : RiemannSphere)
        ((NegativeOneFrames.chartTrivialization b U hU).symm f p) := rfl

/-- The local linear maps agree whenever both chart descriptions apply. -/
theorem localLinearEquiv_chart_independent (a b : Bool) (U : Opens RiemannSphere)
    (ha : U ≤ NegativeOneFrames.frameChart a) (hb : U ≤ NegativeOneFrames.frameChart b) :
    localLinearEquiv a U ha = localLinearEquiv b U hb := by
  unfold localLinearEquiv
  rw [CanonicalGlobal.BaseTwist.idealLinearEquiv_chart_independent a b U ha hb]

/-- Naturality for literal restrictions of the native sections. -/
theorem localLinearEquiv_restrict (b : Bool) {U V : Opens RiemannSphere} (h : U ≤ V)
    (hV : V ≤ NegativeOneFrames.frameChart b) (s : BundleSection V) :
    negativeOneRestriction h (localLinearEquiv b V hV s) =
      localLinearEquiv b U (h.trans hV) (bundleRestrict h s) := by
  change negativeOneRestriction h
      (CanonicalGlobal.BaseTwist.idealLinearEquiv b V hV (legacyLinearEquiv V s)) =
    CanonicalGlobal.BaseTwist.idealLinearEquiv b U (h.trans hV)
      (legacyLinearEquiv U (bundleRestrict h s))
  rw [CanonicalGlobal.BaseTwist.idealLinearEquiv_restrict, legacyLinearEquiv_restrict]

/-- Inverse reconstruction also commutes with every literal restriction. -/
theorem localLinearEquiv_symm_restrict (b : Bool) {U V : Opens RiemannSphere}
    (h : U ≤ V) (hV : V ≤ NegativeOneFrames.frameChart b) (f : NegativeOneSection V) :
    (localLinearEquiv b U (h.trans hV)).symm (negativeOneRestriction h f) =
      bundleRestrict h ((localLinearEquiv b V hV).symm f) := by
  apply (localLinearEquiv b U (h.trans hV)).injective
  rw [LinearEquiv.apply_symm_apply, ← localLinearEquiv_restrict b h hV,
    LinearEquiv.apply_symm_apply]

/-- Restriction followed by any other valid chart gives the same actual
ideal section, without changing the native bundle section being restricted. -/
theorem localLinearEquiv_restrict_change_chart (a b : Bool)
    {U V : Opens RiemannSphere} (h : U ≤ V)
    (hV : V ≤ NegativeOneFrames.frameChart a) (hU : U ≤ NegativeOneFrames.frameChart b)
    (s : BundleSection V) :
    negativeOneRestriction h (localLinearEquiv a V hV s) =
      localLinearEquiv b U hU (bundleRestrict h s) := by
  rw [localLinearEquiv_restrict,
    localLinearEquiv_chart_independent a b U (h.trans hV) hU]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.BaseIdeal
