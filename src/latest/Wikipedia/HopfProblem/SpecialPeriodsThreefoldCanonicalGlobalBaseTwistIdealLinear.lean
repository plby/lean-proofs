import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwistIdeal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwistIdealBundleSectionsLinear

/-!
# O-linear local identification of the native base twist with its ideal sheaf

The already constructed local section equivalences are linear over the
actual ring of holomorphic functions on every chart subopen.  The native
bundle-section operations are the literal pointwise fibre operations,
not algebra structures transported from the ideal.  Restriction and
chart independence retain the exact maps proved in the preceding file.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist

open HolomorphicFunctionSheaf.SphereH1

/-- The actual O(U)-linear identification of native holomorphic bundle
sections with the literal ideal of holomorphic functions vanishing at infinity. -/
def idealLinearEquiv (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) :
    BundleSection U ≃ₗ[HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U]
      NegativeOneSection U :=
  (IdealBundleSections.coefficientLinearEquiv data 𝓘(ℂ) b U
    (fun _ hp => hU hp)).trans (NegativeOneFrames.chartTrivialization b U hU)

@[simp] theorem idealLinearEquiv_apply (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (s : BundleSection U) :
    idealLinearEquiv b U hU s = idealEquiv b U hU s := rfl

@[simp] theorem idealLinearEquiv_symm_apply (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (f : NegativeOneSection U) :
    (idealLinearEquiv b U hU).symm f = (idealEquiv b U hU).symm f := rfl

/-- The O-linear identification sends the native unit frame to the
actual ideal-sheaf frame, including the reciprocal frame at infinity. -/
theorem idealLinearEquiv_nativeFrame (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) :
    idealLinearEquiv b U hU (nativeFrame b U hU) =
      NegativeOneFrames.chartFrame b U hU :=
  idealEquiv_nativeFrame b U hU

/-- The native frame is nonzero in every bundle fibre, also at infinity;
the vanishing of its ideal-function image does not make the fibre vector zero. -/
theorem nativeFrame_ne_zero (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (p : U) : nativeFrame b U hU p ≠ 0 := by
  intro hz
  have hc := nativeFrame_localCoefficient b U hU p
  rw [hz] at hc
  change (data.transition (data.indexAt p) b p : ℂ) * 0 = 1 at hc
  exact zero_ne_one ((mul_zero _).symm.trans hc)

/-- Literal restriction preserves the actual native unit frame. -/
theorem nativeFrame_restrict (b : Bool) {U V : Opens RiemannSphere} (h : U ≤ V)
    (hV : V ≤ NegativeOneFrames.frameChart b) :
    bundleSectionRestrict h (nativeFrame b V hV) = nativeFrame b U (h.trans hV) := by
  apply IdealBundleSections.Section.ext
  intro p
  rfl

/-- The linear identifications agree on every common chart subopen. -/
theorem idealLinearEquiv_chart_independent (a b : Bool) (U : Opens RiemannSphere)
    (ha : U ≤ NegativeOneFrames.frameChart a) (hb : U ≤ NegativeOneFrames.frameChart b) :
    idealLinearEquiv a U ha = idealLinearEquiv b U hb := by
  apply LinearEquiv.ext
  exact idealEquiv_chart_independent a b U ha hb

/-- Naturality for literal restrictions of the original section modules. -/
theorem idealLinearEquiv_restrict (b : Bool) {U V : Opens RiemannSphere} (h : U ≤ V)
    (hV : V ≤ NegativeOneFrames.frameChart b) (s : BundleSection V) :
    negativeOneRestriction h (idealLinearEquiv b V hV s) =
      idealLinearEquiv b U (h.trans hV) (bundleSectionRestrict h s) :=
  idealEquiv_restrict b h hV s

/-- The inverse O-linear identification is natural for restrictions as well. -/
theorem idealLinearEquiv_symm_restrict (b : Bool) {U V : Opens RiemannSphere}
    (h : U ≤ V) (hV : V ≤ NegativeOneFrames.frameChart b) (f : NegativeOneSection V) :
    (idealLinearEquiv b U (h.trans hV)).symm (negativeOneRestriction h f) =
      bundleSectionRestrict h ((idealLinearEquiv b V hV).symm f) :=
  idealEquiv_symm_restrict b h hV f

/-- Restriction followed by a change of valid frame gives the same
O-linear identification of the actual sections. -/
theorem idealLinearEquiv_restrict_change_chart (a b : Bool) {U V : Opens RiemannSphere}
    (h : U ≤ V) (hV : V ≤ NegativeOneFrames.frameChart a)
    (hU : U ≤ NegativeOneFrames.frameChart b) (s : BundleSection V) :
    negativeOneRestriction h (idealLinearEquiv a V hV s) =
      idealLinearEquiv b U hU (bundleSectionRestrict h s) :=
  idealEquiv_restrict_change_chart a b h hV hU s

/-- Every point has an actual chart on all of whose subopens the native
bundle section module is O-linearly identified with the actual ideal. -/
theorem native_bundle_locally_linearly_identifies_ideal (p : RiemannSphere) :
    ∃ b : Bool, p ∈ NegativeOneFrames.frameChart b ∧
      ∀ (U : Opens RiemannSphere) (_hU : U ≤ NegativeOneFrames.frameChart b),
        Nonempty (BundleSection U ≃ₗ[
          HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U] NegativeOneSection U) := by
  obtain ⟨b, hb⟩ := NegativeOneFrames.frameChart_cover p
  exact ⟨b, hb, fun U hU => ⟨idealLinearEquiv b U hU⟩⟩

end Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist
