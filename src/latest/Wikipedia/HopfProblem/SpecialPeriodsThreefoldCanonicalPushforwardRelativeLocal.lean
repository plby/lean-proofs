import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativeSections

/-!
# Actual local projection formula for the relative canonical line

Contraction with an actual base cotangent-dual frame reduces a relative
canonical section to an absolute canonical section. Absolute descent
then produces a native base-ideal-bundle section, and tensoring with the
same base frame produces the native base tensor section. The two actual
base-frame changes cancel by O(U)-linearity, proving chart independence
and restriction compatibility without an assumed projection formula.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative

open CanonicalGlobalLineBundle
open HolomorphicFunctionSheaf.SphereH1

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- Native contraction of the pulled-back base factor over its original chart. -/
def sourceContraction (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) :
    Section U ≃ₗ[Threefold.BaseSection U] PresentationSection (Threefold.basePreimage U) :=
  TensorLocal.sectionLinearEquiv NativePresentation.transitionData RelativeBundle.baseData
    IF 𝓘(ℂ) Threefold.projectionSphere Threefold.projectionSphere_holomorphic b U hU

/-- The corresponding actual contraction on the base tensor bundle. -/
def targetContraction (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) :
    BaseTensorSection U ≃ₗ[Threefold.BaseSection U] BaseIdeal.BundleSection U :=
  TensorLocal.sectionEquivOn CanonicalGlobal.BaseTwist.data RelativeBundle.baseData
    𝓘(ℂ) 𝓘(ℂ) id contMDiff_id b U (fun _ hp => hU hp)

@[simp] theorem sourceContraction_apply (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (s : Section U)
    (x : Threefold.basePreimage U) :
    sourceContraction b U hU s x = TensorLocal.unTensorFiberEquiv
      NativePresentation.transitionData RelativeBundle.baseData Threefold.projectionSphere
        Threefold.projectionSphere_holomorphic.continuous b x.val (s x) := rfl

@[simp] theorem targetContraction_apply (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (s : BaseTensorSection U) (p : U) :
    targetContraction b U hU s p = TensorLocal.unTensorFiberEquiv
      CanonicalGlobal.BaseTwist.data RelativeBundle.baseData id continuous_id
        b p.val (s p) := rfl

/-- The original holomorphic base transition on an actual common subopen. -/
def frameTransition (b c : Bool) (U : Opens RiemannSphere)
    (hb : U ≤ NegativeOneFrames.frameChart b) (hc : U ≤ NegativeOneFrames.frameChart c) :
    Threefold.BaseSection U :=
  TensorLocal.chartTransition RelativeBundle.baseData 𝓘(ℂ) b c U hb hc

/-- Changing the actual pulled-back base frame multiplies the absolute
section by exactly the original holomorphic base transition. -/
theorem sourceContraction_change (b c : Bool) (U : Opens RiemannSphere)
    (hb : U ≤ NegativeOneFrames.frameChart b) (hc : U ≤ NegativeOneFrames.frameChart c)
    (s : Section U) : sourceContraction c U hc s =
      frameTransition b c U hb hc • sourceContraction b U hb s := by
  apply NativeBundleSections.Section.ext NativePresentation.transitionBundle IF
  intro x
  exact TensorLocal.unTensorFiberEquiv_change NativePresentation.transitionData
    RelativeBundle.baseData Threefold.projectionSphere
      Threefold.projectionSphere_holomorphic.continuous b c x.val
        (hb x.property) (hc x.property) (s x)

theorem targetContraction_change (b c : Bool) (U : Opens RiemannSphere)
    (hb : U ≤ NegativeOneFrames.frameChart b) (hc : U ≤ NegativeOneFrames.frameChart c)
    (s : BaseTensorSection U) : targetContraction c U hc s =
      frameTransition b c U hb hc • targetContraction b U hb s := by
  apply NativeBundleSections.Section.ext CanonicalGlobal.BaseTwist.data.core 𝓘(ℂ)
  intro p
  exact TensorLocal.unTensorFiberEquiv_change CanonicalGlobal.BaseTwist.data
    RelativeBundle.baseData id continuous_id b c p.val
      (hb p.property) (hc p.property) (s p)

theorem sourceContraction_restrict (b : Bool) {U V : Opens RiemannSphere} (h : U ≤ V)
    (hU : U ≤ NegativeOneFrames.frameChart b) (hV : V ≤ NegativeOneFrames.frameChart b)
    (s : Section V) :
    sourceContraction b U hU
        (NativeBundleSections.Section.restrict RelativeBundle.bundle IF
          (Threefold.basePreimage_mono h) s) =
      NativeBundleSections.Section.restrict NativePresentation.transitionBundle IF
        (Threefold.basePreimage_mono h) (sourceContraction b V hV s) := by
  apply NativeBundleSections.Section.ext NativePresentation.transitionBundle IF
  intro x
  rfl

theorem targetContraction_restrict (b : Bool) {U V : Opens RiemannSphere} (h : U ≤ V)
    (hU : U ≤ NegativeOneFrames.frameChart b) (hV : V ≤ NegativeOneFrames.frameChart b)
    (s : BaseTensorSection V) :
    targetContraction b U hU
        (NativeBundleSections.Section.restrict baseTensorData.core 𝓘(ℂ) h s) =
      BaseIdeal.bundleRestrict h (targetContraction b V hV s) := by
  apply NativeBundleSections.Section.ext CanonicalGlobal.BaseTwist.data.core 𝓘(ℂ)
  intro p
  rfl

/-- The actual O(U)-linear projection-formula comparison on every chart subopen. -/
def localLinearEquiv (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) :
    Section U ≃ₗ[Threefold.BaseSection U] BaseTensorSection U :=
  ((sourceContraction b U hU).trans (presentationToBaseLinearEquiv U)).trans
    (targetContraction b U hU).symm

/-- The local comparison is precisely the absolute comparison after
contracting the same genuine base frame on its source and target. -/
theorem targetContraction_localLinearEquiv (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (s : Section U) :
    targetContraction b U hU (localLinearEquiv b U hU s) =
      presentationToBaseLinearEquiv U (sourceContraction b U hU s) :=
  (targetContraction b U hU).apply_symm_apply _

/-- Agreement of the actual local comparisons is forced by the two
genuine frame-change formulas and the proved absolute O(U)-linearity. -/
theorem localLinearEquiv_chart_independent (b c : Bool) (U : Opens RiemannSphere)
    (hb : U ≤ NegativeOneFrames.frameChart b) (hc : U ≤ NegativeOneFrames.frameChart c)
    (s : Section U) : localLinearEquiv b U hb s = localLinearEquiv c U hc s := by
  apply (targetContraction c U hc).injective
  calc
    targetContraction c U hc (localLinearEquiv b U hb s) =
        frameTransition b c U hb hc •
          targetContraction b U hb (localLinearEquiv b U hb s) :=
      targetContraction_change b c U hb hc _
    _ = frameTransition b c U hb hc •
        presentationToBaseLinearEquiv U (sourceContraction b U hb s) := by
      rw [targetContraction_localLinearEquiv]
    _ = presentationToBaseLinearEquiv U
        (frameTransition b c U hb hc • sourceContraction b U hb s) :=
      ((presentationToBaseLinearEquiv U).map_smul _ _).symm
    _ = presentationToBaseLinearEquiv U (sourceContraction c U hc s) :=
      congrArg (presentationToBaseLinearEquiv U) (sourceContraction_change b c U hb hc s).symm
    _ = targetContraction c U hc (localLinearEquiv c U hc s) :=
      (targetContraction_localLinearEquiv c U hc s).symm

/-- The actual local projection-formula maps commute with literal
restriction on both original spaces. -/
theorem localLinearEquiv_restrict (b : Bool) {U V : Opens RiemannSphere} (h : U ≤ V)
    (hU : U ≤ NegativeOneFrames.frameChart b) (hV : V ≤ NegativeOneFrames.frameChart b)
    (s : Section V) :
    NativeBundleSections.Section.restrict baseTensorData.core 𝓘(ℂ) h
        (localLinearEquiv b V hV s) =
      localLinearEquiv b U hU
        (NativeBundleSections.Section.restrict RelativeBundle.bundle IF
          (Threefold.basePreimage_mono h) s) := by
  apply (targetContraction b U hU).injective
  rw [targetContraction_restrict b h hU hV, targetContraction_localLinearEquiv b V hV,
    ← presentationToBaseLinearEquiv_restrict h, ← sourceContraction_restrict b h hU hV,
    targetContraction_localLinearEquiv b U hU]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative
