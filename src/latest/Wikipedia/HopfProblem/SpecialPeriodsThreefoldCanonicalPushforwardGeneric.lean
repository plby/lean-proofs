import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardGenericRatio
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardGenericGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalMeromorphicSection

/-!
# The generic base coefficient of an arbitrary actual canonical section

The original normalized canonical form is nowhere zero on the exact
inverse image of the sphere minus `1` and infinity.  Dividing an arbitrary
canonical section by this form gives an actual holomorphic function on
that full inverse image.  The proved direct-image equivalence descends
the ratio to a unique holomorphic function on the original base open.
Recovery and restriction compatibility are literal fibrewise equalities.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Generic

open TrianglePeriodFamily.Canonical

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model

/-- The original normalized nonvanishing form on the full generic preimage. -/
def genericFrame (U : Opens RiemannSphere) : PreimageSection (genericPart U) where
  toFun x := GlobalFiniteRegularSection.genericSection (domainPoint U x)
  contMDiff_toFun := GlobalFiniteRegularSection.genericSectionMap_holomorphic.comp
    (domainPoint_holomorphic U)

@[simp] theorem genericFrame_apply (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (genericPart U)) :
    genericFrame U x = GlobalFiniteRegularSection.genericSection (domainPoint U x) := rfl

theorem genericFrame_ne_zero (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (genericPart U)) : genericFrame U x ≠ 0 :=
  GlobalFiniteRegularSection.genericSection_ne_zero (domainPoint U x)

/-- Literal restriction of an arbitrary original section to the generic preimage. -/
def genericRestriction (U : Opens RiemannSphere) (s : PreimageSection U) :
    PreimageSection (genericPart U) := restrictPreimageSection (genericPart_le U) s

@[simp] theorem genericRestriction_apply (U : Opens RiemannSphere)
    (s : PreimageSection U) (x : Threefold.basePreimage (genericPart U)) :
    genericRestriction U s x = s (preimagePoint U x) := rfl

/-- This is the actual holomorphic scalar ratio on the full original preimage. -/
def upstairsRatio (U : Opens RiemannSphere) (s : PreimageSection U) :
    Threefold.PreimageSection (genericPart U) :=
  ratioSection (Threefold.basePreimage (genericPart U))
    (genericRestriction U s) (genericFrame U) (genericFrame_ne_zero U)

@[simp] theorem upstairsRatio_apply (U : Opens RiemannSphere) (s : PreimageSection U)
    (x : Threefold.basePreimage (genericPart U)) :
    upstairsRatio U s x =
      id (α := ℂ) (s (preimagePoint U x)) /
        id (α := ℂ) (GlobalFiniteRegularSection.genericSection (domainPoint U x)) := rfl

/-- Descent uses the proved actual `f_* O = O` equivalence on this exact open. -/
def baseCoefficient (U : Opens RiemannSphere) (s : PreimageSection U) :
    Threefold.BaseSection (genericPart U) :=
  (Threefold.pullbackSectionEquiv (genericPart U)).symm (upstairsRatio U s)

theorem pullback_baseCoefficient (U : Opens RiemannSphere) (s : PreimageSection U) :
    Threefold.pullbackSection (genericPart U) (baseCoefficient U s) = upstairsRatio U s :=
  (Threefold.pullbackSectionEquiv (genericPart U)).apply_symm_apply (upstairsRatio U s)

/-- Exact evaluation of the descended scalar on every actual fibre. -/
theorem baseCoefficient_projection (U : Opens RiemannSphere) (s : PreimageSection U)
    (x : Threefold.basePreimage (genericPart U)) :
    baseCoefficient U s (Threefold.baseProjection (genericPart U) x) = upstairsRatio U s x :=
  congrArg (fun f : Threefold.PreimageSection (genericPart U) => f x)
    (pullback_baseCoefficient U s)

/-- Actual native canonical-section recovery by the normalized generic form. -/
theorem baseCoefficient_smul_genericSection (U : Opens RiemannSphere)
    (s : PreimageSection U) (x : Threefold.basePreimage (genericPart U)) :
    baseCoefficient U s (Threefold.baseProjection (genericPart U) x) •
      GlobalFiniteRegularSection.genericSection (domainPoint U x) = s (preimagePoint U x) :=
  (congrArg (fun c : ℂ => c • genericFrame U x)
    (baseCoefficient_projection U s x)).trans
      (ratio_smul (Threefold.basePreimage (genericPart U))
        (genericRestriction U s) (genericFrame U) (genericFrame_ne_zero U) x)

/-- The same recovery equality for the globally defined original meromorphic form. -/
theorem baseCoefficient_smul_rawSection (U : Opens RiemannSphere)
    (s : PreimageSection U) (x : Threefold.basePreimage (genericPart U)) :
    baseCoefficient U s (Threefold.baseProjection (genericPart U) x) •
      GlobalMeromorphicSection.rawSection x.val = s (preimagePoint U x) :=
  (congrArg (fun v : Threefold.Canonical.bundle.Fiber x.val =>
      baseCoefficient U s (Threefold.baseProjection (genericPart U) x) • v)
    (GlobalMeromorphicSection.rawSection_eq_generic (domainPoint U x).property)).trans
      (baseCoefficient_smul_genericSection U s x)

/-- On the original regular family this recovers the original regular three-form. -/
theorem baseCoefficient_smul_regular (U : Opens RiemannSphere)
    (s : PreimageSection U) (x : Threefold.basePreimage (genericPart U))
    (hx : x.val ∈ Threefold.regularLocus) :
    baseCoefficient U s (Threefold.baseProjection (genericPart U) x) •
      GlobalRegular.globalSection ⟨x.val, hx⟩ = s (preimagePoint U x) :=
  (congrArg (fun v : Threefold.Canonical.bundle.Fiber x.val =>
      baseCoefficient U s (Threefold.baseProjection (genericPart U) x) • v)
    (GlobalMeromorphicSection.rawSection_eq_regular hx).symm).trans
      (baseCoefficient_smul_rawSection U s x)

/-- A base function representing the original section on the generic preimage is unique. -/
theorem baseCoefficient_unique (U : Opens RiemannSphere) (s : PreimageSection U)
    (f : Threefold.BaseSection (genericPart U))
    (hf : ∀ x : Threefold.basePreimage (genericPart U),
      f (Threefold.baseProjection (genericPart U) x) •
        GlobalFiniteRegularSection.genericSection (domainPoint U x) = s (preimagePoint U x)) :
    f = baseCoefficient U s := by
  apply Threefold.pullbackSection_injective (genericPart U)
  apply ContMDiffMap.ext
  intro x
  apply mul_right_cancel₀ (show id (α := ℂ) (genericFrame U x) ≠ 0 from
    genericFrame_ne_zero U x)
  exact (hf x).trans (baseCoefficient_smul_genericSection U s x).symm

/-- Native division commutes with literal restriction on both original spaces. -/
theorem upstairsRatio_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PreimageSection V) :
    upstairsRatio U (restrictPreimageSection h s) =
      HolomorphicFunctionSheaf.restrictionAlgHom IF Threefold.Space
        (preimage_genericPart_mono h) (upstairsRatio V s) := by
  apply ContMDiffMap.ext
  intro x
  rfl

/-- Actual base descent is natural for every inclusion of original base opens. -/
theorem baseCoefficient_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PreimageSection V) :
    baseCoefficient U (restrictPreimageSection h s) =
      HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere
        (genericPart_mono h) (baseCoefficient V s) := by
  apply Threefold.pullbackSection_injective (genericPart U)
  rw [pullback_baseCoefficient, Threefold.pullbackSection_restrict,
    pullback_baseCoefficient]
  exact upstairsRatio_restrict h s

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Generic
