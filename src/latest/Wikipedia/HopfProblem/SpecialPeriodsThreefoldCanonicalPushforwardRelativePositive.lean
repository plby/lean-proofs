import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativeProjectionLinear
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardCancellation
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardPositive
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsCoefficients

/-!
# The genuine relative canonical direct image is O(+infinity)

The proved native projection formula has target `O(-infinity)` tensor
the dual of the actual sphere canonical bundle. Genuine fibre-linear
holomorphic cancellation identifies this target with the original dual
ideal bundle. That bundle has the actual holomorphic section with local
coefficients `1,w`, sole zero infinity, and genuine order one there.
All section comparisons are O(U)-linear on every original sphere open.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative

open CanonicalGlobalLineBundle
open HolomorphicFunctionSheaf.SphereH1

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₂" => ModelWithCorners.prod (modelWithCornersSelf ℂ ℂ)
  (modelWithCornersSelf ℂ ℂ)

/-- Actual holomorphic cancellation of the base tensor line, with the
original positive dual-ideal bundle as target. -/
def baseTensorPositiveDiffeomorph :
    Diffeomorph I₂ I₂ baseTensorData.core.TotalSpace Positive.bundle.TotalSpace ω :=
  Powers.singleDualSquareDiffeomorph 𝓘(ℂ) CanonicalGlobal.BaseTwist.data

def baseTensorPositiveFiberEquiv (p : RiemannSphere) :
    baseTensorData.core.Fiber p ≃L[ℂ] Positive.bundle.Fiber p :=
  Powers.singleDualSquareFiberEquiv 𝓘(ℂ) CanonicalGlobal.BaseTwist.data p

@[simp] theorem baseTensorPositiveDiffeomorph_mk (p : RiemannSphere)
    (v : baseTensorData.core.Fiber p) :
    baseTensorPositiveDiffeomorph ⟨p, v⟩ = ⟨p, baseTensorPositiveFiberEquiv p v⟩ := rfl

@[simp] theorem baseTensorPositiveDiffeomorph_proj (q : baseTensorData.core.TotalSpace) :
    (baseTensorPositiveDiffeomorph q).proj = q.proj := rfl

/-- The comparison is actual partial evaluation on the original tensor
square, retaining the full continuous dual meaning of the positive line. -/
theorem baseTensorPositiveFiberEquiv_evaluation (p : RiemannSphere)
    (a v : CanonicalGlobal.BaseTwist.bundle.Fiber p) (b : RelativeBundle.baseBundle.Fiber p) :
    Positive.fiberDualEquiv p
        (baseTensorPositiveFiberEquiv p
          (fibreTensorEquiv CanonicalGlobal.BaseTwist.data RelativeBundle.baseData p
            (a ⊗ₜ[ℂ] b))) v =
      dualFiberEquiv (CanonicalGlobal.BaseTwist.data.power 2) p b
        (Powers.squareFiberTensorEquiv 𝓘(ℂ) CanonicalGlobal.BaseTwist.data p
          (a ⊗ₜ[ℂ] v)) :=
  Powers.singleDualSquareTensorEquiv_tmul 𝓘(ℂ) CanonicalGlobal.BaseTwist.data p a v b

/-- The actual native cancellation acts O(U)-linearly on all original base opens. -/
def baseTensorPositiveSectionLinearEquiv (U : Opens RiemannSphere) :
    BaseTensorSection U ≃ₗ[Threefold.BaseSection U] Positive.Section U :=
  NativeBundleSections.Comparison.sectionLinearEquiv baseTensorData.core Positive.bundle 𝓘(ℂ)
    baseTensorPositiveDiffeomorph baseTensorPositiveFiberEquiv
      baseTensorPositiveDiffeomorph_mk U

/-- The cancellation is an isomorphism of the actual native section sheaves. -/
def baseTensorPositiveSheafIso : baseTensorSheaf ≅ Positive.sheaf :=
  NativeBundleSections.Comparison.sheafIso baseTensorData.core Positive.bundle 𝓘(ℂ)
    baseTensorPositiveDiffeomorph baseTensorPositiveFiberEquiv baseTensorPositiveDiffeomorph_mk

/-- The unconditional O(U)-linear relative canonical direct-image formula. -/
def canonicalSectionPositiveEquiv (U : Opens RiemannSphere) :
    Section U ≃ₗ[Threefold.BaseSection U] Positive.Section U :=
  (projectionFormulaSectionLinearEquiv U).trans (baseTensorPositiveSectionLinearEquiv U)

/-- The actual sheaf `f_* ω_(X/ℙ¹)` is the genuine positive infinity line.
Neither the native bundle comparison nor the projection formula is assumed. -/
def relativeCanonicalDirectImageIso : directImage ≅ Positive.sheaf :=
  projectionFormulaSheafIso ≪≫ baseTensorPositiveSheafIso

@[simp] theorem relativeCanonicalDirectImageIso_hom_app (U : Opens RiemannSphere)
    (s : Section U) :
    relativeCanonicalDirectImageIso.hom.hom.app (op U) s = canonicalSectionPositiveEquiv U s :=
  rfl

@[simp] theorem relativeCanonicalDirectImageIso_inv_app (U : Opens RiemannSphere)
    (s : Positive.Section U) :
    relativeCanonicalDirectImageIso.inv.hom.app (op U) s =
      (canonicalSectionPositiveEquiv U).symm s := rfl

instance positiveSheaf_obj_baseModule (U : Opens RiemannSphere) :
    Module (Threefold.BaseSection U) (Positive.sheaf.obj.obj (op U)) :=
  inferInstanceAs (Module (Threefold.BaseSection U) (Positive.Section U))

theorem relativeCanonicalDirectImageIso_hom_app_smul (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : Section U) :
    relativeCanonicalDirectImageIso.hom.hom.app (op U) (f • s) =
      f • relativeCanonicalDirectImageIso.hom.hom.app (op U) s :=
  (canonicalSectionPositiveEquiv U).map_smul f s

theorem relativeCanonicalDirectImageIso_inv_app_smul (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : Positive.Section U) :
    relativeCanonicalDirectImageIso.inv.hom.app (op U) (f • s) =
      f • relativeCanonicalDirectImageIso.inv.hom.app (op U) s :=
  (canonicalSectionPositiveEquiv U).symm.map_smul f s

/-- Exact compatibility of the final actual formula with every base restriction. -/
theorem canonicalSectionPositiveEquiv_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : Section V) :
    NativeBundleSections.Section.restrict Positive.bundle 𝓘(ℂ) h
        (canonicalSectionPositiveEquiv V s) =
      canonicalSectionPositiveEquiv U
        (NativeBundleSections.Section.restrict RelativeBundle.bundle IF
          (Threefold.basePreimage_mono h) s) := by
  exact (NativeBundleSections.Comparison.sectionLinearEquiv_restrict
    baseTensorData.core Positive.bundle 𝓘(ℂ) baseTensorPositiveDiffeomorph
    baseTensorPositiveFiberEquiv baseTensorPositiveDiffeomorph_mk h
      (projectionFormulaSectionLinearEquiv V s)).symm.trans
        (congrArg (baseTensorPositiveSectionLinearEquiv U)
          (projectionFormulaSectionLinearEquiv_restrict h s))

theorem canonicalSectionPositiveEquiv_symm_restrict {U V : Opens RiemannSphere}
    (h : U ≤ V) (s : Positive.Section V) :
    NativeBundleSections.Section.restrict RelativeBundle.bundle IF
        (Threefold.basePreimage_mono h) ((canonicalSectionPositiveEquiv V).symm s) =
      (canonicalSectionPositiveEquiv U).symm
        (NativeBundleSections.Section.restrict Positive.bundle 𝓘(ℂ) h s) := by
  apply (canonicalSectionPositiveEquiv U).injective
  rw [← canonicalSectionPositiveEquiv_restrict, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- Actual local free rank-one trivializations, on all subopens of the
original finite and infinity charts. -/
def directImageLocalTrivialization (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) :
    Threefold.BaseSection U ≃ₗ[Threefold.BaseSection U] Section U :=
  (NativeBundleSections.coefficientLinearEquiv Positive.bundle 𝓘(ℂ) b U
    (fun _ hp => hU hp)).symm.trans (canonicalSectionPositiveEquiv U).symm

theorem relativeCanonicalDirectImage_locally_free_rank_one (p : RiemannSphere) :
    ∃ b : Bool, p ∈ NegativeOneFrames.frameChart b ∧
      ∀ (U : Opens RiemannSphere) (_hU : U ≤ NegativeOneFrames.frameChart b),
        Nonempty (Threefold.BaseSection U ≃ₗ[Threefold.BaseSection U] Section U) := by
  obtain ⟨b, hb⟩ := NegativeOneFrames.frameChart_cover p
  exact ⟨b, hb, fun U hU => ⟨directImageLocalTrivialization b U hU⟩⟩

/-- The relative canonical pushforward formula for the actual threefold
and actual positive infinity line, with no existence or compatibility input. -/
theorem directImage_relative_canonical : Nonempty (directImage ≅ Positive.sheaf) :=
  ⟨relativeCanonicalDirectImageIso⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative
