import Wikipedia.NoExoticSixSphere.OpenSphereTubeCap
import Wikipedia.NoExoticSixSphere.PointSupportedNormalClass

/-!
# The actual tube class is supported on its core sphere

Extend the original zero-section-supported relative class to its actual
compact image under the supplied open tube. Its insertion is the same
compact-support class used in the proved cap normalization. Pullback by
any continuous map therefore has the literal inverse-image core support.
This is the support needed for local transverse-intersection evaluation.
-/

noncomputable section

open TopologicalSpace

namespace NoExoticSixSphere.OpenSphereTubeCap

open SphereNormalCapNormalization ProductNormalCohomologyClass
open CompactSupportCohomology

attribute [local instance] normalDimension

variable {M : Type} [TopologicalSpace M] [T2Space M]
  (f : C(Sphere 3 × NormalVector, M)) (hf : Topology.IsOpenEmbedding f)

/-- The actual compact range of the original core sphere. -/
def coreSupport : Compacts M := ⟨Set.range (core f), isCompact_range (core f).continuous⟩

omit [T2Space M] in
/-- The original zero-section support maps exactly to the actual core range. -/
theorem image_zeroSectionSupport :
    f '' (zeroSectionSupport NormalVector (Sphere 3) : Set (Sphere 3 × NormalVector)) =
      (coreSupport f : Set M) := by
  ext x
  constructor
  · rintro ⟨⟨s, v⟩, hv, rfl⟩
    rw [zeroSectionSupport_coe] at hv
    have hz : v = 0 := hv.2
    subst v
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨(s, 0), ?_, rfl⟩
    rw [zeroSectionSupport_coe]
    exact ⟨Set.mem_univ _, rfl⟩

/-- Original relative extension to the actual compact core support. -/
def supportedClass : Component M 3 (coreSupport f) :=
  OpenEmbeddingSupportCohomology.extension f hf
    (zeroSectionSupport NormalVector (Sphere 3) : Set (Sphere 3 × NormalVector))
    (zeroSectionSupport NormalVector (Sphere 3)).isCompact
    (coreSupport f : Set M) (image_zeroSectionSupport f) 3
    (supportedNormalClass NormalVector 0 (Sphere 3))

/-- Inserting the supported core class gives the original compact-support tube class. -/
theorem of_supportedClass : of M 3 (coreSupport f) (supportedClass f hf) = compactClass f hf :=
  (openMap_of_image f hf 3 (zeroSectionSupport NormalVector (Sphere 3)) (coreSupport f)
    (image_zeroSectionSupport f) (supportedNormalClass NormalVector 0 (Sphere 3))).symm.trans
      (congrArg (openMap f hf 3) (of_supportedNormalClass NormalVector 0 (Sphere 3)))

variable [CompactSpace M]

/-- Forgetting this actual core support is precisely the original absolute tube class. -/
theorem absoluteClass_eq_toAbsolute : absoluteClass f hf =
    RelativeModTwoCochains.toAbsoluteCohomology (coreSupport f : Set M)ᶜ 3
      (supportedClass f hf) :=
  (congrArg (absoluteEquiv M 3) (of_supportedClass f hf)).symm.trans
    (absoluteEquiv_of M 3 (coreSupport f) (supportedClass f hf))

/-- Actual pullback is represented on the literal inverse image of the core sphere. -/
theorem pullback_absoluteClass {X : Type} [TopologicalSpace X] (g : C(X, M)) :
    ModTwoCapProduct.cohomologyPullback g 3 (absoluteClass f hf) =
      RelativeModTwoCochains.toAbsoluteCohomology (g ⁻¹' (coreSupport f : Set M))ᶜ 3
        (SupportedModTwoCohomology.pullback g (coreSupport f : Set M) 3
          (supportedClass f hf)) :=
  (congrArg (ModTwoCapProduct.cohomologyPullback g 3)
    (absoluteClass_eq_toAbsolute f hf)).trans
      (SupportedModTwoCohomology.toAbsolute_pullback g (coreSupport f : Set M) 3
        (supportedClass f hf)).symm

end NoExoticSixSphere.OpenSphereTubeCap
