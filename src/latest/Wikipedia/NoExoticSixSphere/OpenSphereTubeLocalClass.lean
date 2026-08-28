import Wikipedia.NoExoticSixSphere.OpenSphereTubeSupportedClass
import Wikipedia.NoExoticSixSphere.SupportedCohomologyPairPullback

/-!
# The actual tube class in original local normal coordinates

A continuous lift into the supplied open tube pulls its constructed
supported dual back to the original normal point class. Both the
inverse-image support equality and the cohomology identity use the
actual tube map and original inverse-excision extension. The source
support can be named separately, as needed on isolating neighborhoods.
-/

noncomputable section

open Set

namespace NoExoticSixSphere.OpenSphereTubeCap

open SphereNormalCapNormalization ProductNormalCohomologyClass SupportedModTwoCohomology

attribute [local instance] normalDimension

variable {M X : Type} [TopologicalSpace M] [T2Space M] [TopologicalSpace X]
  (f : C(Sphere 3 × NormalVector, M)) (hf : Topology.IsOpenEmbedding f)

include hf in
omit [T2Space M] in
/-- The normal-coordinate support is exactly the original core inverse image. -/
theorem preimage_core_of_lift (g : C(X, M)) (q : C(X, Sphere 3 × NormalVector))
    (hq : f.comp q = g) :
    g ⁻¹' (coreSupport f : Set M) =
      (ContinuousMap.snd.comp q) ⁻¹' (pointSupport NormalVector : Set NormalVector) := by
  have he := congrArg (fun K : Set (Sphere 3 × NormalVector) => q ⁻¹' K)
    (OpenEmbeddingSupportCohomology.preimage_support f hf
      (zeroSectionSupport NormalVector (Sphere 3) : Set (Sphere 3 × NormalVector))
      (coreSupport f : Set M) (image_zeroSectionSupport f))
  have hfg := congrArg (fun k : C(X, M) => k ⁻¹' (coreSupport f : Set M)) hq
  exact hfg.symm.trans he

/-- Actual tube-class pullback is original point-class pullback in the actual normal coordinate. -/
theorem pullbackTo_supportedClass (g : C(X, M)) (q : C(X, Sphere 3 × NormalVector))
    (hq : f.comp q = g) (L : Set X) (hL : g ⁻¹' (coreSupport f : Set M) ⊆ L) :
    pullbackTo g (coreSupport f : Set M) L hL 3 (supportedClass f hf) =
      pullbackTo (ContinuousMap.snd.comp q) (pointSupport NormalVector : Set NormalVector)
        L ((preimage_core_of_lift f hf g q hq).symm.subset.trans hL) 3
          (pointClass NormalVector 0) := by
  let K : Set (Sphere 3 × NormalVector) := zeroSectionSupport NormalVector (Sphere 3)
  have hK : f ⁻¹' (coreSupport f : Set M) ⊆ K :=
    (OpenEmbeddingSupportCohomology.preimage_support f hf K
      (coreSupport f : Set M) (image_zeroSectionSupport f)).subset
  have hqK : q ⁻¹' K ⊆ L :=
    (preimage_core_of_lift f hf g q hq).symm.subset.trans hL
  have hr : pullbackTo f (coreSupport f : Set M) K hK 3 (supportedClass f hf) =
      supportedNormalClass NormalVector 0 (Sphere 3) :=
    OpenEmbeddingSupportCohomology.pullbackTo_extension f hf K
      (zeroSectionSupport NormalVector (Sphere 3)).isCompact
      (coreSupport f : Set M) (image_zeroSectionSupport f) 3
      (supportedNormalClass NormalVector 0 (Sphere 3))
  have hc := pullbackTo_comp q f (coreSupport f : Set M) K L hK hqK 3 (supportedClass f hf)
  have hn := pullbackTo_comp q (ContinuousMap.snd : C(Sphere 3 × NormalVector, NormalVector))
    (pointSupport NormalVector : Set NormalVector) K L (Subset.refl _) hqK 3
    (pointClass NormalVector 0)
  subst g
  exact hc.trans ((congrArg (pullbackTo q K L hqK 3) hr).trans hn.symm)

end NoExoticSixSphere.OpenSphereTubeCap
