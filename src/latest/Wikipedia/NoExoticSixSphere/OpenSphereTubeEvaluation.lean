import Wikipedia.NoExoticSixSphere.OpenSphereTubeSupportedClass
import Wikipedia.HopfProblem.SphereHomologyCoefficientsNaturality

/-!
# Original pairing with a tube core as supported evaluation on the other sphere

Original coefficient reduction and cochain evaluation naturality express
the cap-evaluation pairing with a tube core as evaluation on the original
integral sphere fundamental class. The actual pulled-back representative
is supported on the inverse image of the core, ready for the still-needed
local transverse-intersection calculation and finite-support additivity.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SphereHomologyCoefficients SphereHomology
open scoped Topology

namespace NoExoticSixSphere.OpenSphereTubeCap

open SphereNormalCapNormalization

attribute [local instance] ambientDimension

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace AmbientVector M]
  [CompactSpace M] [SimplyConnectedSpace M]
  (f : C(Sphere 3 × NormalVector, M)) (hf : Topology.IsOpenEmbedding f)
  (m : M) [Subsingleton (π_ 2 M m)]

/-- Both sphere classes use the original reduced fundamental classes and original map actions. -/
theorem pairing_core_sphere (g : C(Sphere 3, M)) :
    MiddleCapEvaluation.pairing (E := AmbientVector) m
        (modHomologyMap 2 (core f) 3 (unitSphereModTopClass 2 2))
        (modHomologyMap 2 g 3 (unitSphereModTopClass 2 2)) =
      SingularModTwoEvaluation.evaluation (Sphere 3) 3
        (ModTwoCapProduct.cohomologyPullback g 3 (absoluteClass f hf))
        (unitSphereTopClass 2) := by
  rw [pairing_core]
  change NativeModTwoMiddleEvaluation.evaluation m (absoluteClass f hf)
    (modHomologyMap 2 g 3
      (reductionHomologyMap 2 (Sphere 3) 3 (unitSphereTopClass 2))) = _
  rw [modHomologyMap_reduction, NativeModTwoMiddleEvaluation.evaluation_reduction]
  exact (ModTwoCohomologyEvaluation.evaluation_naturality
    (K := singularComplex (Sphere 3)) (L := singularComplex M) 3
    (RelativeCoefficients.spaceMap (ModuleCat.of ℤ ℤ) g)
    (absoluteClass f hf) (unitSphereTopClass 2)).symm

/-- The evaluation uses a class on the literal inverse-image intersection support. -/
theorem pairing_core_sphere_supported (g : C(Sphere 3, M)) :
    MiddleCapEvaluation.pairing (E := AmbientVector) m
        (modHomologyMap 2 (core f) 3 (unitSphereModTopClass 2 2))
        (modHomologyMap 2 g 3 (unitSphereModTopClass 2 2)) =
      SingularModTwoEvaluation.evaluation (Sphere 3) 3
        (RelativeModTwoCochains.toAbsoluteCohomology (g ⁻¹' (coreSupport f : Set M))ᶜ 3
          (SupportedModTwoCohomology.pullback g (coreSupport f : Set M) 3
            (supportedClass f hf))) (unitSphereTopClass 2) :=
  (pairing_core_sphere f hf m g).trans
    (congrArg (fun a => SingularModTwoEvaluation.evaluation (Sphere 3) 3 a (unitSphereTopClass 2))
      (pullback_absoluteClass f hf g))

end NoExoticSixSphere.OpenSphereTubeCap
