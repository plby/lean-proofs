import Wikipedia.NoExoticSixSphere.SmoothSphereTubeLocalLift
import Wikipedia.NoExoticSixSphere.OpenSphereTubeLocalClass
import Wikipedia.NoExoticSixSphere.LocalPointPullbackNonvanishing

/-!
# Nonzero actual local contributions at transverse tube intersections

Restrict the original supported tube dual to a neighborhood of a
transverse intersection. Its actual lift has a locally invertible
normal coordinate. The original pair-pullback identity identifies its
class with the nonzero normal point pullback. This proves nonvanishing
of the actual local contribution rather than assuming its value.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem SingularMayerVietoris
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothSphereTube

open SphereNormalCapNormalization ProductNormalCohomologyClass SupportedModTwoCohomology
open OpenSphereTubeCap

attribute [local instance] SphereNormalCapNormalization.normalDimension

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace AmbientVector M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 3)) (𝓡 6) (Sphere 3 × NormalVector) M ∞)
  (hsource : Φ.source = univ)
  (g : C(Sphere 3, M)) (U : Set (Sphere 3)) (hU : IsOpen U)
  (htarget : ∀ x ∈ U, g x ∈ Φ.target)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g) (hcore : ∀ s, Φ (s, 0) = f s)

include hU htarget hf hg hcore in
/-- Native transversality proves nonvanishing of the original local tube-class restriction. -/
theorem local_pullback_ne_zero (x : Sphere 3) (y : U) (hxy : f x = g y)
    (ht : Function.Surjective ((mfderiv (𝓡 3) (𝓡 6) f x).coprod
      (mfderiv (𝓡 3) (𝓡 6) g y)))
    (L : Set U) (hL : (g.comp (subtypeInclusion U)) ⁻¹'
      (coreSupport (tube Φ hsource) : Set M) = L) :
    pullbackTo (g.comp (subtypeInclusion U)) (coreSupport (tube Φ hsource) : Set M) L
      hL.subset 3 (supportedClass (tube Φ hsource) (isOpenEmbedding_tube Φ hsource)) ≠ 0 := by
  let q := lift Φ g U htarget
  let τ := tube Φ hsource
  have hτ := isOpenEmbedding_tube Φ hsource
  have hq : τ.comp q = g.comp (subtypeInclusion U) := tube_comp_lift Φ hsource g U htarget
  have hz : (ContinuousMap.snd.comp q) y = 0 :=
    congrArg Prod.snd (lift_core Φ hsource g U htarget f hcore x y hxy)
  have hK : (pointSupport NormalVector : Set NormalVector) =
      {(ContinuousMap.snd.comp q) y} := by
    rw [pointSupport_coe, hz]
  have hpre : (ContinuousMap.snd.comp q) ⁻¹'
      (pointSupport NormalVector : Set NormalVector) = L :=
    (preimage_core_of_lift τ hτ (g.comp (subtypeInclusion U)) q hq).symm.trans hL
  have hn := pullbackTo_ne_zero_of_local_point (ContinuousMap.snd.comp q) y
    (localHomeomorphOn_normal_lift Φ hsource g U htarget hU f hf hg hcore x y hxy ht)
    3 (pointSupport NormalVector : Set NormalVector) hK L hpre
    (pointClass NormalVector 0) (pointClass_ne_zero NormalVector 0)
  intro he
  exact hn ((pullbackTo_supportedClass τ hτ (g.comp (subtypeInclusion U)) q hq L
    hL.subset).symm.trans he)

end NoExoticSixSphere.SmoothSphereTube
