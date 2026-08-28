import Wikipedia.HopfProblem.DegreeCollapseClopenEmbedding
import Wikipedia.NoExoticSixSphere.ManifoldRawSphereFrame

/-!
# The original geometric sphere parity on a native clopen submanifold

Restriction keeps the ambient embedding and every normal column literally
unchanged. The inherited open-submanifold atlas makes the inclusion smooth
with bijective differential. Its actual raw sphere operator agrees with
the restricted operator, including the original source-dependent twist.
-/

noncomputable section

open Function ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ClopenSphereParity

open GLOrthonormalization Stiefel
open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.SingularMayerVietoris

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (U : TopologicalSpace.Opens M) (hU : IsClosed (U : Set M))
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : C(Sphere 3, U)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

include hf in
theorem smooth_inclusion_comp :
    ContMDiff (𝓡 3) (𝓡 6) ∞ ((subtypeInclusion (U : Set M)).comp f) :=
  (contMDiff_subtype_val (I := 𝓡 6) (U := U)).comp hf

theorem inclusion_comp_injective (hi : Injective f) :
    Injective ((subtypeInclusion (U : Set M)).comp f) := Subtype.val_injective.comp hi

include hf hd in
theorem inclusion_comp_mfderiv_injective (s : Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 6) ((subtypeInclusion (U : Set M)).comp f) s) := by
  change Injective (mfderiv (𝓡 3) (𝓡 6) ((Subtype.val : U → M) ∘ f) s)
  rw [mfderiv_comp s
    ((contMDiff_subtype_val (I := 𝓡 6) (U := U) (n := ∞)).mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))]
  exact (mfderiv_openSubset_val_bijective (I := 𝓡 6) U (f s)).injective.comp (hd s)

theorem rawSphereFrameOperatorMap_restrict :
    (ClopenEmbedding.restrict e U hU).rawSphereFrameOperatorMap
        (ClopenEmbedding.restrictNormalFrame e U hU a) f hf hd =
      e.rawSphereFrameOperatorMap a ((subtypeInclusion (U : Set M)).comp f)
        (smooth_inclusion_comp U f hf) (inclusion_comp_mfderiv_injective U f hf hd) := rfl

theorem sphereParity_restrict (hi : Injective f) :
    (ClopenEmbedding.restrict e U hU).sphereParity
        (ClopenEmbedding.restrictNormalFrame e U hU a) f hf hi hd =
      e.sphereParity a ((subtypeInclusion (U : Set M)).comp f)
        (smooth_inclusion_comp U f hf) (inclusion_comp_injective U f hi)
        (inclusion_comp_mfderiv_injective U f hf hd) := by
  apply zmodTwo_eq_of_zero_iff
  have h₁ := (ClopenEmbedding.restrict e U hU).sphereParity_zero_iff_raw_twisted_extension
    (ClopenEmbedding.restrictNormalFrame e U hU a) f hf hd hi
  have h₂ := e.sphereParity_zero_iff_raw_twisted_extension a
    ((subtypeInclusion (U : Set M)).comp f) (smooth_inclusion_comp U f hf)
    (inclusion_comp_mfderiv_injective U f hf hd) (inclusion_comp_injective U f hi)
  have he := congrArg SpanningDiskFrameCoordinates.twistedBlockMap
    (rawSphereFrameOperatorMap_restrict e U hU a f hf hd)
  exact h₁.trans ((congrArg DiskBoundary.Extends he).to_iff.trans h₂.symm)

end NoExoticSixSphere.ClopenSphereParity
