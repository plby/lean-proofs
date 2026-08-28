import Wikipedia.HopfProblem.HolomorphicPicardNativeGaugeCech
import Wikipedia.HopfProblem.HolomorphicPicardNativeIsoGauge

/-!
# Original native analytic isomorphism is exactly common-cover Čech equality

Both directions use actual original bundle maps and literal unit-sheaf
sections. The common cover is the intersection cover of the original
native trivializations. This is a geometric Čech comparison, not yet the
comparison with native derived sheaf cohomology.
-/

noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative

open HolomorphicExponentialSheaf PeriodTorusLineBundleClassificationNative
  HolomorphicPicard.Cech

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    (V W : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ V] [FiberBundle ℂ W] [VectorBundle ℂ ℂ V] [VectorBundle ℂ ℂ W]
    [ContMDiffVectorBundle ω ℂ V I] [ContMDiffVectorBundle ω ℂ W I]

/-- Arbitrary original native holomorphic line bundles are analytically
isomorphic exactly when their actual Čech classes agree on the common
intersection cover of their original native trivializations. -/
theorem nonempty_analyticBundleIso_iff_commonCover_class_eq :
    Nonempty (AnalyticBundleIso I V W) ↔
      classOf (unitsSheaf I M) (isoGaugeCover M V W)
        (refinement (unitsSheaf I M) Prod.fst
          (isoGaugeCover_le_left M V W) (nativeCocycle I M V)) =
      classOf (unitsSheaf I M) (isoGaugeCover M V W)
        (refinement (unitsSheaf I M) Prod.snd
          (isoGaugeCover_le_right M V W) (nativeCocycle I M W)) := by
  constructor
  · rintro ⟨e⟩
    exact nativeIso_refined_class_eq I M V W e
  · intro h
    exact nonempty_analyticBundleIso_of_refinement_class_eq I M V W
      (isoGaugeCover M V W) Prod.fst Prod.snd
      (isoGaugeCover_le_left M V W) (isoGaugeCover_le_right M V W)
      (isoGaugeCover_covers M V W) h

end Wikipedia.HopfProblem.HolomorphicPicardNative
