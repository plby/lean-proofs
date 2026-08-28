import Wikipedia.NoExoticSixSphere.SevenDimensionalUnroundedTrace
import Wikipedia.NoExoticSixSphere.RoundedSurgeryTrace

/-!
# Supported rounding of the actual seven-manifold attachment

The original geometric inputs construct the actual closed ambient attachment
and a compact supported rounding region. Its collar sheet is smoothly
embedded and immersive, with the original full normal frame. In the proved
uniform band the rounded set is exactly the regular smooth superlevel, and
positive-height points are unchanged. No global compactness is assumed.

This does not yet supply a global smooth boundary atlas or its induced
boundary frame in dimension eight. Surgery homology and the classification
of six-spheres remain separate unproved steps.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel FramedAttachingProduct

universe u

theorem exists_roundedAttachment_of_dimension_seven {M : Type u}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
    [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (hi : Injective f) (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) :
    ∃ A : FramedAttachingProduct e a f,
      IsClosed (RoundedTrace.ambientSet A) ∧
      UnroundedTrace.ambientSet A ⊆ RoundedTrace.ambientSet A ∧
      IsCompact (A.collarSheet '' RoundedTrace.addedParameters A) ∧
      IsEmbedding (fun p : A.tubeHeightCoordinates.source ↦ A.collarSheet p.val) ∧
      ContMDiffOn (((𝓡 3).prod (𝓡 4)).prod 𝓘(ℝ, ℝ)) (𝓡 (e.ambientDimension + 6)) ∞
        A.collarSheet A.tubeHeightCoordinates.source ∧
      (∀ p ∈ A.tubeHeightCoordinates.source,
        Injective (A.collarSheetDerivative p) ∧
          (A.collarSheetFrame p).range = (A.collarSheetDerivative p).rangeᗮ) ∧
      (∀ s : Sphere 3, ∀ v ∈ ball (0 : Vector 4) A.radius,
        ∀ t : ℝ, ‖t‖ ≤ RoundedTrace.collarHeight A →
          (A.collarSheet ((s, v), t) ∈ RoundedTrace.ambientSet A ↔
            0 ≤ RoundedHandleCorner.level (RoundedTrace.bump A)
              (UnroundedTrace.handleRadius A) (v, t))) ∧
      (∀ p : Vector 4 × ℝ, RoundedHandleCorner.level (RoundedTrace.bump A)
          (UnroundedTrace.handleRadius A) p = 0 →
        Surjective (fderiv ℝ (RoundedHandleCorner.level (RoundedTrace.bump A)
          (UnroundedTrace.handleRadius A)) p)) ∧
      ∀ m : M, ∀ t : ℝ, 0 < t →
        (e.heightCylinder (m, t) ∈ RoundedTrace.ambientSet A ↔
          e.heightCylinder (m, t) ∈ UnroundedTrace.ambientSet A) := by
  obtain ⟨A⟩ := e.nonempty_framedAttachingProduct_of_dimension_seven a f hf hi hd
  exact ⟨A, RoundedTrace.isClosed_ambientSet A, RoundedTrace.unrounded_subset A,
    RoundedTrace.isCompact_addedImage A, A.isEmbedding_collarSheet, A.contMDiffOn_collarSheet,
    fun p hp ↦ ⟨A.injective_collarSheetDerivative hp, A.collarSheetFrame_range hp⟩,
    fun s v hv t ht ↦ RoundedTrace.sheet_mem_iff A s hv ht,
    fun p hp ↦ RoundedTrace.regular_corner_zero A hp,
    fun m t ht ↦ RoundedTrace.positive_height_unchanged A m ht⟩

end NoExoticSixSphere.EuclideanEmbedding
