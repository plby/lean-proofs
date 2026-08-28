import Wikipedia.NoExoticSixSphere.SevenDimensionalManifoldDisk
import Wikipedia.NoExoticSixSphere.FramedDiskThickening

/-!
# A framed embedded eight-dimensional product for the original seven-manifold

The constructed spanning disk and its four complementary directions give
an actual embedded D4 x D4 product of positive transverse radius. Its full
normal frame extends the prescribed core frame exactly. The same complement
restricts to the original internal normal four-frame on the sphere boundary.

The affine product's attaching face has not yet been bent into the original
manifold. Thus this is an actual ambient framed product, not an attached or
rounded surgery trace.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

universe u

theorem exists_framedProduct_of_dimension_seven {M : Type u}
    [TopologicalSpace M] [ChartedSpace (Vector 7) M]
    (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (b : Sphere 3) (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (hi : Injective f) (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) :
    ∃ D : DiskData b (e.toFun ∘ f), ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∃ T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        ∃ A : DiskThickening.FramedProduct D.toFun T 4,
          (∀ s : Sphere 3, T s.val = boundaryFrameOperator (a.orthonormal (f s)).val) ∧
          (∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
            D.toFun x = collar b (e.toFun ∘ f) x ∧
            T x = boundaryFrameOperator
              (a.orthonormal (f (SphereRadialRetraction.retract b x))).val) ∧
          ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector e.ambientDimension) ∞
            (boundaryComplementOperator A.transverse) ∧
          (∀ s v, ‖boundaryComplementOperator A.transverse s v‖ = ‖v‖) ∧
          (∀ s, (boundaryComplementOperator A.transverse s).range = e.tangentImage (f s) ⊓
            (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ) ∧
          ∀ s v, appendZeroMap e.ambientDimension 6
            (boundaryComplementOperator A.transverse s v) = A.transverse s.val v := by
  obtain ⟨D, r, hr, hr1, T, hTs, hTn, hTr, hTb, hTc, C, hCs, hCn, hCr,
    hBs, hBn, hBr, hBa⟩ := e.exists_framedSphereDisk_of_dimension_seven a b f hf hi hd
  have hinj : InjOn D.toFun (closedBall (0 : Vector 4) 1) := by
    intro x hx y hy he
    have he' : (⟨x, hx⟩ : closedBall (0 : Vector 4) 1) = ⟨y, hy⟩ :=
      D.embedded.injective he
    exact congrArg Subtype.val he'
  have hN : ((e.ambientDimension - 7) + 5) + 4 + 4 = e.ambientDimension + 6 := by
    have h := e.dimension_le_ambient (f b)
    omega
  obtain ⟨A, hAC⟩ := DiskThickening.exists_framedProduct_of_transverse D.toFun T
    (fun _ _ ↦ D.smooth.contDiffAt) hinj D.immersive hTs hTn hTr hN C hCs hCn hCr
  refine ⟨D, r, hr, hr1, T, A, hTb, hTc, ?_⟩
  rw [hAC]
  exact ⟨hBs, hBn, hBr, hBa⟩

end NoExoticSixSphere.EuclideanEmbedding
