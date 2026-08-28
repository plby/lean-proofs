import Wikipedia.NoExoticSixSphere.SixSphereFramedDiskThickening
import Wikipedia.NoExoticSixSphere.EmbeddedInternalSphereTube
import Wikipedia.NoExoticSixSphere.FramedDiskAttachingComparison

/-!
# The candidate's actual framed disk and original-atlas attaching neighborhood

All disk and transverse-frame data come from the proved zero geometric parity.
The original manifold's tubular retraction and a uniform positive radius are
then constructed. Its sphere product is genuinely embedded and locally
diffeomorphic in the original atlas, not in a transported standard atlas.

The affine disk-product face and this curved neighborhood still need to be
matched across a collar before an attached surgery trace can be constructed.
-/

noncomputable section

open Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem exists_framedDisk_attachingNeighborhood (h : M ≃ₜ Sphere 6)
    (f : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    ∃ D : DiskData (pole 3) (e.toFun ∘ f),
      ∃ T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        ∃ A : DiskThickening.FramedProduct D.toFun T,
          (∀ s : Sphere 3, T s.val = boundaryFrameOperator (e.normalFrameOnSphere a f s).val) ∧
          ∃ r : TubularRetraction e, ∃ ε : ℝ, 0 < ε ∧
            IsClosedEmbedding (fun p : Sphere 3 × closedBall (0 : Vector 3) ε ↦
              e.internalSphereTube f A.boundaryTransverse r (p.1, p.2.val)) ∧
            ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 3) ε,
              (s, v) ∈ e.sphereTubeDomain f A.boundaryTransverse r ∧
                IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 3)) (𝓡 6) ∞
                  (e.internalSphereTube f A.boundaryTransverse r) (s, v) := by
  let : CompactSpace M := compactSpace_of_homeomorph h
  let : T2Space M := t2Space_of_homeomorph h
  let : Nonempty M := ⟨f (pole 3)⟩
  obtain ⟨D, T, A, hTb, _, _⟩ := e.exists_framedDiskThickening a h f hf hi hd
  obtain ⟨r⟩ := e.nonempty_tubularRetraction a
  have hiC (s : Sphere 3) : Injective (A.boundaryTransverse s) :=
    Stiefel.injective ⟨A.boundaryTransverse s, e.norm_boundaryTransverse a f hf hd D A hTb s⟩
  obtain ⟨ε, hε, hemb, hlocal⟩ := e.exists_embedded_internalSphereTube f A.boundaryTransverse r
    hf hi A.contMDiff_boundaryTransverse hd hiC (e.range_boundaryTransverse a f hf hd D A hTb)
  exact ⟨D, T, A, hTb, r, ε, hε, hemb, hlocal⟩

end NoExoticSixSphere.EuclideanEmbedding
