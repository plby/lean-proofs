import Wikipedia.NoExoticSixSphere.SevenDimensionalCurvedProduct
import Wikipedia.NoExoticSixSphere.CompatibleCompactCollarFrame
import Wikipedia.NoExoticSixSphere.FramedAttachingProduct

/-!
# Fully framed attaching data for a three-sphere in a framed seven-manifold

The disk, original-atlas tube, corrected eight-dimensional embedded product,
and full normal frame are constructed from the given smooth embedded sphere.
Both the map and frame agree with the original manifold on an entire collar.
The product interior avoids the original ambient space. No compactness of the
manifold, pre-existing framed disk, or attached surgery trace is assumed.

This provides the actual attaching data; it does not yet construct or round
the eight-dimensional surgery trace or prove its effect on homology.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

universe u

theorem nonempty_framedAttachingProduct_of_dimension_seven {M : Type u}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
    [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (hi : Injective f) (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) :
    Nonempty (FramedAttachingProduct e a f) := by
  obtain ⟨D, r, hr, hr1, T, A, R, χ, hχin, hχout, B, _, hc, hCb, _,
    hemb, hlocal, _, hcollar, havoid⟩ :=
    e.exists_curvedProduct_of_dimension_seven a (pole 3) f hf hi hd
  have hχ : (1 / 2 : ℝ) < χ.rOut := by rw [hχout]; linarith
  have hχ1 : χ.rOut < 1 := by rw [hχout]; linarith
  have hrχ : r ≤ χ.rOut := by rw [← hχin]; exact χ.rIn_lt_rOut.le
  have hc' (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : χ.rOut ≤ ‖x‖) :
      D.toFun x = collar (pole 3) (e.toFun ∘ f) x ∧
      T x = boundaryFrameOperator
        (a.orthonormal (f (SphereRadialRetraction.retract (pole 3) x))).val ∧
      A.transverse x = A.transverse (SphereRadialRetraction.retract (pole 3) x).val :=
    hc x hx (hrχ.trans hxr)
  obtain ⟨q, hqχ, hq1, ε, hε, hεB, G, hG, hGc⟩ :=
    e.exists_compatible_compactCurvedCollarFrame a f hf D A R χ B hCb hχ hχ1 hc'
      (fun s v hv ↦ (hlocal s v hv).1)
  refine ⟨{
    disk := D
    map := e.compactCurvedDiskProduct f D A R χ
    map_core := e.compactCurvedDiskProduct_core f D A R χ
    innerRadius := q
    innerRadius_pos := by linarith
    innerRadius_lt_one := hq1
    radius := ε
    radius_pos := hε
    embedded := restrict_closedProduct_embedding
      (fun p : closedBall (0 : Vector 4) 1 × Vector 4 ↦
        e.compactCurvedDiskProduct f D A R χ (p.1.val, p.2)) hεB B.embedded
    smooth := fun x hx v hv ↦ B.smooth x hx v ((closedBall_subset_closedBall hεB) hv)
    immersive := fun x hx v hv ↦ B.immersive x hx v ((closedBall_subset_closedBall hεB) hv)
    tube := e.compactSphereTube f (boundaryComplementOperator A.transverse) R
    tube_core := e.compactSphereTube_core f (boundaryComplementOperator A.transverse) R
    tube_embedded := restrict_closedProduct_embedding
      (e.compactSphereTube f (boundaryComplementOperator A.transverse) R) hεB hemb
    tube_localDiffeomorph := fun s v hv ↦ (hlocal s v ((closedBall_subset_closedBall hεB) hv)).2
    collar_map := fun x hx hxq v _hv ↦ hcollar x hx (hqχ.le.trans hxq) v
    interior_avoids := fun x hx v hv ↦ havoid x hx v ((closedBall_subset_closedBall hεB) hv)
    normalFrame := G
    normalFrame_smooth := fun x hx v hv ↦ (hG x hx v hv).1
    normalFrame_norm := fun x hx v hv ↦ (hG x hx v hv).2.1
    normalFrame_range := fun x hx v hv ↦ (hG x hx v hv).2.2
    collar_frame := fun x hx hxq v hv ↦ hGc x hx hxq v hv }⟩

end NoExoticSixSphere.EuclideanEmbedding
