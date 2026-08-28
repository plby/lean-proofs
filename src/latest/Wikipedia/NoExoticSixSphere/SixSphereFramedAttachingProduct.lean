import Wikipedia.NoExoticSixSphere.SixSphereCurvedAttachingProduct
import Wikipedia.NoExoticSixSphere.CompatibleCurvedCollarFrame
import Wikipedia.NoExoticSixSphere.FramedAttachingProduct

/-!
# Constructed framed attaching-product data for the candidate

All disk, tube, correction, collar, radius, and normal-frame data are supplied
by the proved geometric constructions. Both the map and its full normal
frame agree exactly with the original manifold on a whole attaching collar.
This provides the local data for a surgery trace; it does not yet construct
the attached manifold or prove a bordism or classification theorem.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem nonempty_framedAttachingProduct (h : M ≃ₜ Sphere 6) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    Nonempty (FramedAttachingProduct e a f) := by
  obtain ⟨D, r, hr, hr1, T, A, R, χ, hχin, hχout, B, hTb, hc, hemb, hlocal, _, havoid⟩ :=
    e.exists_curvedAttachingProduct a h f hf hi hd
  have hχ : (1 / 2 : ℝ) < χ.rOut := by rw [hχout]; linarith
  have hχ1 : χ.rOut < 1 := by rw [hχout]; linarith
  have hrχ : r ≤ χ.rOut := by rw [← hχin]; exact χ.rIn_lt_rOut.le
  have hc' (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : χ.rOut ≤ ‖x‖) :
      D.toFun x = collar (pole 3) (e.toFun ∘ f) x ∧
      T x = boundaryFrameOperator
        (e.normalFrameOnSphere a f (SphereRadialRetraction.retract (pole 3) x)).val ∧
      A.transverse x = A.transverse (SphereRadialRetraction.retract (pole 3) x).val :=
    hc x hx (hrχ.trans hxr)
  obtain ⟨q, hqχ, hq1, ε, hε, hεB, G, hG, hGc⟩ :=
    e.exists_compatible_curvedCollarFrame a f hf hd D A R χ B hTb hχ hχ1 hc'
      (fun s v hv ↦ (hlocal s v hv).1)
  refine ⟨{
    disk := D
    map := e.curvedDiskProduct f D A R χ
    map_core := e.curvedDiskProduct_core f D A R χ
    innerRadius := q
    innerRadius_pos := by linarith
    innerRadius_lt_one := hq1
    radius := ε
    radius_pos := hε
    embedded := restrict_closedProduct_embedding
      (fun p : closedBall (0 : Vector 4) 1 × Vector 3 ↦
        e.curvedDiskProduct f D A R χ (p.1.val, p.2)) hεB B.embedded
    smooth := fun x hx v hv ↦ B.smooth x hx v ((closedBall_subset_closedBall hεB) hv)
    immersive := fun x hx v hv ↦ B.immersive x hx v ((closedBall_subset_closedBall hεB) hv)
    tube := e.internalSphereTube f A.boundaryTransverse R
    tube_core := e.internalSphereTube_core f A.boundaryTransverse R
    tube_embedded := restrict_closedProduct_embedding
      (e.internalSphereTube f A.boundaryTransverse R) hεB hemb
    tube_localDiffeomorph := fun s v hv ↦ (hlocal s v ((closedBall_subset_closedBall hεB) hv)).2
    collar_map := ?_
    interior_avoids := fun x hx v hv ↦ havoid x hx v ((closedBall_subset_closedBall hεB) hv)
    normalFrame := G
    normalFrame_smooth := fun x hx v hv ↦ (hG x hx v hv).1
    normalFrame_norm := fun x hx v hv ↦ (hG x hx v hv).2.1
    normalFrame_range := fun x hx v hv ↦ (hG x hx v hv).2.2
    collar_frame := ?_ }⟩
  · intro x hx hxq v _hv
    have hxr : χ.rOut ≤ ‖x‖ := hqχ.le.trans hxq
    exact e.curvedDiskProduct_collar a f hf hd D A R χ hTb (hχ.trans_le hxr) hxr
      (hc' x hx hxr).1 (hc' x hx hxr).2.2 v
  · intro x hx hxq v hv
    exact hGc x hx hxq v hv

end NoExoticSixSphere.EuclideanEmbedding
