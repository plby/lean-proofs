import Wikipedia.NoExoticSixSphere.RoundedTraceTubeOpenMapping

/-!
# Constructed data for a regular embedded slab tube

All fields are supplied by the proved uniform-radius theorem. This bundles
the exact actual tube, slab, and end formulas for subsequent collapse maps.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

structure SlabTubeData where
  radius : ℝ
  radius_pos : 0 < radius
  closedEmbedding : Topology.IsClosedEmbedding
    (fun q : ambientSet A × closedBall (0 : TimeGraphFrameSpace (e := e)) radius ↦
      verticalTube A (q.1, q.2.val))
  regular : ∀ p v, ‖v‖ ≤ radius → Bijective (verticalTubeDifferential A (p, v))
  in_slab : ∀ p v, ‖v‖ ≤ radius → verticalTube A (p, v) ∈ tubeSlab (e := e)
  other_end : ∀ p v, ‖v‖ ≤ radius →
    (timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) = 0 ↔ p ∈ otherEnd A)
  top_end : ∀ p v, ‖v‖ ≤ radius →
    (timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) = 1 ↔ p ∈ topEnd A)

theorem nonempty_slabTubeData : Nonempty (SlabTubeData A) := by
  obtain ⟨r, hr, he, hprop⟩ := exists_verticalTube_regular_embedding_radius A
  exact ⟨{
    radius := r
    radius_pos := hr
    closedEmbedding := he
    regular := fun p v hv ↦ (hprop p v hv).1
    in_slab := fun p v hv ↦ (hprop p v hv).2.1
    other_end := fun p v hv ↦ (hprop p v hv).2.2.1
    top_end := fun p v hv ↦ (hprop p v hv).2.2.2
  }⟩

def slabTubeData : SlabTubeData A := Classical.choice (nonempty_slabTubeData A)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
