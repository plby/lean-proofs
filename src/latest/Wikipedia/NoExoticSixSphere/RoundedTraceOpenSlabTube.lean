import Wikipedia.NoExoticSixSphere.RoundedTraceSlabTubeData
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# An actual open product tube in the slab

Radial compression gives the full Euclidean framing space as fiber. The
constructed map is an open embedding into the actual closed time slab and
retains its core and exact end preimages. Its inverse on the image is therefore
continuous; smooth inverse regularity is not claimed.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  {A : FramedAttachingProduct e a f}

namespace SlabTubeData

variable (D : SlabTubeData A)

def compression (q : ambientSet A × TimeGraphFrameSpace (e := e)) :
    ambientSet A × TimeGraphFrameSpace (e := e) :=
  (q.1, OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e)) D.radius q.2)

theorem compression_norm_lt (q : ambientSet A × TimeGraphFrameSpace (e := e)) :
    ‖(D.compression q).2‖ < D.radius := by
  have h := (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e)) D.radius).map_source
    (show q.2 ∈ (OpenPartialHomeomorph.univBall
      (0 : TimeGraphFrameSpace (e := e)) D.radius).source by simp)
  rw [OpenPartialHomeomorph.univBall_target _ D.radius_pos, mem_ball, dist_zero_right] at h
  exact h

theorem compression_core (p : ambientSet A) : D.compression (p, 0) = (p, 0) := by
  simp only [compression, OpenPartialHomeomorph.univBall_apply_zero]

theorem isOpenEmbedding_compression : IsOpenEmbedding D.compression := by
  let C := (OpenPartialHomeomorph.refl (ambientSet A)).prod
    (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e)) D.radius)
  have hC : C.source = univ := by
    change univ ×ˢ (OpenPartialHomeomorph.univBall
      (0 : TimeGraphFrameSpace (e := e)) D.radius).source = univ
    rw [OpenPartialHomeomorph.univBall_source, univ_prod_univ]
  exact C.isOpenEmbedding hC

def openTube (q : ambientSet A × TimeGraphFrameSpace (e := e)) : tubeSlab (e := e) :=
  ⟨verticalTube A (D.compression q),
    D.in_slab q.1 (D.compression q).2 (D.compression_norm_lt q).le⟩

theorem continuous_openTube : Continuous D.openTube :=
  ((continuous_verticalTube A).comp D.isOpenEmbedding_compression.continuous).subtype_mk _

theorem injective_openTube : Injective D.openTube := by
  intro q q' he
  let j (p : ambientSet A × TimeGraphFrameSpace (e := e)) :
      ambientSet A × closedBall (0 : TimeGraphFrameSpace (e := e)) D.radius :=
    (p.1, ⟨(D.compression p).2, mem_closedBall_zero_iff.mpr (D.compression_norm_lt p).le⟩)
  have hj : j q = j q' := D.closedEmbedding.injective (congrArg Subtype.val he)
  apply D.isOpenEmbedding_compression.injective
  exact congrArg
    (fun p : ambientSet A × closedBall (0 : TimeGraphFrameSpace (e := e)) D.radius ↦
      (p.1, p.2.val)) hj

theorem isOpenMap_openTube : IsOpenMap D.openTube := by
  intro s hs
  have hcs : IsOpen (D.compression '' s) := D.isOpenEmbedding_compression.isOpenMap s hs
  have hreg : ∀ q ∈ D.compression '' s, Bijective (verticalTubeDifferential A q) := by
    rintro _ ⟨q, _, rfl⟩
    exact D.regular q.1 (D.compression q).2 (D.compression_norm_lt q).le
  have hO := isOpen_verticalTube_image_in_slab A hcs hreg
  have he : D.openTube '' s =
      {z : tubeSlab (e := e) | z.val ∈ verticalTube A '' (D.compression '' s)} := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨D.compression q, ⟨q, hq, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨q, hq, rfl⟩, hqz⟩
      exact ⟨q, hq, Subtype.ext hqz⟩
  rw [he]
  exact hO

theorem isOpenEmbedding_openTube : IsOpenEmbedding D.openTube :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap D.continuous_openTube
    D.injective_openTube D.isOpenMap_openTube

theorem openTube_core (p : ambientSet A) : (D.openTube (p, 0)).val = timeGraph A p := by
  change verticalTube A (D.compression (p, 0)) = timeGraph A p
  rw [D.compression_core, verticalTube_core]

theorem openTube_other_end (p : ambientSet A) (v : TimeGraphFrameSpace (e := e)) :
    timeGraphTimeFunctional (e := e) (D.openTube (p, v)).val = 0 ↔ p ∈ otherEnd A :=
  D.other_end p (D.compression (p, v)).2 (D.compression_norm_lt (p, v)).le

theorem openTube_top_end (p : ambientSet A) (v : TimeGraphFrameSpace (e := e)) :
    timeGraphTimeFunctional (e := e) (D.openTube (p, v)).val = 1 ↔ p ∈ topEnd A :=
  D.top_end p (D.compression (p, v)).2 (D.compression_norm_lt (p, v)).le

end SlabTubeData

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
