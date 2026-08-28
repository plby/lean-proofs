import Wikipedia.NoExoticSixSphere.RoundedTraceOpenSlabTube
import Wikipedia.NoExoticSixSphere.RoundedTraceSlabProductCoordinates
import Wikipedia.NoExoticSixSphere.OpenFiberCollapse
import Mathlib.Topology.Homotopy.Basic

/-!
# A based collapse homotopy from the actual rounded framed trace

The constructed open product tube embeds in the compactified spatial
cylinder. Compactness of the actual trace proves continuity at the collapsed
complement, uniformly in time. The homotopy fixes spatial infinity and has
the exact native trace slices as its zero fibers. Identifying the end maps
with earlier framed-collapse choices remains a separate comparison.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  {A : FramedAttachingProduct e a f}

namespace SlabTubeData

variable (D : SlabTubeData A)

def compactCylinderTube (q : ambientSet A × TimeGraphFrameSpace (e := e)) :
    I × OnePoint (Vector (e.ambientDimension + 6)) :=
  let z := slabProductCoordinates (e := e) (D.openTube q)
  (z.1, (z.2 : OnePoint _))

theorem isOpenEmbedding_compactCylinderTube : IsOpenEmbedding D.compactCylinderTube := by
  have hi : IsOpenEmbedding
      (Prod.map (id : I → I) ((↑) : Vector (e.ambientDimension + 6) →
        OnePoint (Vector (e.ambientDimension + 6)))) :=
    (Homeomorph.refl I).isOpenEmbedding.prodMap OnePoint.isOpenEmbedding_coe
  exact hi.comp ((slabProductCoordinates (e := e)).isOpenEmbedding.comp D.isOpenEmbedding_openTube)

theorem compactCylinderTube_core (p : ambientSet A) :
    D.compactCylinderTube (p, 0) =
      (⟨bordismTime A p, bordismTime_mem_Icc A p⟩, (p.val : OnePoint _)) := by
  apply Prod.ext
  · apply Subtype.ext
    change timeGraphTimeFunctional (e := e) (D.openTube (p, 0)).val = bordismTime A p
    rw [D.openTube_core]
    rfl
  · change ((timeGraphCoordinates (e := e) (D.openTube (p, 0)).val).2 :
      OnePoint (Vector (e.ambientDimension + 6))) = _
    rw [D.openTube_core, timeGraph_coordinates]

theorem not_mem_compactCylinderTube_infty (t : I) :
    (t, OnePoint.infty) ∉ range D.compactCylinderTube := by
  rintro ⟨q, hq⟩
  have h := congrArg (fun z : I × OnePoint (Vector (e.ambientDimension + 6)) ↦ z.2) hq
  exact OnePoint.coe_ne_infty _ h

def cylinderCollapse :
    C(I × OnePoint (Vector (e.ambientDimension + 6)), OnePoint (TimeGraphFrameSpace (e := e))) :=
  ⟨OpenFiberCollapse.collapse D.compactCylinderTube, by
    let := isCompact_iff_compactSpace.mp (isCompact_ambientSet A)
    exact OpenFiberCollapse.continuous_collapse _ D.isOpenEmbedding_compactCylinderTube⟩

def endCollapse (t : I) :
    C(OnePoint (Vector (e.ambientDimension + 6)), OnePoint (TimeGraphFrameSpace (e := e))) :=
  D.cylinderCollapse.comp ((ContinuousMap.const _ t).prodMk (ContinuousMap.id _))

def collapseHomotopy : (D.endCollapse 0).Homotopy (D.endCollapse 1) where
  toContinuousMap := D.cylinderCollapse
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem collapseHomotopy_infty (t : I) :
    D.collapseHomotopy (t, OnePoint.infty) = OnePoint.infty :=
  OpenFiberCollapse.collapse_of_not_mem _ (D.not_mem_compactCylinderTube_infty t)

theorem collapseHomotopy_tube (q : ambientSet A × TimeGraphFrameSpace (e := e)) :
    D.collapseHomotopy (D.compactCylinderTube q) = (q.2 : OnePoint _) :=
  OpenFiberCollapse.collapse_apply _ D.isOpenEmbedding_compactCylinderTube.injective q

theorem collapseHomotopy_zero_fiber
    (t : I) (z : OnePoint (Vector (e.ambientDimension + 6))) :
    D.collapseHomotopy (t, z) = (↑(0 : TimeGraphFrameSpace (e := e))) ↔
      ∃ p : ambientSet A, bordismTime A p = t.val ∧ (p.val : OnePoint _) = z := by
  change OpenFiberCollapse.collapse D.compactCylinderTube (t, z) =
    (↑(0 : TimeGraphFrameSpace (e := e))) ↔ _
  rw [OpenFiberCollapse.collapse_eq_coe_iff _ D.isOpenEmbedding_compactCylinderTube.injective]
  constructor
  · rintro ⟨p, hp⟩
    rw [D.compactCylinderTube_core] at hp
    exact ⟨p,
      congrArg (fun q : I × OnePoint (Vector (e.ambientDimension + 6)) ↦ q.1.val) hp,
      congrArg (fun q : I × OnePoint (Vector (e.ambientDimension + 6)) ↦ q.2) hp⟩
  · rintro ⟨p, ht, hz⟩
    refine ⟨p, ?_⟩
    rw [D.compactCylinderTube_core]
    exact Prod.ext (Subtype.ext ht) hz

theorem endCollapse_zero_fiber_other (z : OnePoint (Vector (e.ambientDimension + 6))) :
    D.endCollapse 0 z = (↑(0 : TimeGraphFrameSpace (e := e))) ↔
      ∃ p : ambientSet A, p ∈ otherEnd A ∧ (p.val : OnePoint _) = z := by
  change D.collapseHomotopy (0, z) = (↑(0 : TimeGraphFrameSpace (e := e))) ↔ _
  rw [D.collapseHomotopy_zero_fiber]
  change (∃ p : ambientSet A, bordismTime A p = 0 ∧ (p.val : OnePoint _) = z) ↔ _
  simp only [bordismTime_zero_iff]

theorem endCollapse_zero_fiber_top (z : OnePoint (Vector (e.ambientDimension + 6))) :
    D.endCollapse 1 z = (↑(0 : TimeGraphFrameSpace (e := e))) ↔
      ∃ p : ambientSet A, p ∈ topEnd A ∧ (p.val : OnePoint _) = z := by
  change D.collapseHomotopy (1, z) = (↑(0 : TimeGraphFrameSpace (e := e))) ↔ _
  rw [D.collapseHomotopy_zero_fiber]
  change (∃ p : ambientSet A, bordismTime A p = 1 ∧ (p.val : OnePoint _) = z) ↔ _
  simp only [bordismTime_one_iff]

end SlabTubeData

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
