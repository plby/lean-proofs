import Wikipedia.NoExoticSixSphere.RoundedTraceEndCollapse
import Wikipedia.NoExoticSixSphere.CollapseBaseEquiv
import Wikipedia.NoExoticSixSphere.UnitSurgeryInducedEmbedding

/-!
# The endpoint collapses in the original and canonical surgery parametrizations

The existing original-end homeomorphism and canonical surgery diffeomorphism
give actual open tubes on those manifolds. Reparametrizing the compact base
does not change the one-point collapse map. The core embeddings and the
spatial boundary-frame formulas are retained exactly.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def otherEndBaseHomeomorph : otherBoundaryPart A ≃ₜ otherEnd A := by
  let i : otherBoundaryPart A → ambientSet A := fun p ↦ p.val.val
  have hi : IsEmbedding i := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hr : range i = otherEnd A := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.val, q.property, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  exact hi.toHomeomorph.trans (Homeomorph.setCongr hr)

theorem otherEndBaseHomeomorph_val (p : otherBoundaryPart A) :
    (otherEndBaseHomeomorph A p).val = p.val.val := rfl

namespace SlabTubeData

variable {A} (D : SlabTubeData A)

def originalEndTube (q : M × TimeGraphFrameSpace (e := e)) : Vector (e.ambientDimension + 6) :=
  D.endTube true (topEndHomeomorph A q.1, q.2)

theorem isOpenEmbedding_originalEndTube : IsOpenEmbedding D.originalEndTube :=
  (D.isOpenEmbedding_endTube true).comp
    ((topEndHomeomorph A).prodCongr (Homeomorph.refl _)).isOpenEmbedding

theorem originalEndTube_core (m : M) :
    D.originalEndTube (m, 0) = e.heightCylinder (m, UnroundedTrace.height A) :=
  D.endTube_core true (topEndHomeomorph A m)

theorem endCollapse_eq_originalEndTube (z : OnePoint (Vector (e.ambientDimension + 6))) :
    D.endCollapse 1 z = OpenFiberCollapse.collapseOnePoint D.originalEndTube z := by
  exact (D.endCollapse_eq_onePoint_endTube true z).trans
    (OpenFiberCollapse.collapseOnePoint_baseEquiv (D.endTube true)
      (topEndHomeomorph A).toEquiv (D.isOpenEmbedding_endTube true).injective z).symm

end SlabTubeData

variable [T2Space M] (hR : A.radius = 2)

def surgeryEndBaseHomeomorph : UnitSurgery.Target A hR ≃ₜ otherEnd A := by
  let := boundaryChartedSpace A
  let := UnitSurgery.targetChartedSpace A hR
  exact (UnitSurgery.comparisonDiffeomorph A hR).symm.toHomeomorph.trans (otherEndBaseHomeomorph A)

theorem surgeryEndBaseHomeomorph_ambient (p : UnitSurgery.Target A hR) :
    (surgeryEndBaseHomeomorph A hR p).val.val = UnitSurgery.ambientMap A hR p := rfl

namespace SlabTubeData

variable {A} (D : SlabTubeData A)

def surgeryEndTube (q : UnitSurgery.Target A hR × TimeGraphFrameSpace (e := e)) :
    Vector (e.ambientDimension + 6) :=
  D.endTube false (surgeryEndBaseHomeomorph A hR q.1, q.2)

theorem isOpenEmbedding_surgeryEndTube : IsOpenEmbedding (D.surgeryEndTube hR) :=
  (D.isOpenEmbedding_endTube false).comp
    ((surgeryEndBaseHomeomorph A hR).prodCongr (Homeomorph.refl _)).isOpenEmbedding

theorem surgeryEndTube_core (p : UnitSurgery.Target A hR) :
    D.surgeryEndTube hR (p, 0) = UnitSurgery.ambientMap A hR p :=
  D.endTube_core false (surgeryEndBaseHomeomorph A hR p)

theorem endCollapse_eq_surgeryEndTube (z : OnePoint (Vector (e.ambientDimension + 6))) :
    D.endCollapse 0 z = OpenFiberCollapse.collapseOnePoint (D.surgeryEndTube hR) z := by
  exact (D.endCollapse_eq_onePoint_endTube false z).trans
    (OpenFiberCollapse.collapseOnePoint_baseEquiv (D.endTube false)
      (surgeryEndBaseHomeomorph A hR).toEquiv (D.isOpenEmbedding_endTube false).injective z).symm

end SlabTubeData

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
