import Wikipedia.NoExoticSixSphere.RoundedTraceOpenCover
import Wikipedia.NoExoticSixSphere.IntervalSuperlevel

/-!
# Exact coordinates on the unchanged open cylinder region

The actual cylinder embedding identifies this relatively open trace piece
with an open subset of the interval superlevel. No ambient points or
topologies are replaced by an abstractly equivalent attachment.
-/

noncomputable section

open Function Set Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

abbrev CylinderSuperlevel :=
  {p : M × ℝ // 0 ≤ IntervalSuperlevel.level (UnroundedTrace.height A) p}

def unchangedCylinderWindow : Opens (CylinderSuperlevel A) where
  carrier := {p | e.heightCylinder p.val ∉ range (UnroundedTrace.handleMap A) ∪
    A.collarSheet '' addedParameters A}
  is_open' := ((UnroundedTrace.closedEmbedding_handle A).isClosed_range.union
    (isCompact_addedImage A).isClosed).isOpen_compl.preimage
      (e.continuous_heightCylinder.comp continuous_subtype_val)

theorem cylinderSuperlevel_time (p : CylinderSuperlevel A) :
    p.val.2 ∈ Icc 0 (UnroundedTrace.height A) :=
  (IntervalSuperlevel.nonneg_iff (UnroundedTrace.height_pos A) p.val).mp p.property

theorem cylinderSuperlevel_mem (p : CylinderSuperlevel A) :
    e.heightCylinder p.val ∈ ambientSet A :=
  unrounded_subset A (Or.inl ⟨(p.val.1, ⟨p.val.2, cylinderSuperlevel_time A p⟩), rfl⟩)

def unchangedCylinderMap : C(unchangedCylinderWindow A, ambientSet A) :=
  ⟨fun p ↦ ⟨e.heightCylinder p.val.val, cylinderSuperlevel_mem A p.val⟩,
    (e.continuous_heightCylinder.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩

theorem isEmbedding_unchangedCylinderMap : IsEmbedding (unchangedCylinderMap A) := by
  have he : IsEmbedding (fun p : unchangedCylinderWindow A ↦ e.heightCylinder p.val.val) :=
    e.isEmbedding_heightCylinder.comp (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
  exact he.codRestrict (ambientSet A) (fun p ↦ cylinderSuperlevel_mem A p.val)

theorem range_unchangedCylinderMap : range (unchangedCylinderMap A) =
    (cylinderOnlyPart A : Set (ambientSet A)) := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact p.property
  · intro hy
    obtain ⟨q, hq⟩ := cylinderOnlyPart_mem A ⟨y, hy⟩
    change e.heightCylinder (q.1, q.2.val) = y.val at hq
    let p : CylinderSuperlevel A := ⟨(q.1, q.2.val),
      (IntervalSuperlevel.nonneg_iff (UnroundedTrace.height_pos A) _).mpr q.2.property⟩
    have hp : p ∈ unchangedCylinderWindow A := by
      change e.heightCylinder (q.1, q.2.val) ∉ _
      rw [hq]
      exact hy
    exact ⟨⟨p, hp⟩, Subtype.ext hq⟩

def unchangedCylinderHomeomorph : cylinderOnlyPart A ≃ₜ unchangedCylinderWindow A :=
  ((isEmbedding_unchangedCylinderMap A).toHomeomorph.trans
    (Homeomorph.setCongr (range_unchangedCylinderMap A))).symm

theorem unchangedCylinderHomeomorph_ambient (p : cylinderOnlyPart A) :
    e.heightCylinder (unchangedCylinderHomeomorph A p).val.val = p.val.val :=
  congrArg (fun y : cylinderOnlyPart A ↦ y.val.val)
    ((unchangedCylinderHomeomorph A).symm_apply_apply p)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
