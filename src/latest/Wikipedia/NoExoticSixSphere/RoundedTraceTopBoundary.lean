import Wikipedia.NoExoticSixSphere.RoundedTraceTopEndSmooth

/-!
# The original end is open and closed in the actual native boundary

Inside the unchanged cylinder, a positive-height boundary point must be at
the top endpoint. This isolates the original end by a relatively open trace
neighborhood and identifies it with an open-and-closed subset of the native
boundary, using the existing subtype topologies throughout.
-/

noncomputable section

open Function Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def positiveCylinderWindow : Opens (cylinderOnlyPart A) where
  carrier := {p | 0 < (unchangedCylinderHomeomorph A p).val.val.2}
  is_open' := isOpen_lt continuous_const
    ((continuous_subtype_val.comp (continuous_subtype_val.comp
      (unchangedCylinderHomeomorph A).continuous)).snd)

def positiveCylinderPart : Opens (ambientSet A) :=
  ⟨Subtype.val '' (positiveCylinderWindow A : Set (cylinderOnlyPart A)),
    (cylinderOnlyPart A).isOpen.isOpenMap_subtype_val _ (positiveCylinderWindow A).isOpen⟩

theorem mem_positiveCylinderPart_iff (p : ambientSet A) : p ∈ positiveCylinderPart A ↔
    ∃ hp : p ∈ cylinderOnlyPart A,
      0 < (unchangedCylinderHomeomorph A ⟨p, hp⟩).val.val.2 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.property, hq⟩
  · rintro ⟨hp, ht⟩
    exact ⟨⟨p, hp⟩, ht, rfl⟩

theorem topMap_mem_positiveCylinder (m : M) : topMap A m ∈ positiveCylinderPart A := by
  apply (mem_positiveCylinderPart_iff A _).mpr
  refine ⟨topMap_mem_cylinderOnly A m, ?_⟩
  change 0 < (unchangedCylinderHomeomorph A (topLift A m)).val.val.2
  rw [topLift_coordinates]
  exact UnroundedTrace.height_pos A

variable [IsManifold (𝓡 6) ∞ M]

theorem mem_topEnd_iff (p : ambientSet A) : letI := traceChartedSpace A;
    p ∈ topEnd A ↔ (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p ∧
      p ∈ positiveCylinderPart A := by
  let := traceChartedSpace A
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨topMap_isBoundaryPoint A m, topMap_mem_positiveCylinder A m⟩
  · rintro ⟨hb, hp⟩
    obtain ⟨hi, ht⟩ := (mem_positiveCylinderPart_iff A p).mp hp
    let q : cylinderOnlyPart A := ⟨p, hi⟩
    let := unchangedCylinderChartedSpace A
    have hq := ((openCover A).isBoundaryPoint_inclusion_iff .cylinder q).mpr hb
    have hend := (unchangedCylinder_isBoundaryPoint_iff A q).mp hq
    have htop := hend.resolve_left (ne_of_gt ht)
    let m := (unchangedCylinderHomeomorph A q).val.val.1
    have hc : (unchangedCylinderHomeomorph A q).val.val =
        (m, UnroundedTrace.height A) := Prod.ext rfl htop
    refine ⟨m, Subtype.ext ?_⟩
    exact (congrArg e.heightCylinder hc.symm).trans
      (unchangedCylinderHomeomorph_ambient A q)

abbrev Boundary := letI := traceChartedSpace A;
  {p : ambientSet A // (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p}

def topBoundaryPart : Opens (Boundary A) :=
  ⟨Subtype.val ⁻¹' positiveCylinderPart A,
    (positiveCylinderPart A).isOpen.preimage continuous_subtype_val⟩

theorem mem_topBoundaryPart_iff (p : Boundary A) :
    p ∈ topBoundaryPart A ↔ p.val ∈ topEnd A := by
  let := traceChartedSpace A
  exact (and_iff_right p.property).symm.trans (mem_topEnd_iff A p.val).symm

theorem isClosed_topBoundaryPart : IsClosed (topBoundaryPart A : Set (Boundary A)) := by
  have he : (topBoundaryPart A : Set (Boundary A)) = Subtype.val ⁻¹' topEnd A := by
    ext p
    exact mem_topBoundaryPart_iff A p
  rw [he]
  exact (isClosed_topEnd A).preimage continuous_subtype_val

def topEndBoundaryHomeomorph : topEnd A ≃ₜ topBoundaryPart A := by
  let := traceChartedSpace A
  exact
    { toFun := fun p ↦ ⟨⟨p.val, ((mem_topEnd_iff A p.val).mp p.property).1⟩,
        ((mem_topEnd_iff A p.val).mp p.property).2⟩
      invFun := fun p ↦ ⟨p.val.val, (mem_topBoundaryPart_iff A p.val).mp p.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }

theorem topEndBoundaryHomeomorph_val (p : topEnd A) :
    (topEndBoundaryHomeomorph A p).val.val = p.val := rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
