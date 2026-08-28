import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceBoundaryEnds

/-!
# Which native boundary pieces lie in the complementary end

The handle and rounded collar boundary pieces lie entirely in the other
end. The unchanged cylinder contributes precisely its zero-height boundary.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem cylinderBoundary_time_cases (p : boundaryPieceDomain A .cylinder) :
    (cylinderBoundaryCoordinates A p).2 = 0 ∨
      (cylinderBoundaryCoordinates A p).2 = UnroundedTrace.height A := by
  let := traceChartedSpace A
  let := unchangedCylinderChartedSpace A
  let q : cylinderOnlyPart A := boundaryTracePoint A .cylinder p
  exact (unchangedCylinder_isBoundaryPoint_iff A q).mp
    (((openCover A).isBoundaryPoint_inclusion_iff .cylinder q).mpr p.val.property)

theorem cylinderBoundary_mem_other_iff (p : boundaryPieceDomain A .cylinder) :
    p.val ∈ otherBoundaryPart A ↔ (cylinderBoundaryCoordinates A p).2 = 0 := by
  have hpos : p.val.val ∈ positiveCylinderPart A ↔
      0 < (cylinderBoundaryCoordinates A p).2 := by
    rw [mem_positiveCylinderPart_iff]
    exact ⟨fun ⟨_, ht⟩ ↦ ht, fun ht ↦ ⟨p.property, ht⟩⟩
  change ¬p.val.val ∈ positiveCylinderPart A ↔ _
  rw [hpos]
  constructor
  · intro hn
    rcases cylinderBoundary_time_cases A p with hz | ht
    · exact hz
    · exact False.elim (hn (ht ▸ UnroundedTrace.height_pos A))
  · intro hz
    rw [hz]
    exact lt_irrefl 0

theorem handleBoundary_mem_other (p : boundaryPieceDomain A .handle) :
    p.val ∈ otherBoundaryPart A := by
  apply (mem_otherBoundaryPart_iff A p.val).mpr
  rintro ⟨m, hm⟩
  exact cylinder_handle_ne A (topLift A m) (boundaryTracePoint A .handle p) hm

theorem collarBoundary_level_zero (p : boundaryPieceDomain A .collar) :
    collarLevel (bump A) (UnroundedTrace.handleRadius A) (collarBoundaryCoordinates A p) = 0 := by
  let := traceChartedSpace A
  let := collarChartedSpace A
  let q : collarPart A := boundaryTracePoint A .collar p
  exact (collar_isBoundaryPoint_iff A q).mp
    (((openCover A).isBoundaryPoint_inclusion_iff .collar q).mpr p.val.property)

theorem collarBoundary_height_nonpos (p : boundaryPieceDomain A .collar) :
    (collarBoundaryCoordinates A p).2 ≤ 0 := by
  have h := SmoothCornerRounding.two_fst_le_level (bump A)
    (GeneralRoundedHandleCorner.coordinates (UnroundedTrace.handleRadius A)
      (collarProjection (collarBoundaryCoordinates A p)))
  change 2 * (collarBoundaryCoordinates A p).2 ≤
    collarLevel (bump A) (UnroundedTrace.handleRadius A) (collarBoundaryCoordinates A p) at h
  rw [collarBoundary_level_zero] at h
  linarith

theorem collarBoundary_mem_other (p : boundaryPieceDomain A .collar) :
    p.val ∈ otherBoundaryPart A := by
  apply (mem_otherBoundaryPart_iff A p.val).mpr
  rintro ⟨m, hm⟩
  have hc := collarHomeomorph_symm_ambient A (boundaryTracePoint A .collar p)
  change A.collarSheet (collarBoundaryCoordinates A p) = p.val.val.val at hc
  have he : (HeightCylinder.heightCylinder e) (m, UnroundedTrace.height A) =
      A.collarSheet (collarBoundaryCoordinates A p) :=
    (congrArg Subtype.val hm).trans hc.symm
  have ht := congrArg Prod.snd ((HeightCylinder.injective_heightCylinder e) he)
  change UnroundedTrace.height A = (collarBoundaryCoordinates A p).2 at ht
  have hn := collarBoundary_height_nonpos A p
  linarith [UnroundedTrace.height_pos A]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
