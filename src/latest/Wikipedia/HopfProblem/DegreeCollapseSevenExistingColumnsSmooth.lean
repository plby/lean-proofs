import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceNormalFrame

/-!
# The existing global columns are the native smooth full normal frame

The compact-quotient field constructed before the atlas agrees exactly with
the smooth field on each actual open piece. Thus its existing values, including
the retained original-end values, are smooth in the proved global atlas.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem columns_on_cylinder_piece (p : cylinderOnlyPart A) :
    columns A p.val = pieceNormalFrame A .cylinder p := by
  let q := unchangedCylinderHomeomorph A p
  let r : UnroundedTrace.Cylinder A :=
    (q.val.val.1, ⟨q.val.val.2, cylinderSuperlevel_time A q.val⟩)
  have he : UnroundedTrace.cylinderMap A r = p.val.val :=
    unchangedCylinderHomeomorph_ambient A p
  have hp : p.val =
      (⟨UnroundedTrace.cylinderMap A r, Or.inl (Or.inl ⟨r, rfl⟩)⟩ : ambientSet A) :=
    Subtype.ext he.symm
  calc
    columns A p.val = columns A
        ⟨UnroundedTrace.cylinderMap A r, Or.inl (Or.inl ⟨r, rfl⟩)⟩ := congrArg (columns A) hp
    _ = UnroundedTrace.columns A ⟨UnroundedTrace.cylinderMap A r, Or.inl ⟨r, rfl⟩⟩ :=
      columns_unrounded A ⟨UnroundedTrace.cylinderMap A r, Or.inl ⟨r, rfl⟩⟩
    _ = pieceNormalFrame A .cylinder p := UnroundedTrace.columns_cylinder A r

theorem columns_on_handle_piece (p : handleOnlyPart A) :
    columns A p.val = pieceNormalFrame A .handle p := by
  let q := unchangedHandleHomeomorph A p
  let r := handleWindowRestriction A q
  have he : UnroundedTrace.handleMap A r = p.val.val := unchangedHandleHomeomorph_ambient A p
  have hp : p.val =
      (⟨UnroundedTrace.handleMap A r, Or.inl (Or.inr ⟨r, rfl⟩)⟩ : ambientSet A) :=
    Subtype.ext he.symm
  calc
    columns A p.val = columns A
        ⟨UnroundedTrace.handleMap A r, Or.inl (Or.inr ⟨r, rfl⟩)⟩ := congrArg (columns A) hp
    _ = UnroundedTrace.columns A ⟨UnroundedTrace.handleMap A r, Or.inr ⟨r, rfl⟩⟩ :=
      columns_unrounded A ⟨UnroundedTrace.handleMap A r, Or.inr ⟨r, rfl⟩⟩
    _ = pieceNormalFrame A .handle p := UnroundedTrace.columns_handle A r

theorem columns_on_collar_piece (p : collarPart A) :
    columns A p.val = pieceNormalFrame A .collar p := by
  let q := (collarHomeomorph A).symm p
  have hq : A.collarSheet q.val = p.val.val := collarHomeomorph_symm_ambient A p
  change columns A p.val = A.collarSheetFrame q.val
  rcases p.val.property with hp | ⟨r, hr, he⟩
  · have hqmem : A.collarSheet q.val ∈ UnroundedTrace.ambientSet A := hq.symm ▸ hp
    have hy : (⟨p.val.val, hp⟩ : UnroundedTrace.ambientSet A) =
        ⟨A.collarSheet q.val, hqmem⟩ := Subtype.ext hq.symm
    calc
      columns A p.val = UnroundedTrace.columns A ⟨p.val.val, hp⟩ :=
        columns_unrounded A ⟨p.val.val, hp⟩
      _ = UnroundedTrace.columns A ⟨A.collarSheet q.val, hqmem⟩ :=
        congrArg (UnroundedTrace.columns A) hy
      _ = A.collarSheetFrame q.val :=
        unrounded_columns_sheet A q.val.1.1 q.property.1 (collarParameter_time A q) hqmem
  · have hrq : r = q.val := A.injOn_collarSheet
      (addedParameters_subset_source A hr) (collarParameters_subset_source A q.property)
      (he.trans hq.symm)
    have hy : p.val = (⟨addedMap A ⟨r, hr⟩, Or.inr ⟨r, hr, rfl⟩⟩ : ambientSet A) :=
      Subtype.ext he.symm
    calc
      columns A p.val = columns A ⟨addedMap A ⟨r, hr⟩, Or.inr ⟨r, hr, rfl⟩⟩ :=
        congrArg (columns A) hy
      _ = A.collarSheetFrame r := columns_added A ⟨r, hr⟩
      _ = A.collarSheetFrame q.val := congrArg A.collarSheetFrame hrq

theorem columns_on_piece (i : Piece) (p : pieceDomain A i) :
    columns A p.val = pieceNormalFrame A i p := by
  cases i with
  | cylinder => exact columns_on_cylinder_piece A p
  | handle => exact columns_on_handle_piece A p
  | collar => exact columns_on_collar_piece A p

theorem columns_eq_traceNormalFrame (p : ambientSet A) :
    columns A p = traceNormalFrame A p := by
  obtain ⟨i, hi⟩ := pieceDomain_covers A p
  exact (columns_on_piece A i ⟨p, hi⟩).trans (traceNormalFrame_on_piece A i ⟨p, hi⟩).symm

theorem contMDiff_columns : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 7))
      𝓘(ℝ, Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6)) ∞
      (columns A) := by
  let := traceChartedSpace A
  intro p
  exact ((contMDiff_traceNormalFrame A) p).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (columns_eq_traceNormalFrame A))

theorem columns_range (p : ambientSet A) :
    (columns A p).range = (traceAmbientDerivative A p).rangeᗮ := by
  rw [columns_eq_traceNormalFrame]
  exact traceNormalFrame_range A p

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
