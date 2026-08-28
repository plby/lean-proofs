import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceSupport

/-!
# The exact continuous frame on the whole rounded ambient attachment

The unrounded frame and the smooth collar-sheet frame agree on their actual
overlap. Their compact quotient therefore gives one norm-preserving continuous
column field on the rounded set. On each geometric piece its range is the
actual normal space. Global smoothness awaits the native glued boundary atlas.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem unrounded_columns_sheet (s : Sphere 3) {v : Vector 4}
    (hv : v ∈ ball (0 : Vector 4) A.radius) {t : ℝ} (ht : ‖t‖ ≤ collarHeight A)
    (hp : A.collarSheet ((s, v), t) ∈ UnroundedTrace.ambientSet A) :
    UnroundedTrace.columns A ⟨A.collarSheet ((s, v), t), hp⟩ =
      A.collarSheetFrame ((s, v), t) := by
  have htbound : -collarHeight A ≤ t ∧ t ≤ collarHeight A :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using ht)
  by_cases hti : 0 ≤ t
  · exact UnroundedTrace.columns_cylinder A
      (A.tube (s, v), ⟨t, hti, htbound.2.trans (collarHeight_lt_height A).le⟩)
  · have hvhalf : v ∈ closedBall (0 : Vector 4) (UnroundedTrace.handleRadius A) :=
      ((sheet_mem_unrounded_iff A s hv ht).mp hp).resolve_left hti
    have hlo : A.innerRadius ^ 2 - 1 ≤ t := by
      linarith [collarHeight_lt_gap A, htbound.1]
    have hx := A.radialPoint_mem_collar s hlo (le_of_not_ge hti)
    let p : UnroundedTrace.Handle A :=
      (⟨RadialHeightCoordinates.point (s, t), hx.1⟩, ⟨v, hvhalf⟩)
    have hmap : UnroundedTrace.handleMap A p = A.collarSheet ((s, v), t) :=
      A.map_radialPoint_eq_sheet s (ball_subset_closedBall hv) hlo (le_of_not_ge hti)
    have he : (⟨A.collarSheet ((s, v), t), hp⟩ : UnroundedTrace.ambientSet A) =
        ⟨UnroundedTrace.handleMap A p, Or.inr ⟨p, rfl⟩⟩ := Subtype.ext hmap.symm
    rw [he, UnroundedTrace.columns_handle]
    exact A.frame_radialPoint_eq_sheet s (ball_subset_closedBall hv) hlo (le_of_not_ge hti)

def addedMap : C(addedParameters A, Vector (e.ambientDimension + 6)) :=
  ⟨fun p ↦ A.collarSheet p.val,
    continuousOn_iff_continuous_restrict.mp
      (A.contMDiffOn_collarSheet.continuousOn.mono (addedParameters_subset_source A))⟩

def addedColumns : C(addedParameters A,
    Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6)) :=
  ⟨fun p ↦ A.collarSheetFrame p.val,
    continuousOn_iff_continuous_restrict.mp
      (A.contMDiffOn_collarSheetFrame.continuousOn.mono (addedParameters_subset_source A))⟩

theorem columns_eq_of_added_map_eq (p : UnroundedTrace.ambientSet A) (q : addedParameters A)
    (he : p.val = addedMap A q) : UnroundedTrace.columns A p = addedColumns A q := by
  have hqmem : addedMap A q ∈ UnroundedTrace.ambientSet A := he ▸ p.property
  have hp : p = ⟨addedMap A q, hqmem⟩ := Subtype.ext he
  rw [hp]
  have ht : ‖q.val.2‖ ≤ collarHeight A := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith [(twice_outer_lt_height A), q.property.2.1.1]
    · exact q.property.2.1.2.trans (collarHeight_pos A).le
  exact unrounded_columns_sheet A q.val.1.1
    ((closedBall_subset_ball (outerRadius_lt A)) q.property.1) ht hqmem

local instance : CompactSpace (UnroundedTrace.ambientSet A) :=
  isCompact_iff_compactSpace.mp (UnroundedTrace.isCompact_ambientSet A)

local instance : CompactSpace (addedParameters A) :=
  isCompact_iff_compactSpace.mp (isCompact_addedParameters A)

def unionMap : C(UnroundedTrace.ambientSet A ⊕ addedParameters A, ambientSet A) where
  toFun
    | .inl p => ⟨p.val, unrounded_subset A p.property⟩
    | .inr p => ⟨addedMap A p, Or.inr ⟨p.val, p.property, rfl⟩⟩
  continuous_toFun := continuous_sum_dom.mpr
    ⟨continuous_subtype_val.subtype_mk _, (addedMap A).continuous.subtype_mk _⟩

theorem surjective_unionMap : Surjective (unionMap A) := by
  rintro ⟨y, hy | ⟨q, hq, rfl⟩⟩
  · exact ⟨.inl ⟨y, hy⟩, rfl⟩
  · exact ⟨.inr ⟨q, hq⟩, rfl⟩

theorem isQuotientMap_unionMap : IsQuotientMap (unionMap A) :=
  (unionMap A).continuous.isClosedMap.isQuotientMap (unionMap A).continuous
    (surjective_unionMap A)

def sumColumns : C(UnroundedTrace.ambientSet A ⊕ addedParameters A,
    Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6)) where
  toFun := Sum.elim (UnroundedTrace.columns A) (addedColumns A)
  continuous_toFun := continuous_sum_dom.mpr
    ⟨(UnroundedTrace.columns A).continuous, (addedColumns A).continuous⟩

theorem columns_factorsThrough : FactorsThrough (sumColumns A) (unionMap A) := by
  intro p q he
  have h := congrArg Subtype.val he
  cases p with
  | inl p =>
    cases q with
    | inl q => exact congrArg (UnroundedTrace.columns A) (Subtype.ext h)
    | inr q => exact columns_eq_of_added_map_eq A p q h
  | inr p =>
    cases q with
    | inl q => exact (columns_eq_of_added_map_eq A q p h.symm).symm
    | inr q =>
      have hpq : p = q := Subtype.ext
        (A.injOn_collarSheet (addedParameters_subset_source A p.property)
          (addedParameters_subset_source A q.property) h)
      exact congrArg (addedColumns A) hpq

def columns : C(ambientSet A,
    Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6)) :=
  (isQuotientMap_unionMap A).lift (sumColumns A) (columns_factorsThrough A)

theorem columns_unionMap (p : UnroundedTrace.ambientSet A ⊕ addedParameters A) :
    columns A (unionMap A p) = sumColumns A p :=
  ContinuousMap.congr_fun
    ((isQuotientMap_unionMap A).lift_comp (sumColumns A) (columns_factorsThrough A)) p

theorem columns_unrounded (p : UnroundedTrace.ambientSet A) :
    columns A ⟨p.val, unrounded_subset A p.property⟩ = UnroundedTrace.columns A p :=
  columns_unionMap A (.inl p)

theorem columns_added (p : addedParameters A) :
    columns A ⟨addedMap A p, Or.inr ⟨p.val, p.property, rfl⟩⟩ = A.collarSheetFrame p.val :=
  columns_unionMap A (.inr p)

theorem columns_norm (p : ambientSet A) (v : Vector ((e.ambientDimension - 7) + 5)) :
    ‖columns A p v‖ = ‖v‖ := by
  obtain ⟨q, rfl⟩ := surjective_unionMap A p
  rw [columns_unionMap]
  cases q with
  | inl q => exact UnroundedTrace.columns_norm A q v
  | inr q => exact A.collarSheetFrame_norm q.val v

theorem columns_originalEnd (m : M) :
    columns A (originalEnd A m) = boundaryFrameOperator (a.orthonormal m).val :=
  (columns_unrounded A (UnroundedTrace.originalEnd A m)).trans
    (UnroundedTrace.originalEnd_columns A m)

theorem columns_handle_range (p : UnroundedTrace.Handle A) :
    (columns A ⟨UnroundedTrace.handleMap A p, Or.inl (Or.inr ⟨p, rfl⟩)⟩).range =
      (fderiv ℝ A.map (p.1.val, p.2.val)).rangeᗮ := by
  have he := columns_unrounded A
    (⟨UnroundedTrace.handleMap A p, Or.inr ⟨p, rfl⟩⟩ : UnroundedTrace.ambientSet A)
  exact (congrArg (fun B : Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6) ↦ B.range) he).trans
      (UnroundedTrace.columns_handle_range A p)

theorem columns_cylinder_range (p : UnroundedTrace.Cylinder A) :
    (columns A ⟨UnroundedTrace.cylinderMap A p, Or.inl (Or.inl ⟨p, rfl⟩)⟩).range =
      (HeightCylinder.heightCylinderDerivative e (p.1, p.2.val)).rangeᗮ := by
  have he := columns_unrounded A
    (⟨UnroundedTrace.cylinderMap A p, Or.inl ⟨p, rfl⟩⟩ : UnroundedTrace.ambientSet A)
  exact (congrArg (fun B : Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6) ↦ B.range) he).trans
      (UnroundedTrace.columns_cylinder_range A p)

theorem columns_added_range (p : addedParameters A) :
    (columns A ⟨addedMap A p, Or.inr ⟨p.val, p.property, rfl⟩⟩).range =
      (A.collarSheetDerivative p.val).rangeᗮ := by
  rw [columns_added]
  exact A.collarSheetFrame_range (addedParameters_subset_source A p.property)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
