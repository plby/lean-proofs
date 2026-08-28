import Wikipedia.HopfProblem.DegreeCollapseSevenUnroundedSurgeryTrace
import Wikipedia.HopfProblem.DegreeCollapseGeneralHeightCylinder

/-!
# The matching frame fields descend to the actual compact attachment

The handle frame and stabilized original-manifold frame agree at every
identified point. They descend along the actual compact quotient map to a
continuous, norm-preserving ambient column field on the unrounded union.
The range is the actual normal space on each piece. No smooth boundary atlas
is asserted.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnroundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def handleColumns : C(Handle A,
    Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6)) := by
  refine ⟨fun p ↦ A.normalFrame (p.1.val, p.2.val), ?_⟩
  let j : Handle A → Vector 4 × Vector 4 := fun p ↦ (p.1.val, p.2.val)
  have hj : Continuous j := (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)
  apply continuous_iff_continuousAt.mpr
  intro p
  exact ContinuousAt.comp (f := j)
    (A.normalFrame_smooth p.1.val p.1.property p.2.val
      (handle_vector_mem A p)).continuousAt hj.continuousAt

variable [CompactSpace M]

def cylinderColumns : C(Cylinder A,
    Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6)) :=
  ⟨fun p ↦ boundaryFrameOperator (a.orthonormal p.1).val,
    (contMDiff_boundaryFrameOperator a.contMDiff_orthonormal).continuous.comp continuous_fst⟩

theorem columns_eq_of_map_eq (p : Handle A) (q : Cylinder A)
    (he : handleMap A p = cylinderMap A q) : handleColumns A p = cylinderColumns A q := by
  obtain ⟨s, hs, hm, _⟩ :=
    (intersection_iff A p.1.property (handle_vector_mem A p) q.1 q.2.property).mp he
  change A.normalFrame (p.1.val, p.2.val) = boundaryFrameOperator (a.orthonormal q.1).val
  rw [← hs, A.normalFrame_boundary s p.2.val (handle_vector_mem A p), hm]

def unionMap : C(Cylinder A ⊕ Handle A, ambientSet A) where
  toFun
    | .inl p => ⟨cylinderMap A p, Or.inl ⟨p, rfl⟩⟩
    | .inr p => ⟨handleMap A p, Or.inr ⟨p, rfl⟩⟩
  continuous_toFun := continuous_sum_dom.mpr
    ⟨(cylinderMap A).continuous.subtype_mk _, (handleMap A).continuous.subtype_mk _⟩

theorem surjective_unionMap : Surjective (unionMap A) := by
  rintro ⟨y, ⟨p, rfl⟩ | ⟨p, rfl⟩⟩
  · exact ⟨.inl p, rfl⟩
  · exact ⟨.inr p, rfl⟩

theorem isQuotientMap_unionMap : IsQuotientMap (unionMap A) :=
  (unionMap A).continuous.isClosedMap.isQuotientMap (unionMap A).continuous
    (surjective_unionMap A)

def sumColumns : C(Cylinder A ⊕ Handle A,
    Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6)) where
  toFun := Sum.elim (cylinderColumns A) (handleColumns A)
  continuous_toFun := continuous_sum_dom.mpr
    ⟨(cylinderColumns A).continuous, (handleColumns A).continuous⟩

theorem columns_factorsThrough : FactorsThrough (sumColumns A) (unionMap A) := by
  intro p q he
  have h := congrArg Subtype.val he
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      have hpq := (closedEmbedding_cylinder A).injective h
      exact congrArg (cylinderColumns A) hpq
    | inr q => exact (columns_eq_of_map_eq A q p h.symm).symm
  | inr p =>
    cases q with
    | inl q => exact columns_eq_of_map_eq A p q h
    | inr q =>
      have hpq := (closedEmbedding_handle A).injective h
      exact congrArg (handleColumns A) hpq

def columns : C(ambientSet A,
    Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6)) :=
  (isQuotientMap_unionMap A).lift (sumColumns A) (columns_factorsThrough A)

theorem columns_unionMap (p : Cylinder A ⊕ Handle A) :
    columns A (unionMap A p) = sumColumns A p :=
  ContinuousMap.congr_fun
    ((isQuotientMap_unionMap A).lift_comp (sumColumns A) (columns_factorsThrough A)) p

theorem columns_cylinder (p : Cylinder A) :
    columns A ⟨cylinderMap A p, Or.inl ⟨p, rfl⟩⟩ = cylinderColumns A p :=
  columns_unionMap A (.inl p)

theorem columns_handle (p : Handle A) :
    columns A ⟨handleMap A p, Or.inr ⟨p, rfl⟩⟩ = A.normalFrame (p.1.val, p.2.val) :=
  columns_unionMap A (.inr p)

theorem columns_norm (p : ambientSet A) (v : Vector ((e.ambientDimension - 7) + 5)) :
    ‖columns A p v‖ = ‖v‖ := by
  obtain ⟨q, rfl⟩ := surjective_unionMap A p
  rw [columns_unionMap]
  cases q with
  | inl q => exact norm_boundaryFrameOperator (a.orthonormal q.1) v
  | inr q =>
    exact A.normalFrame_norm q.1.val q.1.property q.2.val (handle_vector_mem A q) v

theorem columns_handle_range (p : Handle A) :
    (columns A ⟨handleMap A p, Or.inr ⟨p, rfl⟩⟩).range =
      (fderiv ℝ A.map (p.1.val, p.2.val)).rangeᗮ := by
  rw [columns_handle]
  exact A.normalFrame_range p.1.val p.1.property p.2.val (handle_vector_mem A p)

theorem columns_cylinder_range (p : Cylinder A) :
    (columns A ⟨cylinderMap A p, Or.inl ⟨p, rfl⟩⟩).range =
      ((HeightCylinder.heightCylinderDerivative e) (p.1, p.2.val)).rangeᗮ := by
  rw [columns_cylinder]
  exact (HeightCylinder.heightCylinder_frame_range e) a (p.1, p.2.val)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnroundedTrace
