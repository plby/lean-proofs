import Wikipedia.NoExoticSixSphere.UnitSurgeryComparisonSurjective
import Wikipedia.NoExoticSixSphere.UnitSurgeryOverlapFibers

/-! # The smooth comparison with canonical surgery is bijective -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery

open GLOrthonormalization Stiefel RoundedHandleCorner RoundedTrace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem collarEndPoint_eq_handle_of_eq (p : boundaryCollarParameters A)
    (q : boundaryHandleParameters A) (he : collarMap A hR p = handleMap A hR q) :
    collarEndPoint A p = handleEndPoint A q := by
  let := boundaryPieceAtlas A .collar
  let := boundaryPieceAtlas A .handle
  have hu := collar_handle_parameter_of_eq A hR p q he
  have hq : leftCollarToHandle A p hu = q :=
    injective_handleMap A hR ((left_overlap_agreement A hR p hu).symm.trans he)
  rw [← hq]
  exact Subtype.ext (Subtype.ext (Subtype.ext (leftCollarToHandle_ambient A p hu)))

theorem collarEndPoint_eq_exterior_of_eq (p : boundaryCollarParameters A)
    (m : retainedExterior A) (he : collarMap A hR p = exteriorMap A hR m) :
    collarEndPoint A p = exteriorEndPoint A m := by
  let := boundaryPieceAtlas A .collar
  let := boundaryPieceAtlas A .cylinder
  have hu := collar_exterior_parameter_of_eq A hR p m he
  have hm : rightCollarToExterior A p hu = m :=
    injective_exteriorMap A hR ((right_overlap_agreement A hR p hu).symm.trans he)
  rw [← hm]
  exact Subtype.ext (Subtype.ext (Subtype.ext (rightCollarToExterior_ambient A p hu)))

omit [T2Space M] in
theorem endPoint_cover (p : otherBoundaryPart A) :
    p ∈ range (exteriorEndPoint A) ∪ range (handleEndPoint A) ∪ range (collarEndPoint A) := by
  obtain ⟨i, hi⟩ := boundaryPieceDomain_covers A p.val
  cases i with
  | cylinder =>
      let := boundaryPieceAtlas A .cylinder
      let q : bottomCylinderBoundaryPart A := ⟨⟨p.val, hi⟩, p.property⟩
      refine Or.inl (Or.inl ⟨(exteriorBoundaryDiffeomorph A).symm q, ?_⟩)
      have he := (exteriorBoundaryDiffeomorph A).apply_symm_apply q
      exact Subtype.ext (congrArg (fun r : bottomCylinderBoundaryPart A ↦ r.val.val) he)
  | handle =>
      let := boundaryPieceAtlas A .handle
      let q : boundaryPieceDomain A .handle := ⟨p.val, hi⟩
      refine Or.inl (Or.inr ⟨(boundaryHandleDiffeomorph A).symm q, ?_⟩)
      have he := (boundaryHandleDiffeomorph A).apply_symm_apply q
      exact Subtype.ext (congrArg (Subtype.val : boundaryPieceDomain A .handle → Boundary A) he)
  | collar =>
      let := boundaryPieceAtlas A .collar
      let q : boundaryPieceDomain A .collar := ⟨p.val, hi⟩
      refine Or.inr ⟨(boundaryCollarDiffeomorph A).symm q, ?_⟩
      have he := (boundaryCollarDiffeomorph A).apply_symm_apply q
      exact Subtype.ext (congrArg (Subtype.val : boundaryPieceDomain A .collar → Boundary A) he)

theorem injective_comparisonMap : Injective (comparisonMap A hR) := by
  intro p q he
  rcases endPoint_cover A p with (⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩
  all_goals rcases endPoint_cover A q with (⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩
  all_goals simp only [comparisonMap_exteriorEndPoint, comparisonMap_handleEndPoint,
    comparisonMap_collarEndPoint] at he
  · exact congrArg (exteriorEndPoint A) (injective_exteriorMap A hR he)
  · exact (exteriorMap_ne_handleMap A hR x y he).elim
  · exact (collarEndPoint_eq_exterior_of_eq A hR y x he.symm).symm
  · exact (exteriorMap_ne_handleMap A hR y x he.symm).elim
  · exact congrArg (handleEndPoint A) (injective_handleMap A hR he)
  · exact (collarEndPoint_eq_handle_of_eq A hR y x he.symm).symm
  · exact collarEndPoint_eq_exterior_of_eq A hR x y he
  · exact collarEndPoint_eq_handle_of_eq A hR x y he
  · exact congrArg (collarEndPoint A) (injective_collarMap A hR he)

theorem bijective_comparisonMap : Bijective (comparisonMap A hR) :=
  ⟨injective_comparisonMap A hR, surjective_comparisonMap A hR⟩

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
