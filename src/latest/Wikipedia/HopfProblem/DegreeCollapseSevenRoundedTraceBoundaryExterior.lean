import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceBoundaryHandle

/-!
# The actual retained original exterior is a native boundary piece

The map is the original embedding at height zero. Both directions are
smooth in the original manifold atlas and the independently constructed
native cylinder-boundary atlas.
-/

noncomputable section

open Function Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def bottomCylinderBoundaryPart : Opens (boundaryPieceDomain A .cylinder) :=
  ⟨Subtype.val ⁻¹' otherBoundaryPart A,
    (otherBoundaryPart A).isOpen.preimage continuous_subtype_val⟩

def exteriorBoundaryLift (m : retainedExterior A) : boundaryPieceDomain A .cylinder := by
  let := traceChartedSpace A
  let := unchangedCylinderChartedSpace A
  let q := exteriorCylinderLift A m
  have hq : (ProductHalfSpace.model (Vector 7)).IsBoundaryPoint q := by
    apply (unchangedCylinder_isBoundaryPoint_iff A q).mpr
    exact Or.inl (congrArg Prod.snd (exteriorCylinderLift_coordinates A m))
  exact ⟨⟨q.val, ((openCover A).isBoundaryPoint_inclusion_iff .cylinder q).mp hq⟩, q.property⟩

theorem exteriorBoundaryLift_coordinates (m : retainedExterior A) :
    cylinderBoundaryCoordinates A (exteriorBoundaryLift A m) = (m.val, 0) :=
  exteriorCylinderLift_coordinates A m

def exteriorBottomBoundaryMap (m : retainedExterior A) : bottomCylinderBoundaryPart A :=
  ⟨exteriorBoundaryLift A m, (cylinderBoundary_mem_other_iff A _).mpr
    (congrArg Prod.snd (exteriorBoundaryLift_coordinates A m))⟩

theorem bottomBoundaryOriginal_ambient (p : bottomCylinderBoundaryPart A) :
    (HeightCylinder.heightCylinder e) ((cylinderBoundaryCoordinates A p.val).1, 0) = p.val.val.val.val := by
  have ht := (cylinderBoundary_mem_other_iff A p.val).mp p.property
  have hc : cylinderBoundaryCoordinates A p.val =
      ((cylinderBoundaryCoordinates A p.val).1, 0) := Prod.ext rfl ht
  exact (congrArg (HeightCylinder.heightCylinder e) hc.symm).trans
    (unchangedCylinderHomeomorph_ambient A (boundaryTracePoint A .cylinder p.val))

def bottomBoundaryOriginalPoint (p : bottomCylinderBoundaryPart A) : retainedExterior A :=
  ⟨(cylinderBoundaryCoordinates A p.val).1, (mem_retainedExterior_iff A _).mpr (by
    rw [bottomBoundaryOriginal_ambient A p]
    exact p.val.property)⟩

def exteriorBoundaryEquiv : retainedExterior A ≃ bottomCylinderBoundaryPart A where
  toFun := exteriorBottomBoundaryMap A
  invFun := bottomBoundaryOriginalPoint A
  left_inv m := Subtype.ext (congrArg Prod.fst (exteriorBoundaryLift_coordinates A m))
  right_inv p := Subtype.ext (Subtype.ext (Subtype.ext
    (Subtype.ext (bottomBoundaryOriginal_ambient A p))))

theorem contMDiff_exteriorBottomBoundaryMap : letI := boundaryPieceAtlas A .cylinder;
    ContMDiff (𝓡 7) (𝓡 7) ∞ (exteriorBottomBoundaryMap A) := by
  let := boundaryPieceAtlas A .cylinder
  apply (ContMDiff.subtypeVal_comp_iff (bottomCylinderBoundaryPart A)
    (exteriorBottomBoundaryMap A)).mp
  apply (contMDiff_cylinderBoundary_iff_coordinates A _).mpr
  have he : cylinderBoundaryCoordinates A ∘ exteriorBoundaryLift A =
      (fun m : retainedExterior A ↦ (m.val, (0 : ℝ))) :=
    funext (exteriorBoundaryLift_coordinates A)
  change ContMDiff (𝓡 7) ((𝓡 7).prod 𝓘(ℝ, ℝ)) ∞
    (cylinderBoundaryCoordinates A ∘ exteriorBoundaryLift A)
  rw [he]
  exact contMDiff_subtype_val.prodMk contMDiff_const

theorem contMDiff_bottomBoundaryOriginalPoint : letI := boundaryPieceAtlas A .cylinder;
    ContMDiff (𝓡 7) (𝓡 7) ∞ (bottomBoundaryOriginalPoint A) := by
  let := boundaryPieceAtlas A .cylinder
  apply (ContMDiff.subtypeVal_comp_iff (retainedExterior A) (bottomBoundaryOriginalPoint A)).mp
  exact contMDiff_fst.comp ((contMDiff_cylinderBoundaryCoordinates A).comp
    (_root_.contMDiff_subtype_val (U := bottomCylinderBoundaryPart A)))

def exteriorBoundaryDiffeomorph : letI := boundaryPieceAtlas A .cylinder;
    retainedExterior A ≃ₘ⟮𝓡 7, 𝓡 7⟯ bottomCylinderBoundaryPart A := by
  let := boundaryPieceAtlas A .cylinder
  exact
    { toEquiv := exteriorBoundaryEquiv A
      contMDiff_toFun := contMDiff_exteriorBottomBoundaryMap A
      contMDiff_invFun := contMDiff_bottomBoundaryOriginalPoint A }

theorem exteriorBoundaryDiffeomorph_ambient (m : retainedExterior A) :
    letI := boundaryPieceAtlas A .cylinder;
    (exteriorBoundaryDiffeomorph A m).val.val.val.val = (HeightCylinder.heightCylinder e) (m.val, 0) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
