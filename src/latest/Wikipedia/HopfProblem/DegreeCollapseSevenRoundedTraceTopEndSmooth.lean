import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceTopEnd

/-!
# The original smooth atlas on the actual top end

The original manifold maps smoothly into the global trace and lies in its
native boundary. Its atlas is transferred only to the newly defined top-end
subtype; no atlas on the original manifold is changed. The resulting end
inclusion and the exact restriction of the trace normal frame are checked.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem contMDiff_topLift : letI := unchangedCylinderChartedSpace A;
    ContMDiff (𝓡 7) (ProductHalfSpace.model (Vector 7)) ∞ (topLift A) := by
  let := unchangedCylinderChartedSpace A
  apply (contMDiff_unchangedCylinder_iff_parameters A _).mpr
  have he : (fun m ↦ (unchangedCylinderHomeomorph A (topLift A m)).val.val) =
      (fun m : M ↦ (m, UnroundedTrace.height A)) := funext (topLift_coordinates A)
  rw [he]
  exact contMDiff_id.prodMk contMDiff_const

theorem contMDiff_topMap : letI := traceChartedSpace A;
    ContMDiff (𝓡 7) (ProductHalfSpace.model (Vector 7)) ∞ (topMap A) := by
  let := traceChartedSpace A
  let := unchangedCylinderChartedSpace A
  have hi : ContMDiff (ProductHalfSpace.model (Vector 7))
      (ProductHalfSpace.model (Vector 7)) ∞ (Subtype.val : cylinderOnlyPart A → ambientSet A) :=
    (openCover A).contMDiff_inclusion .cylinder
  exact hi.comp (contMDiff_topLift A)

theorem topMap_isBoundaryPoint (m : M) : letI := traceChartedSpace A;
    (ProductHalfSpace.model (Vector 7)).IsBoundaryPoint (topMap A m) := by
  let := traceChartedSpace A
  let := unchangedCylinderChartedSpace A
  apply ((openCover A).isBoundaryPoint_inclusion_iff .cylinder (topLift A m)).mp
  apply (unchangedCylinder_isBoundaryPoint_iff A (topLift A m)).mpr
  exact Or.inr (congrArg Prod.snd (topLift_coordinates A m))

@[instance_reducible]
def topEndChartedSpace : ChartedSpace (Vector 7) (topEnd A) :=
  ModelAtlasTransport.atlas (topEndHomeomorph A).symm

theorem topEnd_isManifold : letI := topEndChartedSpace A;
    IsManifold (𝓡 7) ∞ (topEnd A) :=
  ModelAtlasTransport.isManifold (topEndHomeomorph A).symm (𝓡 7)

def topEndDiffeomorph : letI := topEndChartedSpace A; M ≃ₘ⟮𝓡 7, 𝓡 7⟯ topEnd A := by
  let := topEndChartedSpace A
  exact (ModelAtlasTransport.diffeomorph (topEndHomeomorph A).symm (𝓡 7)).symm

theorem contMDiff_topEndInclusion : letI := traceChartedSpace A;
    letI := topEndChartedSpace A;
    ContMDiff (𝓡 7) (ProductHalfSpace.model (Vector 7)) ∞
      (Subtype.val : topEnd A → ambientSet A) := by
  let := traceChartedSpace A
  let := topEndChartedSpace A
  have h := (contMDiff_topMap A).comp (topEndDiffeomorph A).symm.contMDiff_toFun
  intro p
  apply (h p).congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro q
  change q.val = topMap A ((topEndHomeomorph A).symm q)
  exact (congrArg Subtype.val ((topEndHomeomorph A).apply_symm_apply q)).symm

theorem traceNormalFrame_topMap (m : M) : traceNormalFrame A (topMap A m) =
    boundaryFrameOperator (a.orthonormal m).val := by
  calc
    traceNormalFrame A (topMap A m) = pieceNormalFrame A .cylinder (topLift A m) :=
      traceNormalFrame_on_piece A .cylinder (topLift A m)
    _ = boundaryFrameOperator (a.orthonormal m).val := by
      change boundaryFrameOperator
        (a.orthonormal (unchangedCylinderHomeomorph A (topLift A m)).val.val.1).val = _
      rw [topLift_coordinates]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
