import Wikipedia.HopfProblem.DegreeCollapseSurgeryFlatCollarFormula
import Wikipedia.HopfProblem.DegreeCollapseSurgeryCollarRetraction
import Wikipedia.NoExoticSixSphere.UnitSurgeryTraceBoundary

/-!
# The native rounded surgery end has the checked flat-end homology map

Use the actual native boundary identification to define the end inclusion.
The rounding deformation carries it exactly to the flat representative:
the exterior and handle are fixed, and the full collar formulas agree.
Consequently these actual maps are homotopic and induce the same homology
maps. In particular the native surgery end injects into the trace on H3.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceBody

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open SingularMayerVietoris PeriodTorusHigherHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def nativeTargetInclusion : C(UnitSurgery.Target A hR, ambientSet A) := by
  let := boundaryChartedSpace A
  let := UnitSurgery.targetChartedSpace A hR
  have hd : Continuous (UnitSurgery.comparisonEquiv A hR).symm :=
    (UnitSurgery.contMDiff_comparisonEquiv_symm A hR).continuous
  exact ⟨fun p ↦ ((UnitSurgery.comparisonEquiv A hR).symm p).val.val,
    (continuous_subtype_val.comp continuous_subtype_val).comp hd⟩

theorem nativeTargetInclusion_boundary (p : UnitSurgery.Target A hR) :
    letI := boundaryChartedSpace A; letI := UnitSurgery.targetChartedSpace A hR;
    (nativeTargetInclusion A hR p).val =
      (UnitSurgery.traceBoundaryDiffeomorph A hR (Sum.inr p)).val.val := rfl

theorem nativeTarget_exterior (m : retainedExterior A) :
    nativeTargetInclusion A hR (UnitSurgery.exteriorMap A hR m) =
      (UnitSurgery.exteriorEndPoint A m).val.val := by
  change ((UnitSurgery.comparisonEquiv A hR).symm (UnitSurgery.exteriorMap A hR m)).val.val = _
  rw [UnitSurgery.comparisonEquiv_symm_exterior]

theorem nativeTarget_handle (p : boundaryHandleParameters A) :
    nativeTargetInclusion A hR (UnitSurgery.handleMap A hR p) =
      (UnitSurgery.handleEndPoint A p).val.val := by
  change ((UnitSurgery.comparisonEquiv A hR).symm (UnitSurgery.handleMap A hR p)).val.val = _
  rw [UnitSurgery.comparisonEquiv_symm_handle]

theorem nativeTarget_collar (p : boundaryCollarParameters A) :
    nativeTargetInclusion A hR (UnitSurgery.collarMap A hR p) =
      (UnitSurgery.collarEndPoint A p).val.val := by
  change ((UnitSurgery.comparisonEquiv A hR).symm (UnitSurgery.collarMap A hR p)).val.val = _
  rw [UnitSurgery.comparisonEquiv_symm_collar]

theorem round_retraction_ambient_of_unrounded (x : ambientSet A)
    (hx : x.val ∈ UnroundedTrace.ambientSet A) :
    (TraceRetraction.retraction A x).val = x.val :=
  congrArg (fun z : ambientSet A ↦ z.val) (TraceRetraction.deformation_fixed A 1 ⟨x.val, hx⟩)

theorem retracted_nativeTarget (p : UnitSurgery.Target A hR) :
    TraceRetraction.oldInclusion A (TraceRetraction.retraction A (nativeTargetInclusion A hR p)) =
      flatTargetInclusion A hR p := by
  rcases UnitSurgery.target_cover A hR p with (⟨m, rfl⟩ | ⟨q, rfl⟩) | ⟨q, rfl⟩
  · rw [nativeTarget_exterior]
    apply Subtype.ext
    have hp : (UnitSurgery.exteriorEndPoint A m).val.val.val = e.heightCylinder (m.val, 0) := rfl
    have hx : (UnitSurgery.exteriorEndPoint A m).val.val.val ∈ UnroundedTrace.ambientSet A := by
      rw [hp]
      exact Or.inl ⟨(m.val, ⟨0, le_rfl, (UnroundedTrace.height_pos A).le⟩), rfl⟩
    exact (round_retraction_ambient_of_unrounded A _ hx).trans
      (hp.trans (flatTarget_exterior A hR m).symm)
  · rw [nativeTarget_handle]
    apply Subtype.ext
    have hp : (UnitSurgery.handleEndPoint A q).val.val.val = A.map (q.val.1, q.val.2.val) := by
      let := boundaryPieceAtlas A .handle
      have h := boundaryHandleDiffeomorph_ambient A q
      rw [TraceCoreAttachment.handleRadius_eq_one A hR, one_smul] at h
      exact h
    have hx : (UnitSurgery.handleEndPoint A q).val.val.val ∈ UnroundedTrace.ambientSet A := by
      rw [hp]
      have hq : q.val.1 ∈ closedBall (0 : Vector 4) 1 :=
        ball_subset_closedBall ((ball_subset_ball (handleCoreRadius_lt_one A).le)
          ((mem_boundaryHandleParameters_iff A q.val).mp q.property))
      have hv : q.val.2.val ∈ closedBall (0 : Vector 3) (UnroundedTrace.handleRadius A) := by
        rw [TraceCoreAttachment.handleRadius_eq_one A hR]
        exact sphere_subset_closedBall q.val.2.property
      exact Or.inr ⟨(⟨q.val.1, hq⟩, ⟨q.val.2.val, hv⟩), rfl⟩
    exact (round_retraction_ambient_of_unrounded A _ hx).trans
      (hp.trans (flatTarget_handle A hR q).symm)
  · rw [nativeTarget_collar]
    apply Subtype.ext
    exact (TraceRetraction.retraction_collarEndPoint A q).trans (flatTarget_collar A hR q).symm

theorem retracted_nativeTarget_map :
    ((TraceRetraction.oldInclusion A).comp (TraceRetraction.retraction A)).comp
      (nativeTargetInclusion A hR) = flatTargetInclusion A hR := by
  apply ContinuousMap.ext
  exact retracted_nativeTarget A hR

theorem nativeTarget_homotopic_flat :
    (nativeTargetInclusion A hR).Homotopic (flatTargetInclusion A hR) := by
  have H : (ContinuousMap.id (ambientSet A)).Homotopic
      ((TraceRetraction.oldInclusion A).comp (TraceRetraction.retraction A)) :=
    ⟨TraceRetraction.deformationHomotopy A⟩
  have h := H.comp (ContinuousMap.Homotopic.refl (nativeTargetInclusion A hR))
  change (nativeTargetInclusion A hR).Homotopic
    (((TraceRetraction.oldInclusion A).comp (TraceRetraction.retraction A)).comp
      (nativeTargetInclusion A hR)) at h
  rwa [retracted_nativeTarget_map] at h

theorem nativeTarget_homology_eq_flat (n : ℕ) :
    singularHomologyMap (nativeTargetInclusion A hR) n =
      singularHomologyMap (flatTargetInclusion A hR) n :=
  homotopic_homologyMap (nativeTarget_homotopic_flat A hR) n

theorem nativeTarget_homology_injective_three :
    Injective (singularHomologyMap (nativeTargetInclusion A hR) 3) := by
  rw [nativeTarget_homology_eq_flat]
  exact flatTarget_homology_injective_three A hR

end Wikipedia.HopfProblem.DegreeCollapse.TraceBody
