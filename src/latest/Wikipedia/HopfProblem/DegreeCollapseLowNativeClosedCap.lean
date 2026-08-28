import Wikipedia.HopfProblem.DegreeCollapseLowClosedCapEmbedding
import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceHandleWindow

/-!

# A closed embedded replacement cap in the actual native complementary end

The inner disk lies in the unchanged handle window and on its transverse
sphere. The outer annulus lies on the rounded collar's zero level. Both
therefore lie in the actual native boundary and in its complementary end.
The ambient cap map lifts continuously and remains closed embedded there.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair

open NoExoticSixSphere GLOrthonormalization Stiefel RoundedTrace
open Wikipedia.SmoothSixDPoincare.PuncturedHandle

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)

omit [IsManifold (𝓡 7) ∞ M] in
theorem cutRadius_lt_handleCoreRadius : cutRadius A < handleCoreRadius A := by
  nlinarith [cutRadius_sq A, handleCoreRadius_sq A, cutRadius_pos A,
    handleCoreRadius_pos A, (bump A).rOut_pos]

theorem exists_native_innerCap (hR : A.radius = 2) (p : CapDomain d)
    (hp : ‖capDisk A p‖ ≤ cutRadius A) :
    ∃ y : otherBoundaryPart A, y.val.val.val = capInner A p := by
  let := traceChartedSpace A
  have hw : p.2.val ∈ closedBall (0 : Vector (7 - d)) (UnroundedTrace.handleRadius A) := by
    rw [handleRadius_eq_one A hR]
    exact sphere_subset_closedBall p.2.property
  let z : HandleSuperlevel A := ⟨(capDisk A p, p.2.val),
    (LowHandleSuperlevel.nonneg_iff (UnroundedTrace.handleRadius_pos A) _).mpr hw⟩
  have hz : z ∈ unchangedHandleWindow A := by
    apply (mem_unchangedHandleWindow_iff A z).mpr
    rw [mem_ball, dist_zero_right]
    exact hp.trans_lt (cutRadius_lt_handleCoreRadius A)
  let v : unchangedHandleWindow A := ⟨z, hz⟩
  let q : handleOnlyPart A := (unchangedHandleHomeomorph A).symm v
  have hc : (unchangedHandleHomeomorph A q).val.val = (capDisk A p, p.2.val) :=
    congrArg (fun v : unchangedHandleWindow A ↦ v.val.val)
      ((unchangedHandleHomeomorph A).apply_symm_apply v)
  have hb : q.val ∈ traceBoundarySet A := by
    refine mem_iUnion.mpr ⟨.handle, q, ?_, rfl⟩
    change (unchangedHandleHomeomorph A q).val.val.2 ∈
      sphere (0 : Vector (7 - d)) (UnroundedTrace.handleRadius A)
    rw [hc, handleRadius_eq_one A hR]
    exact p.2.property
  let b : Boundary A := ⟨q.val, (trace_isBoundaryPoint_iff A q.val).mpr hb⟩
  let bpiece : boundaryPieceDomain A .handle := ⟨b, q.property⟩
  refine ⟨⟨b, handleBoundary_mem_other A bpiece⟩, ?_⟩
  have he := unchangedHandleHomeomorph_ambient A q
  rw [hc] at he
  exact he.symm

theorem exists_native_outerCap (hR : A.radius = 2) (p : CapDomain d)
    (hp : cutRadius A ≤ ‖capDisk A p‖) :
    ∃ y : otherBoundaryPart A, y.val.val.val = capOuter A p := by
  let := traceChartedSpace A
  let c : collarParameters A := ⟨capCollar A p, capCollar_mem A hR p hp⟩
  let q : collarPart A := collarHomeomorph A c
  have hc : ((collarHomeomorph A).symm q).val = capCollar A p :=
    congrArg Subtype.val ((collarHomeomorph A).symm_apply_apply c)
  have hb : q.val ∈ traceBoundarySet A := by
    refine mem_iUnion.mpr ⟨.collar, q, ?_, rfl⟩
    change LowRoundedHandleCorner.collarLevel (bump A) (UnroundedTrace.handleRadius A)
      ((collarHomeomorph A).symm q).val = 0
    rw [hc]
    change GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A)
      (LowRoundedZeroPoint.point (bump A) 1 (p.2, capParameter A p)) = 0
    rw [handleRadius_eq_one A hR, LowRoundedZeroPoint.level_point]
  let b : Boundary A := ⟨q.val, (trace_isBoundaryPoint_iff A q.val).mpr hb⟩
  let bpiece : boundaryPieceDomain A .collar := ⟨b, q.property⟩
  exact ⟨⟨b, collarBoundary_mem_other A bpiece⟩, collarHomeomorph_ambient A c⟩

theorem exists_nativeCapPoint (hR : A.radius = 2) (p : CapDomain d) :
    ∃ y : otherBoundaryPart A, y.val.val.val = capPoint A p := by
  by_cases hp : ‖capDisk A p‖ ≤ cutRadius A
  · rw [capPoint_of_inner A p hp]
    exact exists_native_innerCap A hR p hp
  · rw [capPoint_of_outer A hR p (lt_of_not_ge hp).le]
    exact exists_native_outerCap A hR p (lt_of_not_ge hp).le

def nativeCapPoint (hR : A.radius = 2) (p : CapDomain d) : otherBoundaryPart A :=
  (exists_nativeCapPoint A hR p).choose

theorem nativeCapPoint_ambient (hR : A.radius = 2) (p : CapDomain d) :
    (nativeCapPoint A hR p).val.val.val = capPoint A p :=
  (exists_nativeCapPoint A hR p).choose_spec

theorem continuous_nativeCapPoint (hR : A.radius = 2) : Continuous (nativeCapPoint A hR) := by
  have hi : IsEmbedding (fun y : otherBoundaryPart A ↦ y.val.val.val) :=
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).comp IsEmbedding.subtypeVal
  apply hi.continuous_iff.mpr
  change Continuous (fun p ↦ (nativeCapPoint A hR p).val.val.val)
  simpa only [nativeCapPoint_ambient] using continuous_capPoint A hR

theorem nativeCapPoint_injective (hR : A.radius = 2) : Injective (nativeCapPoint A hR) := by
  intro p q h
  apply capPoint_injective A hR
  simpa only [nativeCapPoint_ambient] using
    congrArg (fun y : otherBoundaryPart A ↦ y.val.val.val) h

theorem isClosedEmbedding_nativeCapPoint (hR : A.radius = 2) :
    IsClosedEmbedding (nativeCapPoint A hR) := by
  let := compactSpace_capDomain d
  exact (continuous_nativeCapPoint A hR).isClosedEmbedding (nativeCapPoint_injective A hR)

theorem nativeCapPoint_newBoundary (hR : A.radius = 2) (s : NoExoticSixSphere.Sphere d)
    (w : sphere (0 : Vector (7 - d)) 1) :
    (nativeCapPoint A hR (newBoundary (s, w))).val.val.val =
      (LowHeightCylinder.heightCylinder d e) (A.tube (s, oldRadius A • w.val), 0) := by
  rw [nativeCapPoint_ambient, capPoint_newBoundary A hR]

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair
