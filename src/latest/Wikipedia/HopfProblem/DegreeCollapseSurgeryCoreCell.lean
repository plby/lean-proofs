import Wikipedia.HopfProblem.DegreeCollapseRoundedTraceHomotopyType
import Wikipedia.HopfProblem.DegreeCollapseHandleCoreAttachment
import Wikipedia.SmoothSixDPoincare.ClosedAttachment

/-!
# The actual surgery trace is one genuine core-cell attachment

Normalize the retained handle radius, identify its full source and exact
attaching face, and apply the already constructed relative handle
deformation. It fixes the entire original cylinder and the core disk.
Composing with the explicit rounding deformation gives a homotopy
equivalence from the actual closed four-cell attachment to the native trace.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceCoreAttachment

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open Wikipedia.SmoothSixDPoincare

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

include hR in
theorem handleRadius_eq_one : UnroundedTrace.handleRadius A = 1 := by
  rw [UnroundedTrace.handleRadius, hR]
  norm_num

def unitHandleCoordinates : Handle.Space (N := Vector 4) (P := Vector 3) ≃ₜ
    UnroundedTrace.Handle A :=
  (Homeomorph.refl (closedBall (0 : Vector 4) 1)).prodCongr
    (Homeomorph.setCongr (by rw [handleRadius_eq_one A hR]))

def unitHandleMap : C(Handle.Space (N := Vector 4) (P := Vector 3),
    Vector (e.ambientDimension + 6)) :=
  (UnroundedTrace.handleMap A).comp
    ⟨unitHandleCoordinates A hR, (unitHandleCoordinates A hR).continuous⟩

theorem unitHandleMap_apply (z : Handle.Space (N := Vector 4) (P := Vector 3)) :
    unitHandleMap A hR z = A.map (z.1.val, z.2.val) := rfl

theorem injective_unitHandleMap : Injective (unitHandleMap A hR) :=
  (UnroundedTrace.closedEmbedding_handle A).injective.comp (unitHandleCoordinates A hR).injective

theorem range_unitHandleMap : range (unitHandleMap A hR) = range (UnroundedTrace.handleMap A) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨unitHandleCoordinates A hR p, rfl⟩
  · rintro ⟨p, rfl⟩
    refine ⟨(unitHandleCoordinates A hR).symm p, ?_⟩
    change UnroundedTrace.handleMap A
      (unitHandleCoordinates A hR ((unitHandleCoordinates A hR).symm p)) = _
    rw [Homeomorph.apply_symm_apply]

theorem unitHandleMap_in_cylinder_iff (z : Handle.Space (N := Vector 4) (P := Vector 3)) :
    unitHandleMap A hR z ∈ range (UnroundedTrace.cylinderMap A) ↔ ‖z.1.val‖ = 1 := by
  have h := UnroundedTrace.handle_mem_cylinder_iff A (unitHandleCoordinates A hR z)
  simp only [UnroundedTrace.attachingFace, mem_ofPred_eq, mem_sphere, dist_zero_right] at h
  have hfirst : (unitHandleCoordinates A hR z).1 = z.1 := rfl
  rw [hfirst] at h
  exact h

def coreCellMap : C(closedBall (0 : Vector 4) 1, Vector (e.ambientDimension + 6)) :=
  ⟨fun x ↦ A.disk.toFun x.val, A.disk.smooth.continuous.comp continuous_subtype_val⟩

theorem injective_coreCellMap : Injective (coreCellMap A) := A.disk.embedded.injective

include hR in
theorem coreCellMap_in_cylinder_iff (u : closedBall (0 : Vector 4) 1) :
    coreCellMap A u ∈ range (UnroundedTrace.cylinderMap A) ↔ ‖u.val‖ = 1 := by
  have h := unitHandleMap_in_cylinder_iff A hR (u, ⟨0, mem_closedBall_self (by norm_num)⟩)
  rw [unitHandleMap_apply, A.map_core] at h
  exact h

theorem image_handle_core : unitHandleMap A hR '' CoreAttachment.Core = range (coreCellMap A) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.1, ?_⟩
    change A.disk.toFun z.1.val = A.map (z.1.val, z.2.val)
    rw [show z.2.val = 0 from hz, A.map_core]
  · rintro ⟨u, rfl⟩
    exact ⟨(u, ⟨0, mem_closedBall_self (by norm_num)⟩), rfl, A.map_core u.val⟩

abbrev CoreCellSpace := ClosedAttachment.Space (range (UnroundedTrace.cylinderMap A))
  {u : closedBall (0 : Vector 4) 1 | ‖u.val‖ = 1} (coreCellMap A)

def coreUnionTraceHomotopyEquiv :
    ↥(range (UnroundedTrace.cylinderMap A) ∪ range (coreCellMap A)) ≃ₕ ambientSet A := by
  let U := range (UnroundedTrace.cylinderMap A)
  have hU : IsCompact U := isCompact_range (UnroundedTrace.cylinderMap A).continuous
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let core := CoreAttachment.coreUnionHomotopyEquiv U (unitHandleMap A hR)
    (injective_unitHandleMap A hR) (unitHandleMap_in_cylinder_iff A hR)
  let mark := Homeomorph.setCongr
    (congrArg (fun S : Set (Vector (e.ambientDimension + 6)) ↦ U ∪ S) (image_handle_core A hR))
  let full : Attachment.Union U (unitHandleMap A hR) ≃ₜ UnroundedTrace.ambientSet A :=
    Homeomorph.setCongr (by rw [range_unitHandleMap]; rfl)
  exact mark.symm.toHomotopyEquiv.trans
    (core.trans (full.toHomotopyEquiv.trans (TraceRetraction.unroundedHomotopyEquiv A)))

theorem coreUnionTraceHomotopyEquiv_ambient
    (x : ↥(range (UnroundedTrace.cylinderMap A) ∪ range (coreCellMap A))) :
    (coreUnionTraceHomotopyEquiv A hR x).val = x.val := rfl

def coreCellTraceHomotopyEquiv : CoreCellSpace A ≃ₕ ambientSet A := by
  let U := range (UnroundedTrace.cylinderMap A)
  have hU : IsCompact U := isCompact_range (UnroundedTrace.cylinderMap A).continuous
  let cell := ClosedAttachment.unionHomeomorph U _ (coreCellMap A) hU
    (injective_coreCellMap A) (coreCellMap_in_cylinder_iff A hR)
  exact cell.toHomotopyEquiv.trans (coreUnionTraceHomotopyEquiv A hR)

end Wikipedia.HopfProblem.DegreeCollapse.TraceCoreAttachment
