import Wikipedia.SmoothSixDPoincare.HandleAttachmentDeformation
import Wikipedia.SmoothSixDPoincare.CellCoverHomotopy

/-!
# Core-cell data for any actual closed embedded handle attachment

Use the original old-space and whole-handle embeddings, their exhaustive
cover, and their exact attaching-face intersection. The previously proved
relative deformation supplies the homotopy equivalence to the whole body.
The old-space coordinates and core attaching map commute with the original
embeddings, without reference to a Morse function.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.HandleCoreAttachment

open MorseHandle

variable {N P R X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [FiniteDimensional ℝ N] [NormedAddCommGroup P]
  [TopologicalSpace R] [TopologicalSpace X] [T2Space X]
  (r : R → X) (h : C(UnitDisk N × UnitDisk P, X))
  (hr : IsClosedEmbedding r) (hh : IsClosedEmbedding h)
  (hcover : range r ∪ range h = univ)
  (hface : ∀ z, h z ∈ range r ↔ ‖(z.1 : N)‖ = 1)

include hh in
theorem core_isClosedEmbedding : IsClosedEmbedding (core h) := by
  apply (core h).continuous.isClosedEmbedding
  intro x y hxy
  exact congrArg Prod.fst (hh.injective hxy)

def cellPresentation : EmbeddedCellAttachment N (coreSpace r h) :=
  .ofUnion (range r) (core h) hr.isClosed_range (core_isClosedEmbedding h hh)
    (fun z => hface (z, ⟨0, by simp⟩))

def cellOldHomeomorph : R ≃ₜ (cellPresentation r h hr hh hface).old where
  toFun a := ⟨⟨r a, Or.inl (mem_range_self a)⟩, mem_range_self a⟩
  invFun a := hr.toHomeomorph.symm ⟨a.val.val, a.property⟩
  left_inv a := hr.toHomeomorph.symm_apply_apply a
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    change r (hr.toHomeomorph.symm ⟨a.val.val, a.property⟩) = a.val.val
    exact congrArg (fun z : range r => (z : X))
      (hr.toHomeomorph.apply_symm_apply ⟨a.val.val, a.property⟩)
  continuous_toFun := (hr.continuous.subtype_mk _).subtype_mk _
  continuous_invFun := hr.toHomeomorph.symm.continuous.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

theorem cellOldHomeomorph_point (a : R) :
    ((cellOldHomeomorph r h hr hh hface a).val : X) = r a := rfl

def coreBoundaryMap : C(PuncturedHandle.UnitSphere N, R) :=
  (cellOldHomeomorph r h hr hh hface).symm.toHomotopyEquiv.toFun.comp
    (cellPresentation r h hr hh hface).attachingSphere

theorem cell_attaching_eq : (cellPresentation r h hr hh hface).attachingSphere =
    (cellOldHomeomorph r h hr hh hface).toHomotopyEquiv.toFun.comp
      (coreBoundaryMap r h hr hh hface) := by
  apply ContinuousMap.ext
  intro u
  exact ((cellOldHomeomorph r h hr hh hface).apply_symm_apply _).symm

theorem coreBoundaryMap_point (u : PuncturedHandle.UnitSphere N) :
    r (coreBoundaryMap r h hr hh hface u) =
      core h ⟨u.val, sphere_subset_closedBall u.property⟩ :=
  congrArg (fun a : (cellPresentation r h hr hh hface).old => (a.val : X))
    ((cellOldHomeomorph r h hr hh hface).apply_symm_apply
      ((cellPresentation r h hr hh hface).attachingSphere u))

variable [NormedSpace ℝ P]

theorem cell_old_realization : (homotopyEquiv r h hr hh hcover hface).toFun.comp
    ((⟨Subtype.val, continuous_subtype_val⟩ :
      C((cellPresentation r h hr hh hface).old, coreSpace r h)).comp
        (cellOldHomeomorph r h hr hh hface).toHomotopyEquiv.toFun) =
      (⟨r, hr.continuous⟩ : C(R, X)) := rfl

end Wikipedia.SmoothSixDPoincare.HandleCoreAttachment
