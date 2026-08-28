import Wikipedia.SmoothSixDPoincare.HandleAttachmentDeformation
import Wikipedia.SmoothSixDPoincare.CellOldNeighborhoodRetraction

/-!
# An embedded whole handle with its specified attaching sphere

The actual old-space map, handle, and attaching map determine a core-cell
presentation. Its homotopy equivalence into the full attachment is the
literal inclusion and fixes the old space. These data will be constructed
for both ends of the same surgery-pair quotient.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse

open Wikipedia.SmoothSixDPoincare PuncturedHandle MorseHandle

structure EmbeddedHandle (N P R X : Type)
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace R] [TopologicalSpace X] where
  oldMap : C(R, X)
  handle : C(UnitDisk N × UnitDisk P, X)
  old_closed : IsClosedEmbedding oldMap
  handle_closed : IsClosedEmbedding handle
  cover : range oldMap ∪ range handle = univ
  face : ∀ z, handle z ∈ range oldMap ↔ ‖z.1.val‖ = 1
  attaching : C(UnitSphere N, R)
  boundary : ∀ s, handle (⟨s.val, sphere_subset_closedBall s.property⟩, ⟨0, by simp⟩) =
    oldMap (attaching s)

namespace EmbeddedHandle

variable {N P R X : Type}
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace R] [TopologicalSpace X] [T2Space X]
  (D : EmbeddedHandle N P R X)

def core : C(UnitDisk N, X) := HandleCoreAttachment.core D.handle

theorem core_closed : IsClosedEmbedding D.core := by
  apply D.core.continuous.isClosedEmbedding
  intro x y h
  exact congrArg Prod.fst (D.handle_closed.injective h)

theorem core_mem_old (z : UnitDisk N) : D.core z ∈ range D.oldMap ↔ ‖z.val‖ = 1 :=
  D.face (z, ⟨0, by simp⟩)

def corePresentation : EmbeddedCellAttachment N ↥(range D.oldMap ∪ range D.core) :=
  EmbeddedCellAttachment.ofUnion (range D.oldMap) D.core
    D.old_closed.isClosed_range D.core_closed D.core_mem_old

def rangeOldHomeomorph : range D.oldMap ≃ₜ D.corePresentation.old where
  toFun x := ⟨⟨x.val, Or.inl x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def oldHomeomorph : R ≃ₜ D.corePresentation.old :=
  D.old_closed.isEmbedding.toHomeomorph.trans D.rangeOldHomeomorph

def coreHomotopyEquiv : ↥(range D.oldMap ∪ range D.core) ≃ₕ X :=
  HandleCoreAttachment.homotopyEquiv D.oldMap D.handle D.old_closed D.handle_closed D.cover D.face

theorem coreHomotopyEquiv_apply (x : ↥(range D.oldMap ∪ range D.core)) :
    D.coreHomotopyEquiv x = x.val := rfl

theorem presentation_attaching : D.corePresentation.attachingSphere =
    D.oldHomeomorph.toHomotopyEquiv.toFun.comp D.attaching := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  apply Subtype.ext
  exact D.boundary s

end EmbeddedHandle
end Wikipedia.HopfProblem.DegreeCollapse
