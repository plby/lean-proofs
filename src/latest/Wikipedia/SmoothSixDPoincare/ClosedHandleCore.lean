import Wikipedia.SmoothSixDPoincare.HandleAttachmentDeformation
import Wikipedia.SmoothSixDPoincare.SurgeryComplementPieces
import Wikipedia.SmoothSixDPoincare.ClosedAttachment

/-!
# An embedded handle attachment has the homotopy type of its core-cell attachment

The core and all spaces are genuine subsets of the original ambient space.
The equivalence from the core union to the full handle union is its actual
inclusion, obtained from the constructed relative deformation.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ClosedHandleCore

open MorseHandle

variable {N P X : Type*} [NormedAddCommGroup N]
  [NormedAddCommGroup P] [TopologicalSpace X]
  (A : Set X) (h : C(UnitDisk N × UnitDisk P, X))

def oldInclusion : C(A, ↥(A ∪ range h)) :=
  ⟨Set.inclusion (fun _ hx => Or.inl hx), continuous_inclusion _⟩

def handleInclusion : C(UnitDisk N × UnitDisk P, ↥(A ∪ range h)) :=
  ⟨fun z => ⟨h z, Or.inr (mem_range_self z)⟩, h.continuous.subtype_mk _⟩

theorem old_closed (hA : IsClosed A) : IsClosedEmbedding (oldInclusion A h) :=
  ClosedCover.isClosedEmbedding_codRestrict hA.isClosedEmbedding_subtypeVal
    (fun x => Or.inl x.property)

theorem handle_closed (hh : IsClosedEmbedding h) : IsClosedEmbedding (handleInclusion A h) :=
  ClosedCover.isClosedEmbedding_codRestrict hh (fun z => Or.inr (mem_range_self z))

theorem pieces_cover : range (oldInclusion A h) ∪ range (handleInclusion A h) = univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨x, hx | ⟨z, rfl⟩⟩
  · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inr ⟨z, rfl⟩

theorem handle_mem_old_iff (z : UnitDisk N × UnitDisk P) :
    handleInclusion A h z ∈ range (oldInclusion A h) ↔ h z ∈ A := by
  constructor
  · rintro ⟨a, ha⟩
    have heq : (a : X) = h z := congrArg Subtype.val ha
    exact heq ▸ a.property
  · intro hz
    exact ⟨⟨h z, hz⟩, rfl⟩

theorem core_subset : A ∪ range (HandleCoreAttachment.core h) ⊆ A ∪ range h := by
  rintro x (hx | ⟨z, rfl⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨(z, ⟨0, by simp⟩), rfl⟩

theorem coreSpace_iff (x : ↥(A ∪ range h)) :
    x ∈ HandleCoreAttachment.coreSpace (oldInclusion A h) (handleInclusion A h) ↔
      x.val ∈ A ∪ range (HandleCoreAttachment.core h) := by
  constructor
  · rintro (⟨a, ha⟩ | ⟨z, hz⟩)
    · left
      have heq : (a : X) = x.val := congrArg Subtype.val ha
      exact heq ▸ a.property
    · right
      exact ⟨z, congrArg Subtype.val hz⟩
  · rintro (hx | ⟨z, hz⟩)
    · exact Or.inl ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    · exact Or.inr ⟨z, Subtype.ext hz⟩

/-- Remove only the nested subtype introduced by the actual closed cover. -/
def coreUnionHomeomorph : ↥(A ∪ range (HandleCoreAttachment.core h)) ≃ₜ
    HandleCoreAttachment.coreSpace (oldInclusion A h) (handleInclusion A h) where
  toFun x := ⟨⟨x.val, core_subset A h x.property⟩,
    (coreSpace_iff A h _).mpr x.property⟩
  invFun x := ⟨x.val.val, (coreSpace_iff A h x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

variable [NormedSpace ℝ N] [NormedSpace ℝ P]
  (hA : IsClosed A) (hh : IsClosedEmbedding h)
  (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1)

/-- The core union includes into the full handle union by a constructed homotopy equivalence. -/
def unionHomotopyEquiv :
    ↥(A ∪ range (HandleCoreAttachment.core h)) ≃ₕ ↥(A ∪ range h) :=
  (coreUnionHomeomorph A h).toHomotopyEquiv.trans
    (HandleCoreAttachment.homotopyEquiv (oldInclusion A h) (handleInclusion A h)
      (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
      (fun z => (handle_mem_old_iff A h z).trans (hface z)))

theorem unionHomotopyEquiv_apply (x : ↥(A ∪ range (HandleCoreAttachment.core h))) :
    (unionHomotopyEquiv A h hA hh hface x : X) = x.val := rfl

variable [T2Space X] [CompactSpace (UnitDisk N)]

/-- The genuine core union is the cell-attachment quotient along the original core boundary. -/
def coreQuotientHomeomorph (hcompact : IsCompact A) :
    ClosedAttachment.Space A {z : UnitDisk N | ‖(z : N)‖ = 1} (HandleCoreAttachment.core h) ≃ₜ
      ↥(A ∪ range (HandleCoreAttachment.core h)) := by
  apply ClosedAttachment.unionHomeomorph _ _ _ hcompact
  · intro x y hxy
    have heq := hh.injective hxy
    exact congrArg Prod.fst heq
  · intro z
    exact hface (z, ⟨0, by simp⟩)

end Wikipedia.SmoothSixDPoincare.ClosedHandleCore
