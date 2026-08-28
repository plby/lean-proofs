import Wikipedia.HopfProblem.DegreeCollapseAttachmentHomotopy
import Wikipedia.HopfProblem.DegreeCollapseHandleDeformation

/-!
# An actual attached handle reduces to its core cell

The homotopy fixes the original lower subspace and the entire core cell.
This is a homotopy equivalence of the actual unions inside the original
ambient Hausdorff space, not a replacement of their topologies.
-/

noncomputable section

open Set Metric
open scoped unitInterval ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.CoreAttachment

variable {N P M : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

abbrev Core : Set (Handle.Space (N := N) (P := P)) := {z | (z.2 : P) = 0}
abbrev Face : Set (Handle.Space (N := N) (P := P)) := {z | ‖(z.1 : N)‖ = 1}

def faceDeformation :
    (ContinuousMap.id (Handle.Space (N := N) (P := P))).HomotopyRel Handle.retraction Face where
  __ := Handle.deformation.toHomotopy
  prop' t z hz := Handle.interpolate_fixed t z (Or.inl hz)

variable [FiniteDimensional ℝ N] [FiniteDimensional ℝ P]
  [TopologicalSpace M] [T2Space M]
  (A : Set M) [CompactSpace A] (h : C(Handle.Space (N := N) (P := P), M))
  (hinj : Function.Injective h) (hface : ∀ z, h z ∈ A ↔ z ∈ Face)

abbrev CoreUnion := ↥(A ∪ h '' Core)

def family : C(I × Attachment.Union A h, Attachment.Union A h) :=
  Attachment.unionFamily A Face h faceDeformation hinj hface

theorem family_zero (x : Attachment.Union A h) : family A h hinj hface (0, x) = x :=
  Attachment.unionFamily_zero A Face h faceDeformation hinj hface x

theorem family_fixed_lower (t : I) (a : A) :
    family A h hinj hface (t, ⟨a.val, Or.inl a.property⟩) = ⟨a.val, Or.inl a.property⟩ :=
  Attachment.unionFamily_fixed_lower A Face h faceDeformation hinj hface t a

theorem family_on_handle (t : I) (z : Handle.Space (N := N) (P := P)) :
    (family A h hinj hface (t, ⟨h z, Or.inr ⟨z, rfl⟩⟩)).val = h (Handle.interpolate t z) :=
  Attachment.unionFamily_on_handle A Face h faceDeformation hinj hface t z

theorem family_one_mem_coreUnion (x : Attachment.Union A h) :
    (family A h hinj hface (1, x)).val ∈ A ∪ h '' Core := by
  rcases x with ⟨x, hx | ⟨z, rfl⟩⟩
  · have he := family_fixed_lower A h hinj hface 1 ⟨x, hx⟩
    exact Or.inl (congrArg Subtype.val he ▸ hx)
  · rw [family_on_handle, Handle.interpolate_one]
    rcases Handle.retraction_mem_faceCore z with hz | hz
    · exact Or.inl ((hface (Handle.retraction z)).mpr hz)
    · exact Or.inr ⟨Handle.retraction z, hz, rfl⟩

def inclusion : C(CoreUnion A h, Attachment.Union A h) :=
  ⟨fun x => ⟨x.val, x.property.elim Or.inl
    (fun hx => Or.inr (by obtain ⟨z, _, hz⟩ := hx; exact ⟨z, hz⟩))⟩,
    continuous_subtype_val.subtype_mk _⟩

def reduce : C(Attachment.Union A h, CoreUnion A h) :=
  ⟨fun x => ⟨(family A h hinj hface (1, x)).val, family_one_mem_coreUnion A h hinj hface x⟩,
    ((continuous_subtype_val.comp (family A h hinj hface).continuous).comp
      (continuous_const.prodMk continuous_id)).subtype_mk _⟩

theorem family_fixed_coreUnion (t : I) (x : CoreUnion A h) :
    family A h hinj hface (t, inclusion A h x) = inclusion A h x := by
  rcases x with ⟨x, hx | ⟨z, hz, rfl⟩⟩
  · exact family_fixed_lower A h hinj hface t ⟨x, hx⟩
  · apply Subtype.ext
    change (family A h hinj hface (t, ⟨h z, Or.inr ⟨z, rfl⟩⟩)).val = h z
    rw [family_on_handle, Handle.interpolate_fixed t z (Or.inr hz)]

/-- The actual lower subspace together with the core is homotopy equivalent to the full union. -/
def coreUnionHomotopyEquiv : CoreUnion A h ≃ₕ Attachment.Union A h where
  toFun := inclusion A h
  invFun := reduce A h hinj hface
  left_inv := by
    have he : (reduce A h hinj hface).comp (inclusion A h) = ContinuousMap.id (CoreUnion A h) := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      change (family A h hinj hface (1, inclusion A h x)).val = x.val
      exact congrArg Subtype.val (family_fixed_coreUnion A h hinj hface 1 x)
    rw [he]
  right_inv := by
    let H : (ContinuousMap.id (Attachment.Union A h)).Homotopy
        ((inclusion A h).comp (reduce A h hinj hface)) := {
      toContinuousMap := family A h hinj hface
      map_zero_left := family_zero A h hinj hface
      map_one_left := fun _ => rfl }
    exact ⟨H.symm⟩

end Wikipedia.HopfProblem.DegreeCollapse.CoreAttachment
