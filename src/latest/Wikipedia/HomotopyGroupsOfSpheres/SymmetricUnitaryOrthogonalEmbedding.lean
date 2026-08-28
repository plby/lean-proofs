import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryOrthogonalSmoothness
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCompactness

/-! # The constrained matrix space is homeomorphic to its real orthogonal image -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealRepresentation

open QuaternionicSymmetricMatrices NoExoticSixSphere.GLOrthonormalization

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem specialOrthogonal_injective : Function.Injective (specialOrthogonal (N := N)) := by
  intro B C h
  apply Subtype.ext
  apply Subtype.ext
  exact orthogonal_injective h

theorem continuous_specialOrthogonal : Continuous (specialOrthogonal (N := N)) :=
  continuous_orthogonal.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem isClosedEmbedding_specialOrthogonal :
    Topology.IsClosedEmbedding (specialOrthogonal (N := N)) :=
  continuous_specialOrthogonal.isClosedEmbedding specialOrthogonal_injective

def specialOrthogonalRangeHomeomorph :
    SpecialSpace N ≃ₜ Set.range (specialOrthogonal (N := N)) :=
  isClosedEmbedding_specialOrthogonal.isEmbedding.toHomeomorph

theorem continuous_of_specialOrthogonal {Y : Type*} [TopologicalSpace Y]
    {f : Y → SpecialSpace N} (hf : Continuous (fun y ↦ specialOrthogonal (f y))) :
    Continuous f :=
  isClosedEmbedding_specialOrthogonal.isEmbedding.isInducing.continuous_iff.mpr hf

def orthogonalFamily {Y : Type*} [TopologicalSpace Y] (F : C(Y, SpecialSpace N)) :
    C(Y, OrthogonalOperators (2 * Fintype.card N)) :=
  ⟨fun y ↦ specialOrthogonal (F y), continuous_specialOrthogonal.comp F.continuous⟩

def liftOrthogonalFamily {Y : Type*} [TopologicalSpace Y]
    (F : C(Y, OrthogonalOperators (2 * Fintype.card N)))
    (hF : ∀ y, F y ∈ Set.range (specialOrthogonal (N := N))) : C(Y, SpecialSpace N) :=
  ⟨fun y ↦ specialOrthogonalRangeHomeomorph.symm ⟨F y, hF y⟩,
    specialOrthogonalRangeHomeomorph.symm.continuous.comp (F.continuous.subtype_mk hF)⟩

theorem specialOrthogonal_liftOrthogonalFamily {Y : Type*} [TopologicalSpace Y]
    (F : C(Y, OrthogonalOperators (2 * Fintype.card N)))
    (hF : ∀ y, F y ∈ Set.range (specialOrthogonal (N := N))) (y : Y) :
    specialOrthogonal (liftOrthogonalFamily F hF y) = F y :=
  congrArg Subtype.val (specialOrthogonalRangeHomeomorph.apply_symm_apply ⟨F y, hF y⟩)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealRepresentation
