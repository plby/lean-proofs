import Wikipedia.SmoothSixDPoincare.ZeroIndexOpenComponents
import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryReverse

/-! # The retained boundary of a top-index surgery is an open complement -/

noncomputable section

open Set Function Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

open PuncturedHandle

variable {E F R X Y : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y] [Subsingleton F]
  (d : SurgeryBoundaryPair E F R X Y)

theorem topIndex_oldPiece_range : range d.oldPiece = range d.attachingSphere := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, congrArg d.oldPiece (Prod.ext rfl (Subsingleton.elim _ _))⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(u, ballZero), rfl⟩

theorem topIndex_attaching_isOpen : IsOpen (range d.attachingSphere) :=
  d.reverse.bornOpen.isOpen

theorem topIndex_oldOpenExterior : (d.oldOpenExterior : Set X) =
    (range d.attachingSphere)ᶜ := by
  change (range d.oldPiece)ᶜ = _
  rw [d.topIndex_oldPiece_range]

theorem topIndex_mem_newOpenExterior (y : Y) : y ∈ d.newOpenExterior := by
  rintro ⟨p, _⟩
  exact isEmptyElim p.2

theorem topIndex_newOpenExterior : (d.newOpenExterior : Set Y) = univ :=
  eq_univ_of_forall d.topIndex_mem_newOpenExterior

def topIndexNewCoordinates : Y ≃ₜ d.newOpenExterior where
  toFun y := ⟨y, d.topIndex_mem_newOpenExterior y⟩
  invFun := Subtype.val
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

theorem topIndexNewCoordinates_coe (y : Y) : (d.topIndexNewCoordinates y).val = y := rfl

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H}

def topIndexNewDiffeomorph [ChartedSpace H Y] : Diffeomorph J J Y d.newOpenExterior ∞ where
  toEquiv := d.topIndexNewCoordinates.toEquiv
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff d.newOpenExterior _).mp contMDiff_id
  contMDiff_invFun := contMDiff_subtype_val

end Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
