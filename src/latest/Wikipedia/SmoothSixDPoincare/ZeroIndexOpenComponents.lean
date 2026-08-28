import Wikipedia.SmoothSixDPoincare.ZeroIndexBoundaryPair
import Wikipedia.SmoothSixDPoincare.OpenSurgeryExterior
import Wikipedia.SmoothSixDPoincare.OpenPartitionDiffeomorph

/-! # The born sphere and retained boundary are complementary open submanifolds -/

noncomputable section

open Set Function Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

open PuncturedHandle

variable {E F R X Y : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y] [Subsingleton E]
  (d : SurgeryBoundaryPair E F R X Y)

theorem zeroIndex_oldOpenExterior : (d.oldOpenExterior : Set X) = univ := by
  apply eq_univ_of_forall
  intro x
  rintro ⟨p, _⟩
  exact isEmptyElim p.1

theorem zeroIndex_newPiece_range : range d.newPiece = range d.beltSphere := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.2, congrArg d.newPiece (Prod.ext (Subsingleton.elim _ _) rfl)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨(ballZero, v), rfl⟩

theorem zeroIndex_belt_range : range d.beltSphere = (range d.newExterior)ᶜ := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩ ⟨r, hr⟩
    exact d.newExterior_avoids r ⟨v, hr.symm⟩
  · intro hy
    have h : y ∈ range d.newExterior ∪ range d.newPiece := d.new_cover ▸ mem_univ y
    rw [d.zeroIndex_newPiece_range] at h
    exact h.resolve_left hy

def bornOpen : Opens Y :=
  ⟨range d.beltSphere, by
    rw [d.zeroIndex_belt_range]
    exact d.newExterior_closed.isClosed_range.isOpen_compl⟩

def bornCoordinates : UnitSphere F ≃ₜ d.bornOpen := d.zeroIndex_belt_closed.toHomeomorph

theorem bornCoordinates_coe (v : UnitSphere F) : (d.bornCoordinates v).val = d.beltSphere v := rfl

theorem bornCoordinates_symm_coe (y : d.bornOpen) :
    d.beltSphere (d.bornCoordinates.symm y) = y.val :=
  congrArg (fun z : d.bornOpen => z.val) (d.bornCoordinates.apply_symm_apply y)

theorem zeroIndex_open_disjoint : Disjoint (d.newOpenExterior : Set Y) d.bornOpen := by
  change Disjoint (range d.newPiece)ᶜ (range d.beltSphere)
  rw [d.zeroIndex_newPiece_range]
  exact disjoint_compl_left

theorem zeroIndex_open_cover : (d.newOpenExterior : Set Y) ∪ d.bornOpen = univ := by
  change (range d.newPiece)ᶜ ∪ range d.beltSphere = univ
  rw [d.zeroIndex_newPiece_range]
  exact compl_union_self _

theorem zeroIndex_mem_oldOpenExterior (x : X) : x ∈ d.oldOpenExterior := by
  rintro ⟨p, _⟩
  exact isEmptyElim p.1

def zeroIndexOldCoordinates : X ≃ₜ d.oldOpenExterior where
  toFun x := ⟨x, d.zeroIndex_mem_oldOpenExterior x⟩
  invFun := Subtype.val
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

theorem zeroIndexOldCoordinates_coe (x : X) : (d.zeroIndexOldCoordinates x).val = x := rfl

theorem zeroIndexOldCoordinates_exterior (x : X) :
    (d.openExteriorHomeomorph (d.zeroIndexOldCoordinates x)).val =
      d.zeroIndexBoundaryHomeomorph (Sum.inl x) := by
  change d.newExterior (d.oldOpenCoordinates (d.zeroIndexOldCoordinates x)) =
    d.newExterior (d.zeroIndexOldExterior.symm x)
  apply congrArg d.newExterior
  apply d.oldExterior_closed.injective
  exact (d.oldExterior_oldOpenCoordinates (d.zeroIndexOldCoordinates x)).trans
    (d.zeroIndexOldExterior.apply_symm_apply x).symm

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H}

def zeroIndexOldDiffeomorph [ChartedSpace H X] : Diffeomorph J J X d.oldOpenExterior ∞ where
  toEquiv := d.zeroIndexOldCoordinates.toEquiv
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff d.oldOpenExterior _).mp contMDiff_id
  contMDiff_invFun := contMDiff_subtype_val

def zeroIndexPartitionDiffeomorph [ChartedSpace H Y] :
    Diffeomorph J J (d.newOpenExterior ⊕ d.bornOpen) Y ∞ :=
  OpenPartition.diffeomorph d.newOpenExterior d.bornOpen
    d.zeroIndex_open_disjoint d.zeroIndex_open_cover

end Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
