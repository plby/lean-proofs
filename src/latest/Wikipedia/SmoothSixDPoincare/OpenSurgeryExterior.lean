import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

/-!
# The open common exterior of the two whole surgery pieces

Removing the whole closed piece, rather than only its core, leaves an open
subset of each boundary. The original common-exterior embeddings identify
these open subsets, with their exact original point maps.
-/

noncomputable section

open Set Function Topology TopologicalSpace

namespace Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

open PuncturedHandle

variable {N P R X Y : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair N P R X Y)

def oldOpenExterior : Opens X :=
  ⟨(range d.oldPiece)ᶜ, d.oldPiece_closed.isClosed_range.isOpen_compl⟩

def newOpenExterior : Opens Y :=
  ⟨(range d.newPiece)ᶜ, d.newPiece_closed.isClosed_range.isOpen_compl⟩

theorem oldOpenExterior_mem_range (x : d.oldOpenExterior) : x.val ∈ range d.oldExterior := by
  have hx : x.val ∈ range d.oldExterior ∪ range d.oldPiece := d.old_cover ▸ mem_univ x.val
  exact hx.resolve_right x.property

theorem newOpenExterior_mem_range (y : d.newOpenExterior) : y.val ∈ range d.newExterior := by
  have hy : y.val ∈ range d.newExterior ∪ range d.newPiece := d.new_cover ▸ mem_univ y.val
  exact hy.resolve_right y.property

def oldOpenCoordinates (x : d.oldOpenExterior) : R :=
  d.oldExterior_closed.toHomeomorph.symm ⟨x.val, d.oldOpenExterior_mem_range x⟩

def newOpenCoordinates (y : d.newOpenExterior) : R :=
  d.newExterior_closed.toHomeomorph.symm ⟨y.val, d.newOpenExterior_mem_range y⟩

theorem oldExterior_oldOpenCoordinates (x : d.oldOpenExterior) :
    d.oldExterior (d.oldOpenCoordinates x) = x.val :=
  congrArg Subtype.val (d.oldExterior_closed.toHomeomorph.apply_symm_apply
    ⟨x.val, d.oldOpenExterior_mem_range x⟩)

theorem newExterior_newOpenCoordinates (y : d.newOpenExterior) :
    d.newExterior (d.newOpenCoordinates y) = y.val :=
  congrArg Subtype.val (d.newExterior_closed.toHomeomorph.apply_symm_apply
    ⟨y.val, d.newOpenExterior_mem_range y⟩)

theorem newExterior_oldOpenCoordinates_not_mem (x : d.oldOpenExterior) :
    d.newExterior (d.oldOpenCoordinates x) ∉ range d.newPiece := by
  rintro ⟨p, hp⟩
  obtain ⟨q, hq, -⟩ := (d.new_overlap _ _).mp hp.symm
  apply x.property
  refine ⟨oldBoundary q, ?_⟩
  have h := (d.old_overlap (d.oldOpenCoordinates x) (oldBoundary q)).mpr ⟨q, hq, rfl⟩
  exact h.symm.trans (d.oldExterior_oldOpenCoordinates x)

theorem oldExterior_newOpenCoordinates_not_mem (y : d.newOpenExterior) :
    d.oldExterior (d.newOpenCoordinates y) ∉ range d.oldPiece := by
  rintro ⟨p, hp⟩
  obtain ⟨q, hq, -⟩ := (d.old_overlap _ _).mp hp.symm
  apply y.property
  refine ⟨newBoundary q, ?_⟩
  have h := (d.new_overlap (d.newOpenCoordinates y) (newBoundary q)).mpr ⟨q, hq, rfl⟩
  exact h.symm.trans (d.newExterior_newOpenCoordinates y)

def openExteriorHomeomorph : d.oldOpenExterior ≃ₜ d.newOpenExterior where
  toFun x := ⟨d.newExterior (d.oldOpenCoordinates x),
    d.newExterior_oldOpenCoordinates_not_mem x⟩
  invFun y := ⟨d.oldExterior (d.newOpenCoordinates y),
    d.oldExterior_newOpenCoordinates_not_mem y⟩
  left_inv x := by
    apply Subtype.ext
    have hc : d.newOpenCoordinates
        ⟨d.newExterior (d.oldOpenCoordinates x), d.newExterior_oldOpenCoordinates_not_mem x⟩ =
        d.oldOpenCoordinates x :=
      d.newExterior_closed.injective (d.newExterior_newOpenCoordinates _)
    exact (congrArg d.oldExterior hc).trans (d.oldExterior_oldOpenCoordinates x)
  right_inv y := by
    apply Subtype.ext
    have hc : d.oldOpenCoordinates
        ⟨d.oldExterior (d.newOpenCoordinates y), d.oldExterior_newOpenCoordinates_not_mem y⟩ =
        d.newOpenCoordinates y :=
      d.oldExterior_closed.injective (d.oldExterior_oldOpenCoordinates _)
    exact (congrArg d.newExterior hc).trans (d.newExterior_newOpenCoordinates y)
  continuous_toFun := (d.newExterior_closed.continuous.comp
    (d.oldExterior_closed.toHomeomorph.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _
  continuous_invFun := (d.oldExterior_closed.continuous.comp
    (d.newExterior_closed.toHomeomorph.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _

theorem openExteriorHomeomorph_coe (x : d.oldOpenExterior) :
    (d.openExteriorHomeomorph x).val = d.newExterior (d.oldOpenCoordinates x) := rfl

theorem openExteriorHomeomorph_symm_coe (y : d.newOpenExterior) :
    (d.openExteriorHomeomorph.symm y).val = d.oldExterior (d.newOpenCoordinates y) := rfl

end Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
