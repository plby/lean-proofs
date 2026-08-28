import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluingCover
import Wikipedia.HopfProblem.FundamentalGroupHomeomorph

/-!
# Actual fundamental-group maps in the threefold attachment diagram

The groups here belong to the literal preceding stage, filling, and full
regular overlap.  Flattening the auxiliary subspaces in the two-open-set
cover gives pointed homeomorphisms, and their induced group maps commute
with the actual geometric inclusions.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

abbrev AttachmentGroup (s : Finset Puncture) (i : Puncture) :=
  FundamentalGroup (partialPatch (insert i s)) (attachmentBase s i)

abbrev PreviousStageGroup (s : Finset Puncture) (i : Puncture) :=
  FundamentalGroup (partialPatch s)
    ⟨attachmentPoint i, attachmentPoint_mem_partialPatch s i⟩

abbrev FillingGroup (i : Puncture) :=
  FundamentalGroup (liftedPatch (some i))
    ⟨attachmentPoint i, attachmentPoint_mem_filling i⟩

abbrev RegularOverlap (i : Puncture) :=
  ((liftedPatch none : Set Space) ∩ liftedPatch (some i) : Set Space)

abbrev regularOverlapPoint (i : Puncture) : RegularOverlap i :=
  ⟨attachmentPoint i, attachmentPoint_mem_regular i, attachmentPoint_mem_filling i⟩

abbrev RegularOverlapGroup (i : Puncture) :=
  FundamentalGroup (RegularOverlap i) (regularOverlapPoint i)

def previousStageInclusion (s : Finset Puncture) (i : Puncture) :
    C(partialPatch s, partialPatch (insert i s)) :=
  ⟨fun x => ⟨x.val, partialPatch_le_insert s i x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def fillingStageInclusion (s : Finset Puncture) (i : Puncture) :
    C(liftedPatch (some i), partialPatch (insert i s)) :=
  ⟨fun x => ⟨x.val, filling_le_partialPatch_insert s i x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def overlapPreviousInclusion (s : Finset Puncture) (i : Puncture) :
    C(RegularOverlap i, partialPatch s) :=
  ⟨fun x => ⟨x.val, regular_le_partialPatch s x.property.1⟩,
    continuous_subtype_val.subtype_mk _⟩

def overlapFillingInclusion (i : Puncture) : C(RegularOverlap i, liftedPatch (some i)) :=
  ⟨fun x => ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩

def previousStageHom (s : Finset Puncture) (i : Puncture) :
    PreviousStageGroup s i →* AttachmentGroup s i :=
  FundamentalGroup.map (previousStageInclusion s i)
    ⟨attachmentPoint i, attachmentPoint_mem_partialPatch s i⟩

def fillingStageHom (s : Finset Puncture) (i : Puncture) :
    FillingGroup i →* AttachmentGroup s i :=
  FundamentalGroup.map (fillingStageInclusion s i)
    ⟨attachmentPoint i, attachmentPoint_mem_filling i⟩

def overlapPreviousHom (s : Finset Puncture) (i : Puncture) :
    RegularOverlapGroup i →* PreviousStageGroup s i :=
  FundamentalGroup.map (overlapPreviousInclusion s i) (regularOverlapPoint i)

def overlapFillingHom (i : Puncture) : RegularOverlapGroup i →* FillingGroup i :=
  FundamentalGroup.map (overlapFillingInclusion i) (regularOverlapPoint i)

theorem attachmentHom_compatible (s : Finset Puncture) (i : Puncture) :
    (previousStageHom s i).comp (overlapPreviousHom s i) =
      (fillingStageHom s i).comp (overlapFillingHom i) := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- Flattening the left cover member gives the native previous-stage group. -/
def attachmentLeftGroupEquiv (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) :
    (attachmentCover s i hi).UGroup ≃* PreviousStageGroup s i :=
  homeomorphFundamentalGroupEquiv (attachmentLeftHomeomorph s i hi)
    (attachmentCover s i hi).baseUPoint

/-- Flattening the right member gives the native filling group. -/
def attachmentRightGroupEquiv (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) :
    (attachmentCover s i hi).VGroup ≃* FillingGroup i :=
  homeomorphFundamentalGroupEquiv (attachmentRightHomeomorph s i hi)
    (attachmentCover s i hi).baseVPoint

/-- Flattening the intersection gives the group of the full regular overlap. -/
def attachmentOverlapGroupEquiv (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) :
    (attachmentCover s i hi).OverlapGroup ≃* RegularOverlapGroup i :=
  homeomorphFundamentalGroupEquiv (attachmentOverlapHomeomorph s i hi)
    (attachmentCover s i hi).baseOverlapPoint

theorem attachmentLeftGroupEquiv_inclusion (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) :
    (previousStageHom s i).comp (attachmentLeftGroupEquiv s i hi).toMonoidHom =
      (attachmentCover s i hi).inclusionHomU := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

theorem attachmentRightGroupEquiv_inclusion (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) :
    (fillingStageHom s i).comp (attachmentRightGroupEquiv s i hi).toMonoidHom =
      (attachmentCover s i hi).inclusionHomV := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

theorem attachmentLeftGroupEquiv_overlap (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) :
    (attachmentLeftGroupEquiv s i hi).toMonoidHom.comp
        (attachmentCover s i hi).overlapHomU =
      (overlapPreviousHom s i).comp (attachmentOverlapGroupEquiv s i hi).toMonoidHom := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

theorem attachmentRightGroupEquiv_overlap (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) :
    (attachmentRightGroupEquiv s i hi).toMonoidHom.comp
        (attachmentCover s i hi).overlapHomV =
      (overlapFillingHom i).comp (attachmentOverlapGroupEquiv s i hi).toMonoidHom := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
