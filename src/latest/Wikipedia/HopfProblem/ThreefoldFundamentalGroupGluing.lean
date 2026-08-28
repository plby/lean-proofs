import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluingUniversal

/-!
# The actual threefold fundamental group by successive filling attachments

Every finite attachment stage satisfies the genuine van Kampen universal
property, with the literal geometric inclusion maps.  The initial stage
is the actual regular family, and the full stage is the constructed
threefold.  In particular, the final attachment gives an explicit group
pushout isomorphism to the actual fundamental group of the threefold.

This establishes the topological gluing step; evaluating the inclusion
maps on lattice and meridian generators is a separate calculation.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

/-- The empty attachment stage is the full open regular patch. -/
def emptyStageHomeomorph : partialPatch ∅ ≃ₜ liftedPatch none :=
  Homeomorph.setCongr (by rw [partialPatch_empty])

@[simp] theorem emptyStageHomeomorph_val (x : partialPatch ∅) :
    (emptyStageHomeomorph x : Space) = x.val := rfl

/-- The actual regular quotient family is the initial stage. -/
def regularStageHomeomorph : SpecialRegularFamily ≃ₜ partialPatch ∅ :=
  (gluingData.patchHomeomorph none).trans emptyStageHomeomorph.symm

@[simp] theorem regularStageHomeomorph_val (x : SpecialRegularFamily) :
    (regularStageHomeomorph x : Space) = inclusion none x := rfl

/-- The initial fundamental group is the native regular-family fundamental group. -/
def initialStageFundamentalGroupEquiv (x : partialPatch ∅) :
    FundamentalGroup (partialPatch ∅) x ≃*
      FundamentalGroup SpecialRegularFamily (regularStageHomeomorph.symm x) :=
  homeomorphFundamentalGroupEquiv regularStageHomeomorph.symm x

/-- Once all three fillings are attached, flattening the full stage gives the actual space. -/
def fullStageHomeomorph : partialPatch Finset.univ ≃ₜ Space where
  toFun := Subtype.val
  invFun x := ⟨x, by rw [partialPatch_univ]; trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk
    (fun x : Space => by rw [partialPatch_univ]; trivial)

@[simp] theorem fullStageHomeomorph_apply (x : partialPatch Finset.univ) :
    fullStageHomeomorph x = x.val := rfl

/-- This is the actual fundamental group of the constructed threefold, not
a group only declared to model it. -/
def fullStageFundamentalGroupEquiv (x : partialPatch Finset.univ) :
    FundamentalGroup (partialPatch Finset.univ) x ≃* FundamentalGroup Space x.val :=
  homeomorphFundamentalGroupEquiv fullStageHomeomorph x

/-- Any one of the three fillings may be chosen as the last attachment. -/
def terminalStageHomeomorph (i : Puncture) :
    partialPatch (insert i (Finset.univ.erase i)) ≃ₜ Space :=
  (Homeomorph.setCongr (show
    (partialPatch (insert i (Finset.univ.erase i)) : Set Space) =
      (partialPatch Finset.univ : Set Space) by
    rw [Finset.insert_erase (Finset.mem_univ i)])).trans fullStageHomeomorph

@[simp] theorem terminalStageHomeomorph_apply (i : Puncture)
    (x : partialPatch (insert i (Finset.univ.erase i))) :
    terminalStageHomeomorph i x = x.val := rfl

/-- The final actual attachment group, at its actual overlap point. -/
def terminalFundamentalGroupEquiv (i : Puncture) :
    AttachmentGroup (Finset.univ.erase i) i ≃* FundamentalGroup Space (attachmentPoint i) :=
  homeomorphFundamentalGroupEquiv (terminalStageHomeomorph i)
    (attachmentBase (Finset.univ.erase i) i)

/-- A genuine pushout description of the actual threefold fundamental group.
The previous stage is itself obtained by the same proved attachment theorem. -/
def terminalPushoutEquiv (i : Puncture) :
    (attachmentCover (Finset.univ.erase i) i (Finset.notMem_erase i Finset.univ)).Pushout ≃*
      FundamentalGroup Space (attachmentPoint i) :=
  (attachmentPushoutEquiv (Finset.univ.erase i) i (Finset.notMem_erase i Finset.univ)).trans
    (terminalFundamentalGroupEquiv i)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
