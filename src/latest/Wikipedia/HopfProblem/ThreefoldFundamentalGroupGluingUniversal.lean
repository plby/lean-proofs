import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluingMaps
import Wikipedia.HopfProblem.FundamentalGroupVanKampen

/-!
# Van Kampen for each actual threefold filling attachment

The standard two-open-set theorem is applied to the constructed stage
cover.  The resulting universal property is stated directly on the
fundamental groups of the previous stage, the full filling, and their
full regular overlap, with their genuine geometric inclusion maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

variable {G : Type*} [Group G]
variable (s : Finset Puncture) (i : Puncture) (hi : i ∉ s)

def AttachmentCompatible (f : PreviousStageGroup s i →* G) (g : FillingGroup i →* G) : Prop :=
  f.comp (overlapPreviousHom s i) = g.comp (overlapFillingHom i)

theorem attachmentCover_compatible (f : PreviousStageGroup s i →* G)
    (g : FillingGroup i →* G) (h : AttachmentCompatible s i f g) :
    (attachmentCover s i hi).Compatible
      (f.comp (attachmentLeftGroupEquiv s i hi).toMonoidHom)
      (g.comp (attachmentRightGroupEquiv s i hi).toMonoidHom) := by
  change (f.comp (attachmentLeftGroupEquiv s i hi).toMonoidHom).comp
      (attachmentCover s i hi).overlapHomU =
    (g.comp (attachmentRightGroupEquiv s i hi).toMonoidHom).comp
      (attachmentCover s i hi).overlapHomV
  rw [MonoidHom.comp_assoc, attachmentLeftGroupEquiv_overlap,
    ← MonoidHom.comp_assoc, h, MonoidHom.comp_assoc,
    ← attachmentRightGroupEquiv_overlap, ← MonoidHom.comp_assoc]

/-- The actual induced homomorphism after attaching one genuine filling. -/
def attachmentLift (f : PreviousStageGroup s i →* G) (g : FillingGroup i →* G)
    (h : AttachmentCompatible s i f g) : AttachmentGroup s i →* G :=
  (attachmentCover s i hi).lift
    (f.comp (attachmentLeftGroupEquiv s i hi).toMonoidHom)
    (g.comp (attachmentRightGroupEquiv s i hi).toMonoidHom)
    (attachmentCover_compatible s i hi f g h)

theorem attachmentLift_comp_previous (f : PreviousStageGroup s i →* G)
    (g : FillingGroup i →* G) (h : AttachmentCompatible s i f g) :
    (attachmentLift s i hi f g h).comp (previousStageHom s i) = f := by
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (attachmentLeftGroupEquiv s i hi).surjective x
  have hr := (attachmentCover s i hi).lift_comp_inclusionU
    (f.comp (attachmentLeftGroupEquiv s i hi).toMonoidHom)
    (g.comp (attachmentRightGroupEquiv s i hi).toMonoidHom)
    (attachmentCover_compatible s i hi f g h)
  exact (congrArg (attachmentLift s i hi f g h)
    (DFunLike.congr_fun (attachmentLeftGroupEquiv_inclusion s i hi) y)).trans
      (DFunLike.congr_fun hr y)

theorem attachmentLift_comp_filling (f : PreviousStageGroup s i →* G)
    (g : FillingGroup i →* G) (h : AttachmentCompatible s i f g) :
    (attachmentLift s i hi f g h).comp (fillingStageHom s i) = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (attachmentRightGroupEquiv s i hi).surjective x
  have hr := (attachmentCover s i hi).lift_comp_inclusionV
    (f.comp (attachmentLeftGroupEquiv s i hi).toMonoidHom)
    (g.comp (attachmentRightGroupEquiv s i hi).toMonoidHom)
    (attachmentCover_compatible s i hi f g h)
  exact (congrArg (attachmentLift s i hi f g h)
    (DFunLike.congr_fun (attachmentRightGroupEquiv_inclusion s i hi) y)).trans
      (DFunLike.congr_fun hr y)

include hi in
/-- The two actual inclusions jointly determine every map out of the new stage group. -/
theorem attachment_hom_ext (f g : AttachmentGroup s i →* G)
    (hprev : f.comp (previousStageHom s i) = g.comp (previousStageHom s i))
    (hfill : f.comp (fillingStageHom s i) = g.comp (fillingStageHom s i)) : f = g := by
  apply (attachmentCover s i hi).hom_ext
  · ext γ
    have hmap := DFunLike.congr_fun (attachmentLeftGroupEquiv_inclusion s i hi) γ
    have hval := DFunLike.congr_fun hprev (attachmentLeftGroupEquiv s i hi γ)
    exact (congrArg f hmap).symm.trans (hval.trans (congrArg g hmap))
  · ext γ
    have hmap := DFunLike.congr_fun (attachmentRightGroupEquiv_inclusion s i hi) γ
    have hval := DFunLike.congr_fun hfill (attachmentRightGroupEquiv s i hi γ)
    exact (congrArg f hmap).symm.trans (hval.trans (congrArg g hmap))

include hi in
/-- The genuine previous stage and filling form the fundamental-group
pushout along their full regular overlap.  All topological hypotheses
have already been proved for these actual spaces. -/
theorem attachment_exists_unique_hom (f : PreviousStageGroup s i →* G)
    (g : FillingGroup i →* G) (h : AttachmentCompatible s i f g) :
    ∃! F : AttachmentGroup s i →* G,
      F.comp (previousStageHom s i) = f ∧ F.comp (fillingStageHom s i) = g := by
  refine ⟨attachmentLift s i hi f g h,
    ⟨attachmentLift_comp_previous s i hi f g h,
      attachmentLift_comp_filling s i hi f g h⟩, ?_⟩
  intro F hF
  exact attachment_hom_ext s i hi F (attachmentLift s i hi f g h)
    (hF.1.trans (attachmentLift_comp_previous s i hi f g h).symm)
    (hF.2.trans (attachmentLift_comp_filling s i hi f g h).symm)

/-- An explicit group-pushout isomorphism for every actual attachment.
The left, right, and overlap groups of this diagram are identified with
the literal geometric groups by the three `attachment*GroupEquiv` maps. -/
def attachmentPushoutEquiv : (attachmentCover s i hi).Pushout ≃* AttachmentGroup s i :=
  (attachmentCover s i hi).pushoutEquiv

theorem attachmentPushoutEquiv_previous :
    (attachmentPushoutEquiv s i hi).toMonoidHom.comp
        (attachmentCover s i hi).pushoutOfU =
      (previousStageHom s i).comp (attachmentLeftGroupEquiv s i hi).toMonoidHom :=
  ((attachmentCover s i hi).pushoutEquiv_comp_ofU).trans
    (attachmentLeftGroupEquiv_inclusion s i hi).symm

theorem attachmentPushoutEquiv_filling :
    (attachmentPushoutEquiv s i hi).toMonoidHom.comp
        (attachmentCover s i hi).pushoutOfV =
      (fillingStageHom s i).comp (attachmentRightGroupEquiv s i hi).toMonoidHom :=
  ((attachmentCover s i hi).pushoutEquiv_comp_ofV).trans
    (attachmentRightGroupEquiv_inclusion s i hi).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
