import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluingCoverBasic
import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluingCoverHomeomorphs
import Wikipedia.HopfProblem.FundamentalGroupVanKampenCover

/-!
# Actual two-open-set covers for each filling attachment

Every step of attaching a genuine filling has a concrete two-open-set
cover, with path-connected members and path-connected intersection.
The old stage, new filling, and regular overlap are identified with the
corresponding subspaces by homeomorphisms preserving the actual point.
-/

noncomputable section

open Set TopologicalSpace

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open FundamentalGroupVanKampen

/-- The previous stage as an open subset of the enlarged stage. -/
def attachmentLeft (s : Finset Puncture) (i : Puncture) :
    Opens (partialPatch (insert i s)) :=
  Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ (partialPatch s)

/-- The new filling as an open subset of the enlarged stage. -/
def attachmentRight (s : Finset Puncture) (i : Puncture) :
    Opens (partialPatch (insert i s)) :=
  Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ (liftedPatch (some i))

@[simp] theorem mem_attachmentLeft (s : Finset Puncture) (i : Puncture)
    (x : partialPatch (insert i s)) :
    x ∈ attachmentLeft s i ↔ (x : Space) ∈ partialPatch s := Iff.rfl

@[simp] theorem mem_attachmentRight (s : Finset Puncture) (i : Puncture)
    (x : partialPatch (insert i s)) :
    x ∈ attachmentRight s i ↔ (x : Space) ∈ liftedPatch (some i) := Iff.rfl

/-- The same actual overlap point is used regardless of the preceding stage. -/
def attachmentBase (s : Finset Puncture) (i : Puncture) : partialPatch (insert i s) :=
  ⟨attachmentPoint i, attachmentPoint_mem_partialPatch (insert i s) i⟩

@[simp] theorem attachmentBase_val (s : Finset Puncture) (i : Puncture) :
    (attachmentBase s i : Space) = attachmentPoint i := rfl

theorem attachmentLeft_union_right (s : Finset Puncture) (i : Puncture) :
    (attachmentLeft s i : Set (partialPatch (insert i s))) ∪ attachmentRight s i = univ := by
  apply eq_univ_of_forall
  intro x
  change (x : Space) ∈ partialPatch s ∨ (x : Space) ∈ liftedPatch (some i)
  exact (le_of_eq (partialPatch_insert s i)) x.property

theorem attachmentLeft_isPathConnected (s : Finset Puncture) (i : Puncture) :
    IsPathConnected (attachmentLeft s i : Set (partialPatch (insert i s))) :=
  (partialPatch_isPathConnected s).preimage_coe (partialPatch_le_insert s i)

theorem attachmentRight_isPathConnected (s : Finset Puncture) (i : Puncture) :
    IsPathConnected (attachmentRight s i : Set (partialPatch (insert i s))) :=
  (liftedPatch_isPathConnected (some i)).preimage_coe (filling_le_partialPatch_insert s i)

/-- The actual overlap in the enlarged stage is the preimage of the regular overlap. -/
theorem attachment_intersection_eq (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) :
    (attachmentLeft s i : Set (partialPatch (insert i s))) ∩ attachmentRight s i =
      (Subtype.val : partialPatch (insert i s) → Space) ⁻¹'
        ((liftedPatch none : Set Space) ∩ liftedPatch (some i)) := by
  change (Subtype.val : partialPatch (insert i s) → Space) ⁻¹'
      (partialPatch s : Set Space) ∩
      (Subtype.val : partialPatch (insert i s) → Space) ⁻¹'
        (liftedPatch (some i) : Set Space) = _
  rw [← preimage_inter, partialPatch_inter_filling_eq s i hi]

theorem attachmentIntersection_isPathConnected (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) :
    IsPathConnected ((attachmentLeft s i : Set (partialPatch (insert i s))) ∩
      attachmentRight s i) := by
  rw [attachment_intersection_eq s i hi]
  exact (liftedPatch_regular_inter_isPathConnected i).preimage_coe
    (fun _ hx => regular_le_partialPatch (insert i s) hx.1)

/-- The genuine based cover used to attach one previously absent filling. -/
def attachmentCover (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) :
    TwoOpenCover (partialPatch (insert i s)) where
  U := attachmentLeft s i
  V := attachmentRight s i
  cover := attachmentLeft_union_right s i
  pathConnectedU := attachmentLeft_isPathConnected s i
  pathConnectedV := attachmentRight_isPathConnected s i
  pathConnectedIntersection := attachmentIntersection_isPathConnected s i hi
  base := attachmentBase s i
  baseU := attachmentPoint_mem_partialPatch s i
  baseV := attachmentPoint_mem_filling i

@[simp] theorem attachmentCover_base_val (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) :
    ((attachmentCover s i hi).base : Space) = attachmentPoint i := rfl

/-- The left member is homeomorphic to the full preceding stage. -/
def attachmentLeftHomeomorph (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) :
    (attachmentCover s i hi).U ≃ₜ partialPatch s :=
  subspacePreimageHomeomorph (partialPatch_le_insert s i)

/-- The right member is homeomorphic to the full new filling. -/
def attachmentRightHomeomorph (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) :
    (attachmentCover s i hi).V ≃ₜ liftedPatch (some i) :=
  subspacePreimageHomeomorph (filling_le_partialPatch_insert s i)

/-- The intersection is the genuine full regular/filling overlap. -/
def attachmentOverlapHomeomorph (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) :
    (attachmentCover s i hi).overlap ≃ₜ
      ((liftedPatch none : Set Space) ∩ liftedPatch (some i) : Set Space) :=
  (subspacePreimageInterHomeomorph
    (fun _ hx => partialPatch_le_insert s i hx.1)).trans
      (Homeomorph.setCongr (partialPatch_inter_filling_eq s i hi))

@[simp] theorem attachmentLeftHomeomorph_val (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) (x : (attachmentCover s i hi).U) :
    (attachmentLeftHomeomorph s i hi x : Space) = x.val.val := rfl

@[simp] theorem attachmentRightHomeomorph_val (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) (x : (attachmentCover s i hi).V) :
    (attachmentRightHomeomorph s i hi x : Space) = x.val.val := rfl

@[simp] theorem attachmentOverlapHomeomorph_val (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) (x : (attachmentCover s i hi).overlap) :
    (attachmentOverlapHomeomorph s i hi x : Space) = x.val.val := rfl

@[simp] theorem attachmentLeftHomeomorph_base (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) :
    attachmentLeftHomeomorph s i hi (attachmentCover s i hi).baseUPoint =
      ⟨attachmentPoint i, attachmentPoint_mem_partialPatch s i⟩ := rfl

@[simp] theorem attachmentRightHomeomorph_base (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) :
    attachmentRightHomeomorph s i hi (attachmentCover s i hi).baseVPoint =
      ⟨attachmentPoint i, attachmentPoint_mem_filling i⟩ := rfl

@[simp] theorem attachmentOverlapHomeomorph_base (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) :
    attachmentOverlapHomeomorph s i hi (attachmentCover s i hi).baseOverlapPoint =
      ⟨attachmentPoint i, attachmentPoint_mem_regular i, attachmentPoint_mem_filling i⟩ := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
