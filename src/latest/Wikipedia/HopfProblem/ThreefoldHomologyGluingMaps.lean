import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluing
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Actual singular-homology maps for the threefold filling attachments

The homology groups are the integral singular homology of the literal
attachment stages, fillings, and full regular overlaps. Their maps are
induced by the existing geometric continuous inclusions. The genuine
cover-flattening homeomorphisms identify these maps with the raw subtype
and intersection inclusions used in the Mayer–Vietoris sequence.
-/

noncomputable section

open Set
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- Integral singular homology of the actual preceding attachment stage. -/
abbrev StageHomology (s : Finset Puncture) (n : ℕ) :=
  SingularHomology (partialPatch s) n

/-- Integral singular homology of the full actual filling patch. -/
abbrev FillingPatchHomology (i : Puncture) (n : ℕ) :=
  SingularHomology (liftedPatch (some i)) n

/-- Integral singular homology of the full actual regular/filling overlap. -/
abbrev OverlapHomology (i : Puncture) (n : ℕ) :=
  SingularHomology (RegularOverlap i) n

def previousStageHomologyMap (s : Finset Puncture) (i : Puncture) (n : ℕ) :
    StageHomology s n →ₗ[ℤ] StageHomology (insert i s) n :=
  singularHomologyMap (previousStageInclusion s i) n

def fillingStageHomologyMap (s : Finset Puncture) (i : Puncture) (n : ℕ) :
    FillingPatchHomology i n →ₗ[ℤ] StageHomology (insert i s) n :=
  singularHomologyMap (fillingStageInclusion s i) n

def overlapPreviousHomologyMap (s : Finset Puncture) (i : Puncture) (n : ℕ) :
    OverlapHomology i n →ₗ[ℤ] StageHomology s n :=
  singularHomologyMap (overlapPreviousInclusion s i) n

def overlapFillingHomologyMap (i : Puncture) (n : ℕ) :
    OverlapHomology i n →ₗ[ℤ] FillingPatchHomology i n :=
  singularHomologyMap (overlapFillingInclusion i) n

@[simp] theorem previousStageHomologyMap_apply (s : Finset Puncture) (i : Puncture)
    (n : ℕ) (a : StageHomology s n) :
    previousStageHomologyMap s i n a =
      singularHomologyMap (previousStageInclusion s i) n a := rfl

@[simp] theorem fillingStageHomologyMap_apply (s : Finset Puncture) (i : Puncture)
    (n : ℕ) (a : FillingPatchHomology i n) :
    fillingStageHomologyMap s i n a =
      singularHomologyMap (fillingStageInclusion s i) n a := rfl

@[simp] theorem overlapPreviousHomologyMap_apply (s : Finset Puncture) (i : Puncture)
    (n : ℕ) (a : OverlapHomology i n) :
    overlapPreviousHomologyMap s i n a =
      singularHomologyMap (overlapPreviousInclusion s i) n a := rfl

@[simp] theorem overlapFillingHomologyMap_apply (i : Puncture) (n : ℕ)
    (a : OverlapHomology i n) :
    overlapFillingHomologyMap i n a =
      singularHomologyMap (overlapFillingInclusion i) n a := rfl

/-- The two actual routes from the overlap to the enlarged stage induce
the same map on integral singular homology in every degree. -/
theorem attachmentHomologyMap_compatible (s : Finset Puncture) (i : Puncture) (n : ℕ) :
    (previousStageHomologyMap s i n).comp (overlapPreviousHomologyMap s i n) =
      (fillingStageHomologyMap s i n).comp (overlapFillingHomologyMap i n) := by
  rw [previousStageHomologyMap, overlapPreviousHomologyMap,
    fillingStageHomologyMap, overlapFillingHomologyMap,
    ← singularHomologyMap_comp, ← singularHomologyMap_comp]
  rfl

/-- The left cover member has exactly the homology of the preceding stage. -/
def attachmentLeftHomologyEquiv (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) (n : ℕ) :
    SingularHomology (attachmentLeft s i) n ≃ₗ[ℤ] StageHomology s n :=
  homeomorphHomologyEquiv (attachmentLeftHomeomorph s i hi) n

/-- The right cover member has exactly the homology of the full new filling. -/
def attachmentRightHomologyEquiv (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) (n : ℕ) :
    SingularHomology (attachmentRight s i) n ≃ₗ[ℤ] FillingPatchHomology i n :=
  homeomorphHomologyEquiv (attachmentRightHomeomorph s i hi) n

/-- The cover intersection has exactly the homology of the actual full
regular/filling overlap, by the proved geometric homeomorphism. -/
def attachmentOverlapHomologyEquiv (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) (n : ℕ) :
    SingularHomology
        ((attachmentLeft s i : Set (partialPatch (insert i s))) ∩ attachmentRight s i :
          Set (partialPatch (insert i s))) n
      ≃ₗ[ℤ] OverlapHomology i n :=
  homeomorphHomologyEquiv (attachmentOverlapHomeomorph s i hi) n

@[simp] theorem attachmentLeftHomologyEquiv_toLinearMap (s : Finset Puncture)
    (i : Puncture) (hi : i ∉ s) (n : ℕ) :
    (attachmentLeftHomologyEquiv s i hi n).toLinearMap =
      singularHomologyMap (attachmentLeftHomeomorph s i hi :
        C((attachmentCover s i hi).U, partialPatch s)) n := rfl

@[simp] theorem attachmentRightHomologyEquiv_toLinearMap (s : Finset Puncture)
    (i : Puncture) (hi : i ∉ s) (n : ℕ) :
    (attachmentRightHomologyEquiv s i hi n).toLinearMap =
      singularHomologyMap (attachmentRightHomeomorph s i hi :
        C((attachmentCover s i hi).V, liftedPatch (some i))) n := rfl

@[simp] theorem attachmentOverlapHomologyEquiv_toLinearMap (s : Finset Puncture)
    (i : Puncture) (hi : i ∉ s) (n : ℕ) :
    (attachmentOverlapHomologyEquiv s i hi n).toLinearMap =
      singularHomologyMap (attachmentOverlapHomeomorph s i hi :
        C((attachmentCover s i hi).overlap, RegularOverlap i)) n := rfl

/-- The left geometric inclusion agrees with the literal raw
Mayer–Vietoris subtype inclusion after flattening the cover member. -/
theorem attachmentLeftHomologyEquiv_inclusion (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) (n : ℕ) :
    (previousStageHomologyMap s i n).comp (attachmentLeftHomologyEquiv s i hi n).toLinearMap =
      singularHomologyMap (subtypeInclusion
        (attachmentLeft s i : Set (partialPatch (insert i s)))) n := by
  let e : attachmentLeft s i ≃ₜ partialPatch s := attachmentLeftHomeomorph s i hi
  change (singularHomologyMap (previousStageInclusion s i) n).comp
      (singularHomologyMap (e : C(attachmentLeft s i, partialPatch s)) n) = _
  rw [← singularHomologyMap_comp]
  apply congrArg (fun f : C(attachmentLeft s i, partialPatch (insert i s)) =>
    singularHomologyMap f n)
  apply ContinuousMap.ext
  intro x
  rfl

/-- The same comparison for the literal filling inclusion. -/
theorem attachmentRightHomologyEquiv_inclusion (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) (n : ℕ) :
    (fillingStageHomologyMap s i n).comp (attachmentRightHomologyEquiv s i hi n).toLinearMap =
      singularHomologyMap (subtypeInclusion
        (attachmentRight s i : Set (partialPatch (insert i s)))) n := by
  let e : attachmentRight s i ≃ₜ liftedPatch (some i) := attachmentRightHomeomorph s i hi
  change (singularHomologyMap (fillingStageInclusion s i) n).comp
      (singularHomologyMap (e : C(attachmentRight s i, liftedPatch (some i))) n) = _
  rw [← singularHomologyMap_comp]
  apply congrArg (fun f : C(attachmentRight s i, partialPatch (insert i s)) =>
    singularHomologyMap f n)
  apply ContinuousMap.ext
  intro x
  rfl

/-- The first raw intersection inclusion becomes the actual overlap-to-
preceding-stage map under the genuine homology equivalences. -/
theorem attachmentLeftHomologyEquiv_overlap (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) (n : ℕ) :
    (attachmentLeftHomologyEquiv s i hi n).toLinearMap.comp
        (singularHomologyMap (ContinuousMap.inclusion
          (Set.inter_subset_left :
            (attachmentLeft s i : Set (partialPatch (insert i s))) ∩ attachmentRight s i ⊆
              attachmentLeft s i)) n) =
      (overlapPreviousHomologyMap s i n).comp
        (attachmentOverlapHomologyEquiv s i hi n).toLinearMap := by
  let eL : attachmentLeft s i ≃ₜ partialPatch s := attachmentLeftHomeomorph s i hi
  let eO : ((attachmentLeft s i : Set (partialPatch (insert i s))) ∩
      attachmentRight s i : Set (partialPatch (insert i s))) ≃ₜ RegularOverlap i :=
    attachmentOverlapHomeomorph s i hi
  change (singularHomologyMap (eL : C(attachmentLeft s i, partialPatch s)) n).comp
      (singularHomologyMap (ContinuousMap.inclusion
        (Set.inter_subset_left :
          (attachmentLeft s i : Set (partialPatch (insert i s))) ∩ attachmentRight s i ⊆
            attachmentLeft s i)) n) =
    (singularHomologyMap (overlapPreviousInclusion s i) n).comp
      (singularHomologyMap (eO : C(_, RegularOverlap i)) n)
  rw [← singularHomologyMap_comp, ← singularHomologyMap_comp]
  apply congrArg (fun f : C(((attachmentLeft s i : Set (partialPatch (insert i s))) ∩
      attachmentRight s i : Set (partialPatch (insert i s))), partialPatch s) =>
    singularHomologyMap f n)
  apply ContinuousMap.ext
  intro x
  rfl

/-- The second raw intersection inclusion becomes the actual overlap-to-
filling map; the Mayer–Vietoris minus sign can be applied afterwards. -/
theorem attachmentRightHomologyEquiv_overlap (s : Finset Puncture) (i : Puncture)
    (hi : i ∉ s) (n : ℕ) :
    (attachmentRightHomologyEquiv s i hi n).toLinearMap.comp
        (singularHomologyMap (ContinuousMap.inclusion
          (Set.inter_subset_right :
            (attachmentLeft s i : Set (partialPatch (insert i s))) ∩ attachmentRight s i ⊆
              attachmentRight s i)) n) =
      (overlapFillingHomologyMap i n).comp
        (attachmentOverlapHomologyEquiv s i hi n).toLinearMap := by
  let eR : attachmentRight s i ≃ₜ liftedPatch (some i) := attachmentRightHomeomorph s i hi
  let eO : ((attachmentLeft s i : Set (partialPatch (insert i s))) ∩
      attachmentRight s i : Set (partialPatch (insert i s))) ≃ₜ RegularOverlap i :=
    attachmentOverlapHomeomorph s i hi
  change (singularHomologyMap (eR : C(attachmentRight s i, liftedPatch (some i))) n).comp
      (singularHomologyMap (ContinuousMap.inclusion
        (Set.inter_subset_right :
          (attachmentLeft s i : Set (partialPatch (insert i s))) ∩ attachmentRight s i ⊆
            attachmentRight s i)) n) =
    (singularHomologyMap (overlapFillingInclusion i) n).comp
      (singularHomologyMap (eO : C(_, RegularOverlap i)) n)
  rw [← singularHomologyMap_comp, ← singularHomologyMap_comp]
  apply congrArg (fun f : C(((attachmentLeft s i : Set (partialPatch (insert i s))) ∩
      attachmentRight s i : Set (partialPatch (insert i s))), liftedPatch (some i)) =>
    singularHomologyMap f n)
  apply ContinuousMap.ext
  intro x
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
