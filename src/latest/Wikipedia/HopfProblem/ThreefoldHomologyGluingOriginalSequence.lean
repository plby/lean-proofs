import Wikipedia.HopfProblem.ThreefoldHomologyGluingSequence
import Wikipedia.HopfProblem.ThreefoldHomologyGluingOriginalPieces

/-!
# Attachment homology in the original regular-family and filling coordinates

The full filling patch in the genuine Mayer–Vietoris sequence is replaced
by its original local piece through the existing patch homeomorphism.
The overlap maps are still induced by actual continuous maps: one factors
through the original regular family, and the other is the actual overlap
expressed in the original filling coordinates.
-/

noncomputable section

open Set
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- Actual integral singular homology of the original filling piece. -/
abbrev OriginalFillingHomology (i : Puncture) (n : ℕ) :=
  SingularHomology (localPiece (some i)) n

/-- Replace only the filling-patch factor through its actual homeomorphism. -/
def originalAttachmentPairEquiv (s : Finset Puncture) (i : Puncture) (n : ℕ) :
    (StageHomology s n × FillingPatchHomology i n) ≃ₗ[ℤ]
      (StageHomology s n × OriginalFillingHomology i n) :=
  ((AddEquiv.refl (StageHomology s n)).prodCongr
    (originalFillingHomologyEquiv i n).toAddEquiv).toIntLinearEquiv

/-- The actual signed overlap map in the original filling coordinates. -/
def originalAttachmentLeftHomologyMap (s : Finset Puncture) (i : Puncture) (n : ℕ) :
    OverlapHomology i n →ₗ[ℤ] (StageHomology s n × OriginalFillingHomology i n) :=
  (originalAttachmentPairEquiv s i n).toLinearMap.comp (attachmentLeftHomologyMap s i n)

/-- The actual sum of stage inclusions in the same original coordinates. -/
def originalAttachmentRightHomologyMap (s : Finset Puncture) (i : Puncture) (n : ℕ) :
    (StageHomology s n × OriginalFillingHomology i n) →ₗ[ℤ] StageHomology (insert i s) n :=
  (attachmentRightHomologyMap s i n).comp (originalAttachmentPairEquiv s i n).symm.toLinearMap

theorem originalAttachmentRightHomologyMap_comparison
    (s : Finset Puncture) (i : Puncture) (n : ℕ) :
    (originalAttachmentRightHomologyMap s i n).comp
        (originalAttachmentPairEquiv s i n).toLinearMap = attachmentRightHomologyMap s i n := by
  apply LinearMap.ext
  intro a
  change attachmentRightHomologyMap s i n
    ((originalAttachmentPairEquiv s i n).symm (originalAttachmentPairEquiv s i n a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The filling-coordinate component is induced by the actual map
from the full overlap into the original filling piece. -/
theorem originalAttachment_overlapFilling_eq (i : Puncture) (n : ℕ) :
    (originalFillingHomologyEquiv i n).toLinearMap.comp (overlapFillingHomologyMap i n) =
      singularHomologyMap (overlapToFilling i) n := by
  rw [originalFillingHomologyEquiv_toLinearMap, overlapFillingHomologyMap,
    ← singularHomologyMap_comp, ← overlapToFilling_eq]

@[simp] theorem originalAttachmentLeftHomologyMap_apply
    (s : Finset Puncture) (i : Puncture) (n : ℕ) (a : OverlapHomology i n) :
    originalAttachmentLeftHomologyMap s i n a =
      (overlapPreviousHomologyMap s i n a, -singularHomologyMap (overlapToFilling i) n a) := by
  change (overlapPreviousHomologyMap s i n a,
      originalFillingHomologyEquiv i n (-overlapFillingHomologyMap i n a)) = _
  rw [map_neg]
  apply Prod.ext
  · rfl
  · exact congrArg Neg.neg (LinearMap.congr_fun (originalAttachment_overlapFilling_eq i n) a)

/-- The preceding-stage component factors through the genuine original
regular family, with no assumed coordinate description of its homology. -/
theorem originalAttachmentLeftHomologyMap_apply_from_regular
    (s : Finset Puncture) (i : Puncture) (n : ℕ) (a : OverlapHomology i n) :
    originalAttachmentLeftHomologyMap s i n a =
      (singularHomologyMap (originalRegularToStage s) n
        (singularHomologyMap (overlapToRegularFamily i) n a),
        -singularHomologyMap (overlapToFilling i) n a) := by
  rw [originalAttachmentLeftHomologyMap_apply]
  apply Prod.ext
  · have h := congrArg (fun f : C(RegularOverlap i, partialPatch s) =>
        singularHomologyMap f n) (originalRegularToStage_overlap s i)
    rw [singularHomologyMap_comp] at h
    exact (LinearMap.congr_fun h a).symm
  · rfl

/-- The map into the enlarged stage is precisely the sum of the actual
preceding-stage inclusion and the original filling inclusion. -/
@[simp] theorem originalAttachmentRightHomologyMap_apply
    (s : Finset Puncture) (i : Puncture) (n : ℕ)
    (a : StageHomology s n × OriginalFillingHomology i n) :
    originalAttachmentRightHomologyMap s i n a =
      singularHomologyMap (previousStageInclusion s i) n a.1 +
        singularHomologyMap (originalFillingToStage s i) n a.2 := by
  change previousStageHomologyMap s i n a.1 +
    fillingStageHomologyMap s i n ((originalFillingHomologyEquiv i n).symm a.2) = _
  apply congrArg₂ (· + ·)
  · rfl
  · rw [originalFillingHomologyEquiv_symm_apply]
    exact (LinearMap.congr_fun (singularHomologyMap_comp
      (originalPatchHomeomorph (some i) : C(localPiece (some i), liftedPatch (some i)))
      (fillingStageInclusion s i) n) a.2).symm

theorem originalAttachment_exact_at_pair
    (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) (n : ℕ) :
    Function.Exact (originalAttachmentLeftHomologyMap s i n)
      (originalAttachmentRightHomologyMap s i n) := by
  apply exact_of_linearEquiv_squares (attachmentLeftHomologyMap s i n)
    (attachmentRightHomologyMap s i n) _ _ (LinearEquiv.refl ℤ _)
    (originalAttachmentPairEquiv s i n) (LinearEquiv.refl ℤ _)
    _ _ (attachment_exact_at_pair s i hi n)
  · apply LinearMap.ext
    intro a
    rfl
  · simpa using originalAttachmentRightHomologyMap_comparison s i n

theorem originalAttachment_exact_at_intersection
    (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) (n : ℕ) :
    Function.Exact (attachmentConnectingHomomorphism s i hi n)
      (originalAttachmentLeftHomologyMap s i n) := by
  apply exact_of_linearEquiv_squares (attachmentConnectingHomomorphism s i hi n)
    (attachmentLeftHomologyMap s i n) _ _ (LinearEquiv.refl ℤ _)
    (LinearEquiv.refl ℤ _) (originalAttachmentPairEquiv s i n)
    _ _ (attachment_exact_at_intersection s i hi n)
  · simp
  · apply LinearMap.ext
    intro a
    rfl

theorem originalAttachment_exact_at_ambient
    (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) (n : ℕ) :
    Function.Exact (originalAttachmentRightHomologyMap s i (n + 1))
      (attachmentConnectingHomomorphism s i hi n) := by
  apply exact_of_linearEquiv_squares (attachmentRightHomologyMap s i (n + 1))
    (attachmentConnectingHomomorphism s i hi n) _ _
    (originalAttachmentPairEquiv s i (n + 1)) (LinearEquiv.refl ℤ _)
    (LinearEquiv.refl ℤ _) _ _ (attachment_exact_at_ambient s i hi n)
  · simpa using originalAttachmentRightHomologyMap_comparison s i (n + 1)
  · simp

theorem originalAttachmentRightHomologyMap_zero_surjective
    (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) :
    Function.Surjective (originalAttachmentRightHomologyMap s i 0) :=
  (attachmentRightHomologyMap_zero_surjective s i hi).comp
    (originalAttachmentPairEquiv s i 0).symm.surjective

/-- The complete actual attachment sequence in original filling
coordinates, ready for separate geometric evaluation of the inclusion maps. -/
theorem originalAttachment_mayerVietoris_exact
    (s : Finset Puncture) (i : Puncture) (hi : i ∉ s) (n : ℕ) :
    Function.Exact (attachmentConnectingHomomorphism s i hi n)
        (originalAttachmentLeftHomologyMap s i n) ∧
      Function.Exact (originalAttachmentLeftHomologyMap s i n)
        (originalAttachmentRightHomologyMap s i n) ∧
      Function.Exact (originalAttachmentRightHomologyMap s i (n + 1))
        (attachmentConnectingHomomorphism s i hi n) :=
  ⟨originalAttachment_exact_at_intersection s i hi n,
    originalAttachment_exact_at_pair s i hi n, originalAttachment_exact_at_ambient s i hi n⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
