import Wikipedia.HopfProblem.ThreefoldHomologyGluingOriginalSequence

/-!
# The first attachment sequence in the original threefold pieces

The empty stage is identified with the actual original regular period
family. Thus the first attachment's pair term consists literally of the
singular homology of that family and of the original new filling. The
overlap map is their actual signed pair of induced inclusion maps. The
connecting map remains the previously constructed singular connecting
homomorphism of the genuine attachment cover.
-/

noncomputable section

open Set
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- Replace the empty-stage factor by the original regular family's
actual homology, using the canonical integral module on the product. -/
def initialAttachmentPairEquiv (i : Puncture) (n : ℕ) :
    (StageHomology ∅ n × OriginalFillingHomology i n) ≃ₗ[ℤ]
      (SingularHomology SpecialRegularFamily n × SingularHomology (localPiece (some i)) n) :=
  ((initialStageHomologyEquiv n).toAddEquiv.prodCongr
    (AddEquiv.refl (OriginalFillingHomology i n))).toIntLinearEquiv

@[simp] theorem initialAttachmentPairEquiv_apply (i : Puncture) (n : ℕ)
    (a : StageHomology ∅ n × OriginalFillingHomology i n) :
    initialAttachmentPairEquiv i n a = (initialStageHomologyEquiv n a.1, a.2) := rfl

@[simp] theorem initialAttachmentPairEquiv_symm_apply (i : Puncture) (n : ℕ)
    (a : SingularHomology SpecialRegularFamily n × SingularHomology (localPiece (some i)) n) :
    (initialAttachmentPairEquiv i n).symm a =
      ((initialStageHomologyEquiv n).symm a.1, a.2) := rfl

/-- The actual signed overlap map to the original regular family and
the original filling in the first attachment. -/
def initialAttachmentLeftHomologyMap (i : Puncture) (n : ℕ) :
    OverlapHomology i n →ₗ[ℤ]
      (SingularHomology SpecialRegularFamily n × SingularHomology (localPiece (some i)) n) :=
  (initialAttachmentPairEquiv i n).toLinearMap.comp
    (originalAttachmentLeftHomologyMap ∅ i n)

/-- The actual sum map from those original pieces into the enlarged stage. -/
def initialAttachmentRightHomologyMap (i : Puncture) (n : ℕ) :
    (SingularHomology SpecialRegularFamily n × SingularHomology (localPiece (some i)) n)
      →ₗ[ℤ] StageHomology (insert i ∅) n :=
  (originalAttachmentRightHomologyMap ∅ i n).comp
    (initialAttachmentPairEquiv i n).symm.toLinearMap

/-- The genuine attachment connecting map, unchanged by relabelling
the pair term in the sequence. -/
abbrev initialAttachmentConnectingHomomorphism (i : Puncture) (n : ℕ) :
    StageHomology (insert i ∅) (n + 1) →ₗ[ℤ] OverlapHomology i n :=
  attachmentConnectingHomomorphism ∅ i (Finset.notMem_empty i) n

@[simp] theorem initialAttachmentLeftHomologyMap_apply (i : Puncture) (n : ℕ)
    (a : OverlapHomology i n) :
    initialAttachmentLeftHomologyMap i n a =
      (singularHomologyMap (overlapToRegularFamily i) n a,
        -singularHomologyMap (overlapToFilling i) n a) := by
  change initialAttachmentPairEquiv i n (originalAttachmentLeftHomologyMap ∅ i n a) = _
  rw [originalAttachmentLeftHomologyMap_apply, initialAttachmentPairEquiv_apply]
  apply Prod.ext
  · exact LinearMap.congr_fun (initialStageHomologyEquiv_overlap i n) a
  · rfl

/-- The sum map is induced by the two literal original-piece inclusions,
not by arbitrarily chosen homology coordinates. -/
@[simp] theorem initialAttachmentRightHomologyMap_apply (i : Puncture) (n : ℕ)
    (a : SingularHomology SpecialRegularFamily n × SingularHomology (localPiece (some i)) n) :
    initialAttachmentRightHomologyMap i n a =
      singularHomologyMap (originalRegularToStage (insert i ∅)) n a.1 +
        singularHomologyMap (originalFillingToStage ∅ i) n a.2 := by
  change originalAttachmentRightHomologyMap ∅ i n ((initialAttachmentPairEquiv i n).symm a) = _
  rw [initialAttachmentPairEquiv_symm_apply, originalAttachmentRightHomologyMap_apply,
    initialStageHomologyEquiv_symm_apply]
  apply congrArg₂ (· + ·)
  · have he := singularHomologyMap_comp
      (regularStageHomeomorph : C(SpecialRegularFamily, partialPatch ∅))
      (previousStageInclusion ∅ i) n
    have hc : (previousStageInclusion ∅ i).comp
        (regularStageHomeomorph : C(SpecialRegularFamily, partialPatch ∅)) =
          originalRegularToStage (insert i ∅) := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      exact regularStageHomeomorph_val x
    rw [hc] at he
    exact (LinearMap.congr_fun he a.1).symm
  · rfl

theorem initialAttachmentRightHomologyMap_comparison (i : Puncture) (n : ℕ) :
    (initialAttachmentRightHomologyMap i n).comp
        (initialAttachmentPairEquiv i n).toLinearMap =
      originalAttachmentRightHomologyMap ∅ i n := by
  apply LinearMap.ext
  intro a
  change originalAttachmentRightHomologyMap ∅ i n
    ((initialAttachmentPairEquiv i n).symm (initialAttachmentPairEquiv i n a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Exactness at the literal pair of original-piece homology groups. -/
theorem initialAttachment_exact_at_pair (i : Puncture) (n : ℕ) :
    Function.Exact (initialAttachmentLeftHomologyMap i n)
      (initialAttachmentRightHomologyMap i n) := by
  apply exact_of_linearEquiv_squares (originalAttachmentLeftHomologyMap ∅ i n)
    (originalAttachmentRightHomologyMap ∅ i n) _ _ (LinearEquiv.refl ℤ _)
    (initialAttachmentPairEquiv i n) (LinearEquiv.refl ℤ _)
    _ _ (originalAttachment_exact_at_pair ∅ i (Finset.notMem_empty i) n)
  · apply LinearMap.ext
    intro a
    rfl
  · apply LinearMap.ext
    intro a
    exact LinearMap.congr_fun (initialAttachmentRightHomologyMap_comparison i n) a

/-- Exactness at the homology of the full actual regular/filling overlap. -/
theorem initialAttachment_exact_at_intersection (i : Puncture) (n : ℕ) :
    Function.Exact (initialAttachmentConnectingHomomorphism i n)
      (initialAttachmentLeftHomologyMap i n) := by
  apply exact_of_linearEquiv_squares
    (attachmentConnectingHomomorphism ∅ i (Finset.notMem_empty i) n)
    (originalAttachmentLeftHomologyMap ∅ i n) _ _ (LinearEquiv.refl ℤ _)
    (LinearEquiv.refl ℤ _) (initialAttachmentPairEquiv i n)
    _ _ (originalAttachment_exact_at_intersection ∅ i (Finset.notMem_empty i) n)
  · apply LinearMap.ext
    intro a
    rfl
  · apply LinearMap.ext
    intro a
    rfl

/-- Exactness at every positive-degree homology group of the first stage. -/
theorem initialAttachment_exact_at_ambient (i : Puncture) (n : ℕ) :
    Function.Exact (initialAttachmentRightHomologyMap i (n + 1))
      (initialAttachmentConnectingHomomorphism i n) := by
  apply exact_of_linearEquiv_squares (originalAttachmentRightHomologyMap ∅ i (n + 1))
    (attachmentConnectingHomomorphism ∅ i (Finset.notMem_empty i) n) _ _
    (initialAttachmentPairEquiv i (n + 1)) (LinearEquiv.refl ℤ _)
    (LinearEquiv.refl ℤ _) _ _
    (originalAttachment_exact_at_ambient ∅ i (Finset.notMem_empty i) n)
  · apply LinearMap.ext
    intro a
    exact LinearMap.congr_fun (initialAttachmentRightHomologyMap_comparison i (n + 1)) a
  · apply LinearMap.ext
    intro a
    rfl

theorem initialAttachmentRightHomologyMap_zero_surjective (i : Puncture) :
    Function.Surjective (initialAttachmentRightHomologyMap i 0) :=
  (originalAttachmentRightHomologyMap_zero_surjective ∅ i (Finset.notMem_empty i)).comp
    (initialAttachmentPairEquiv i 0).symm.surjective

/-- The actual first-attachment Mayer–Vietoris sequence, with the regular
family and filling appearing in their original geometric coordinates. -/
theorem initialAttachment_mayerVietoris_exact (i : Puncture) (n : ℕ) :
    Function.Exact (initialAttachmentConnectingHomomorphism i n)
        (initialAttachmentLeftHomologyMap i n) ∧
      Function.Exact (initialAttachmentLeftHomologyMap i n)
        (initialAttachmentRightHomologyMap i n) ∧
      Function.Exact (initialAttachmentRightHomologyMap i (n + 1))
        (initialAttachmentConnectingHomomorphism i n) :=
  ⟨initialAttachment_exact_at_intersection i n, initialAttachment_exact_at_pair i n,
    initialAttachment_exact_at_ambient i n⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
