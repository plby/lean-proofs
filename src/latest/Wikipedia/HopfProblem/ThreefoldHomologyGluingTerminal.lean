import Wikipedia.HopfProblem.ThreefoldHomologyGluingOriginalSequence

/-!
# The terminal attachment sequence of the actual global threefold

Any of the three genuine fillings can be attached last. The proved full
stage homeomorphism identifies the resulting ambient homology with the
actual integral singular homology of the constructed threefold. The
incoming map remains the sum of literal geometric inclusion maps, and
the connecting map is transported from the actual singular sequence.
-/

noncomputable section

open Set
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The preceding-stage inclusion followed by the actual terminal-stage
homeomorphism is literally the inclusion into the global threefold. -/
theorem terminalStage_previousInclusion (i : Puncture) :
    (terminalStageHomeomorph i :
      C(partialPatch (insert i (Finset.univ.erase i)), Space)).comp
        (previousStageInclusion (Finset.univ.erase i) i) =
      subtypeInclusion (partialPatch (Finset.univ.erase i) : Set Space) := by
  apply ContinuousMap.ext
  intro x
  exact terminalStageHomeomorph_apply i
    (previousStageInclusion (Finset.univ.erase i) i x)

/-- The original filling inclusion followed by terminal flattening is
the actual inclusion of that local piece into the global threefold. -/
theorem terminalStage_originalFillingInclusion (i : Puncture) :
    (terminalStageHomeomorph i :
      C(partialPatch (insert i (Finset.univ.erase i)), Space)).comp
        (originalFillingToStage (Finset.univ.erase i) i) =
      originalPieceInclusion (some i) := by
  apply ContinuousMap.ext
  intro x
  exact (terminalStageHomeomorph_apply i
    (originalFillingToStage (Finset.univ.erase i) i x)).trans
      (originalFillingToStage_val (Finset.univ.erase i) i x)

/-- The signed overlap map for the last attachment, in original filling
coordinates and with the genuine preceding-stage homology. -/
abbrev terminalLeftHomologyMap (i : Puncture) (n : ℕ) :
    OverlapHomology i n →ₗ[ℤ]
      (StageHomology (Finset.univ.erase i) n × OriginalFillingHomology i n) :=
  originalAttachmentLeftHomologyMap (Finset.univ.erase i) i n

/-- The sum of actual inclusions into the actual global singular homology. -/
def terminalRightHomologyMap (i : Puncture) (n : ℕ) :
    (StageHomology (Finset.univ.erase i) n × OriginalFillingHomology i n) →ₗ[ℤ]
      SingularHomology Space n :=
  (terminalStageHomologyEquiv i n).toLinearMap.comp
    (originalAttachmentRightHomologyMap (Finset.univ.erase i) i n)

/-- The connecting homomorphism with domain the actual global
threefold homology, induced by the proved last-attachment sequence. -/
def terminalConnectingHomomorphism (i : Puncture) (n : ℕ) :
    SingularHomology Space (n + 1) →ₗ[ℤ] OverlapHomology i n :=
  (attachmentConnectingHomomorphism (Finset.univ.erase i) i
    (Finset.notMem_erase i Finset.univ) n).comp
      (terminalStageHomologyEquiv i (n + 1)).symm.toLinearMap

@[simp] theorem terminalLeftHomologyMap_apply (i : Puncture) (n : ℕ)
    (a : OverlapHomology i n) :
    terminalLeftHomologyMap i n a =
      (singularHomologyMap (originalRegularToStage (Finset.univ.erase i)) n
        (singularHomologyMap (overlapToRegularFamily i) n a),
        -singularHomologyMap (overlapToFilling i) n a) :=
  originalAttachmentLeftHomologyMap_apply_from_regular (Finset.univ.erase i) i n a

/-- Both summands are the genuine homology maps of the literal geometric
inclusions, not maps defined only by candidate integer matrices. -/
@[simp] theorem terminalRightHomologyMap_apply (i : Puncture) (n : ℕ)
    (a : StageHomology (Finset.univ.erase i) n × OriginalFillingHomology i n) :
    terminalRightHomologyMap i n a =
      singularHomologyMap
        (subtypeInclusion (partialPatch (Finset.univ.erase i) : Set Space)) n a.1 +
      singularHomologyMap (originalPieceInclusion (some i)) n a.2 := by
  change terminalStageHomologyEquiv i n
    (originalAttachmentRightHomologyMap (Finset.univ.erase i) i n a) = _
  simp only [originalAttachmentRightHomologyMap_apply, map_add,
    terminalStageHomologyEquiv_apply]
  apply congrArg₂ (· + ·)
  · rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, terminalStage_previousInclusion]
  · rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
      terminalStage_originalFillingInclusion]

theorem terminalConnectingHomomorphism_comparison (i : Puncture) (n : ℕ) :
    (terminalConnectingHomomorphism i n).comp
        (terminalStageHomologyEquiv i (n + 1)).toLinearMap =
      attachmentConnectingHomomorphism (Finset.univ.erase i) i
        (Finset.notMem_erase i Finset.univ) n := by
  apply LinearMap.ext
  intro a
  change attachmentConnectingHomomorphism (Finset.univ.erase i) i
    (Finset.notMem_erase i Finset.univ) n
    ((terminalStageHomologyEquiv i (n + 1)).symm (terminalStageHomologyEquiv i (n + 1) a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Exactness at the overlap homology in the genuine terminal sequence. -/
theorem terminal_exact_at_intersection (i : Puncture) (n : ℕ) :
    Function.Exact (terminalConnectingHomomorphism i n) (terminalLeftHomologyMap i n) := by
  apply exact_of_linearEquiv_squares
    (attachmentConnectingHomomorphism (Finset.univ.erase i) i
      (Finset.notMem_erase i Finset.univ) n)
    (originalAttachmentLeftHomologyMap (Finset.univ.erase i) i n) _ _
    (terminalStageHomologyEquiv i (n + 1)) (LinearEquiv.refl ℤ _) (LinearEquiv.refl ℤ _)
    _ _ (originalAttachment_exact_at_intersection (Finset.univ.erase i) i
      (Finset.notMem_erase i Finset.univ) n)
  · simpa using terminalConnectingHomomorphism_comparison i n
  · simp only [LinearEquiv.refl_toLinearMap, LinearMap.comp_id, LinearMap.id_comp]

/-- Exactness at the preceding-stage and original-filling pair. -/
theorem terminal_exact_at_pair (i : Puncture) (n : ℕ) :
    Function.Exact (terminalLeftHomologyMap i n) (terminalRightHomologyMap i n) := by
  apply exact_of_linearEquiv_squares
    (originalAttachmentLeftHomologyMap (Finset.univ.erase i) i n)
    (originalAttachmentRightHomologyMap (Finset.univ.erase i) i n) _ _
    (LinearEquiv.refl ℤ _) (LinearEquiv.refl ℤ _) (terminalStageHomologyEquiv i n)
    _ _ (originalAttachment_exact_at_pair (Finset.univ.erase i) i
      (Finset.notMem_erase i Finset.univ) n)
  · simp only [LinearEquiv.refl_toLinearMap, LinearMap.comp_id, LinearMap.id_comp]
  · simp only [LinearEquiv.refl_toLinearMap, LinearMap.comp_id, terminalRightHomologyMap]

/-- Exactness at the actual positive-degree singular homology of the
constructed global threefold. -/
theorem terminal_exact_at_ambient (i : Puncture) (n : ℕ) :
    Function.Exact (terminalRightHomologyMap i (n + 1))
      (terminalConnectingHomomorphism i n) := by
  apply exact_of_linearEquiv_squares
    (originalAttachmentRightHomologyMap (Finset.univ.erase i) i (n + 1))
    (attachmentConnectingHomomorphism (Finset.univ.erase i) i
      (Finset.notMem_erase i Finset.univ) n) _ _
    (LinearEquiv.refl ℤ _) (terminalStageHomologyEquiv i (n + 1)) (LinearEquiv.refl ℤ _)
    _ _ (originalAttachment_exact_at_ambient (Finset.univ.erase i) i
      (Finset.notMem_erase i Finset.univ) n)
  · simp only [LinearEquiv.refl_toLinearMap, LinearMap.comp_id, terminalRightHomologyMap]
  · simpa using terminalConnectingHomomorphism_comparison i n

theorem terminalRightHomologyMap_zero_surjective (i : Puncture) :
    Function.Surjective (terminalRightHomologyMap i 0) :=
  (terminalStageHomologyEquiv i 0).surjective.comp
    (originalAttachmentRightHomologyMap_zero_surjective (Finset.univ.erase i) i
      (Finset.notMem_erase i Finset.univ))

/-- The all-degree terminal Mayer–Vietoris sequence, whose ambient
term is literally the integral singular homology of the actual threefold. -/
theorem terminal_mayerVietoris_exact (i : Puncture) (n : ℕ) :
    Function.Exact (terminalConnectingHomomorphism i n) (terminalLeftHomologyMap i n) ∧
      Function.Exact (terminalLeftHomologyMap i n) (terminalRightHomologyMap i n) ∧
      Function.Exact (terminalRightHomologyMap i (n + 1))
        (terminalConnectingHomomorphism i n) :=
  ⟨terminal_exact_at_intersection i n, terminal_exact_at_pair i n,
    terminal_exact_at_ambient i n⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
