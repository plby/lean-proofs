import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluing
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Actual singular homology in the original threefold pieces

The attachment stages and full inverse-image patches are related to the
original regular family, filling spaces, and glued threefold by their actual
homeomorphisms.  These induce equivalences on integral singular homology in
every degree.  The overlap maps below are obtained by the inverse patch
homeomorphisms, and their compositions with the original inclusions are the
literal ambient subtype maps.
-/

noncomputable section

open Set
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The original patch homeomorphism, with the geometric local-piece and
full inverse-image patch types made explicit. -/
def originalPatchHomeomorph (i : Index) : localPiece i ≃ₜ liftedPatch i :=
  gluingData.patchHomeomorph i

@[simp] theorem originalPatchHomeomorph_val (i : Index) (x : localPiece i) :
    (originalPatchHomeomorph i x : Space) = inclusion i x := rfl

/-- The regular specialization has the native quotient-family type. -/
def originalRegularPatchHomeomorph : SpecialRegularFamily ≃ₜ liftedPatch none :=
  originalPatchHomeomorph none

/-- The initial stage has the actual integral singular homology of the
original regular quotient family. -/
def initialStageHomologyEquiv (n : ℕ) :
    SingularHomology (partialPatch ∅) n ≃ₗ[ℤ]
      SingularHomology SpecialRegularFamily n :=
  homeomorphHomologyEquiv regularStageHomeomorph.symm n

@[simp] theorem initialStageHomologyEquiv_toLinearMap (n : ℕ) :
    (initialStageHomologyEquiv n).toLinearMap =
      singularHomologyMap
        (regularStageHomeomorph.symm : C(partialPatch ∅, SpecialRegularFamily)) n := rfl

@[simp] theorem initialStageHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (partialPatch ∅) n) :
    initialStageHomologyEquiv n a = singularHomologyMap
      (regularStageHomeomorph.symm : C(partialPatch ∅, SpecialRegularFamily)) n a := rfl

@[simp] theorem initialStageHomologyEquiv_symm_apply (n : ℕ)
    (a : SingularHomology SpecialRegularFamily n) :
    (initialStageHomologyEquiv n).symm a = singularHomologyMap
      (regularStageHomeomorph : C(SpecialRegularFamily, partialPatch ∅)) n a := rfl

/-- Flattening the stage containing all fillings gives the homology of the
actual constructed threefold. -/
def fullStageHomologyEquiv (n : ℕ) :
    SingularHomology (partialPatch Finset.univ) n ≃ₗ[ℤ] SingularHomology Space n :=
  homeomorphHomologyEquiv fullStageHomeomorph n

@[simp] theorem fullStageHomologyEquiv_toLinearMap (n : ℕ) :
    (fullStageHomologyEquiv n).toLinearMap =
      singularHomologyMap
        (fullStageHomeomorph : C(partialPatch Finset.univ, Space)) n := rfl

@[simp] theorem fullStageHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (partialPatch Finset.univ) n) :
    fullStageHomologyEquiv n a =
      singularHomologyMap
        (fullStageHomeomorph : C(partialPatch Finset.univ, Space)) n a := rfl

theorem fullStageHomeomorph_toContinuousMap :
    (fullStageHomeomorph : C(partialPatch Finset.univ, Space)) =
      subtypeInclusion (partialPatch Finset.univ : Set Space) := rfl

@[simp] theorem fullStageHomologyEquiv_symm_apply (n : ℕ)
    (a : SingularHomology Space n) :
    (fullStageHomologyEquiv n).symm a = singularHomologyMap
      (fullStageHomeomorph.symm : C(Space, partialPatch Finset.univ)) n a := rfl

/-- Any of the three actual fillings can be attached last. -/
def terminalStageHomologyEquiv (i : Puncture) (n : ℕ) :
    SingularHomology (partialPatch (insert i (Finset.univ.erase i))) n ≃ₗ[ℤ]
      SingularHomology Space n :=
  homeomorphHomologyEquiv (terminalStageHomeomorph i) n

@[simp] theorem terminalStageHomologyEquiv_toLinearMap (i : Puncture) (n : ℕ) :
    (terminalStageHomologyEquiv i n).toLinearMap = singularHomologyMap
      (terminalStageHomeomorph i :
        C(partialPatch (insert i (Finset.univ.erase i)), Space)) n := rfl

@[simp] theorem terminalStageHomologyEquiv_apply (i : Puncture) (n : ℕ)
    (a : SingularHomology (partialPatch (insert i (Finset.univ.erase i))) n) :
    terminalStageHomologyEquiv i n a = singularHomologyMap
      (terminalStageHomeomorph i :
        C(partialPatch (insert i (Finset.univ.erase i)), Space)) n a := rfl

theorem terminalStageHomeomorph_toContinuousMap (i : Puncture) :
    (terminalStageHomeomorph i :
      C(partialPatch (insert i (Finset.univ.erase i)), Space)) =
        subtypeInclusion (partialPatch (insert i (Finset.univ.erase i)) : Set Space) := rfl

@[simp] theorem terminalStageHomologyEquiv_symm_apply (i : Puncture) (n : ℕ)
    (a : SingularHomology Space n) :
    (terminalStageHomologyEquiv i n).symm a = singularHomologyMap
      ((terminalStageHomeomorph i).symm :
        C(Space, partialPatch (insert i (Finset.univ.erase i)))) n a := rfl

/-- The full filling patch has the homology of its original geometric
filling, not merely of a space with the same abstract homology. -/
def originalFillingHomologyEquiv (i : Puncture) (n : ℕ) :
    SingularHomology (liftedPatch (some i)) n ≃ₗ[ℤ]
      SingularHomology (localPiece (some i)) n :=
  homeomorphHomologyEquiv (originalPatchHomeomorph (some i)).symm n

@[simp] theorem originalFillingHomologyEquiv_toLinearMap (i : Puncture) (n : ℕ) :
    (originalFillingHomologyEquiv i n).toLinearMap = singularHomologyMap
      ((originalPatchHomeomorph (some i)).symm :
        C(liftedPatch (some i), localPiece (some i))) n := rfl

@[simp] theorem originalFillingHomologyEquiv_apply (i : Puncture) (n : ℕ)
    (a : SingularHomology (liftedPatch (some i)) n) :
    originalFillingHomologyEquiv i n a = singularHomologyMap
      ((originalPatchHomeomorph (some i)).symm :
        C(liftedPatch (some i), localPiece (some i))) n a := rfl

@[simp] theorem originalFillingHomologyEquiv_symm_apply (i : Puncture) (n : ℕ)
    (a : SingularHomology (localPiece (some i)) n) :
    (originalFillingHomologyEquiv i n).symm a = singularHomologyMap
      (originalPatchHomeomorph (some i) :
        C(localPiece (some i), liftedPatch (some i))) n a := rfl

/-- The genuine inclusion of an original local piece into the threefold. -/
def originalPieceInclusion (i : Index) : C(localPiece i, Space) :=
  ⟨inclusion i, (inclusion_openEmbedding i).continuous⟩

@[simp] theorem originalPieceInclusion_apply (i : Index) (x : localPiece i) :
    originalPieceInclusion i x = inclusion i x := rfl

/-- The same original inclusion, with its native regular-family source type. -/
def originalRegularInclusion : C(SpecialRegularFamily, Space) :=
  originalPieceInclusion none

@[simp] theorem originalRegularInclusion_apply (x : SpecialRegularFamily) :
    originalRegularInclusion x = inclusion none x := rfl

/-- Express the actual full overlap in the original regular-family coordinates. -/
def overlapToRegularFamily (i : Puncture) : C(RegularOverlap i, SpecialRegularFamily) :=
  (originalRegularPatchHomeomorph.symm :
    C(liftedPatch none, SpecialRegularFamily)).comp
    (ContinuousMap.inclusion (Set.inter_subset_left :
      (liftedPatch none : Set Space) ∩ liftedPatch (some i) ⊆ liftedPatch none))

/-- Express the same actual full overlap in the original filling coordinates. -/
def overlapToFilling (i : Puncture) : C(RegularOverlap i, localPiece (some i)) :=
  ((originalPatchHomeomorph (some i)).symm :
    C(liftedPatch (some i), localPiece (some i))).comp (overlapFillingInclusion i)

theorem overlapToFilling_eq (i : Puncture) :
    overlapToFilling i =
      ((originalPatchHomeomorph (some i)).symm :
        C(liftedPatch (some i), localPiece (some i))).comp
          (overlapFillingInclusion i) := rfl

@[simp] theorem inclusion_overlapToRegularFamily (i : Puncture) (x : RegularOverlap i) :
    inclusion none (overlapToRegularFamily i x) = x.val :=
  congrArg Subtype.val (originalRegularPatchHomeomorph.apply_symm_apply
    ⟨x.val, x.property.1⟩)

@[simp] theorem inclusion_overlapToFilling (i : Puncture) (x : RegularOverlap i) :
    inclusion (some i) (overlapToFilling i x) = x.val :=
  congrArg Subtype.val ((originalPatchHomeomorph (some i)).apply_symm_apply
    ⟨x.val, x.property.2⟩)

theorem originalPieceInclusion_overlapToRegularFamily (i : Puncture) :
    originalRegularInclusion.comp (overlapToRegularFamily i) =
      subtypeInclusion ((liftedPatch none : Set Space) ∩ liftedPatch (some i)) := by
  apply ContinuousMap.ext
  intro x
  exact inclusion_overlapToRegularFamily i x

theorem originalPieceInclusion_overlapToFilling (i : Puncture) :
    (originalPieceInclusion (some i)).comp (overlapToFilling i) =
      subtypeInclusion ((liftedPatch none : Set Space) ∩ liftedPatch (some i)) := by
  apply ContinuousMap.ext
  intro x
  exact inclusion_overlapToFilling i x

/-- The original regular quotient family includes into every attachment stage. -/
def originalRegularToStage (s : Finset Puncture) : C(SpecialRegularFamily, partialPatch s) :=
  ⟨fun x => ⟨inclusion none x,
      regular_le_partialPatch s (originalPatchHomeomorph none x).property⟩,
    (inclusion_openEmbedding none).continuous.subtype_mk _⟩

@[simp] theorem originalRegularToStage_val (s : Finset Puncture)
    (x : SpecialRegularFamily) :
    (originalRegularToStage s x : Space) = inclusion none x := rfl

theorem originalRegularToStage_empty :
    originalRegularToStage ∅ =
      (regularStageHomeomorph : C(SpecialRegularFamily, partialPatch ∅)) := rfl

/-- The original filling includes into the stage obtained by attaching it. -/
def originalFillingToStage (s : Finset Puncture) (i : Puncture) :
    C(localPiece (some i), partialPatch (insert i s)) :=
  (fillingStageInclusion s i).comp
    (originalPatchHomeomorph (some i) : C(localPiece (some i), liftedPatch (some i)))

@[simp] theorem originalFillingToStage_val (s : Finset Puncture) (i : Puncture)
    (x : localPiece (some i)) :
    (originalFillingToStage s i x : Space) = inclusion (some i) x := rfl

theorem originalRegularToStage_overlap (s : Finset Puncture) (i : Puncture) :
    (originalRegularToStage s).comp (overlapToRegularFamily i) =
      overlapPreviousInclusion s i := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact inclusion_overlapToRegularFamily i x

theorem originalFillingToStage_overlap (s : Finset Puncture) (i : Puncture) :
    (originalFillingToStage s i).comp (overlapToFilling i) =
      (fillingStageInclusion s i).comp (overlapFillingInclusion i) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact inclusion_overlapToFilling i x

theorem originalFillingToStage_overlap_previous (s : Finset Puncture) (i : Puncture) :
    (originalFillingToStage s i).comp (overlapToFilling i) =
      (previousStageInclusion s i).comp (overlapPreviousInclusion s i) := by
  rw [originalFillingToStage_overlap]
  rfl

theorem originalFillingToStage_patchInverse (s : Finset Puncture) (i : Puncture) :
    (originalFillingToStage s i).comp
        ((originalPatchHomeomorph (some i)).symm :
          C(liftedPatch (some i), localPiece (some i))) = fillingStageInclusion s i := by
  apply ContinuousMap.ext
  intro x
  change fillingStageInclusion s i
    (originalPatchHomeomorph (some i) ((originalPatchHomeomorph (some i)).symm x)) = _
  rw [Homeomorph.apply_symm_apply]

theorem initialStageInverse_overlap (i : Puncture) :
    (regularStageHomeomorph.symm : C(partialPatch ∅, SpecialRegularFamily)).comp
        (overlapPreviousInclusion ∅ i) = overlapToRegularFamily i := rfl

theorem originalRegularToStage_ambient (s : Finset Puncture) :
    (subtypeInclusion (partialPatch s : Set Space)).comp (originalRegularToStage s) =
      originalRegularInclusion := rfl

theorem originalFillingToStage_ambient (s : Finset Puncture) (i : Puncture) :
    (subtypeInclusion (partialPatch (insert i s) : Set Space)).comp
        (originalFillingToStage s i) = originalPieceInclusion (some i) := rfl

/-- The overlap map in regular coordinates induces exactly the ambient
inclusion after applying the original regular-family inclusion. -/
theorem originalPieceInclusion_homology_overlapToRegularFamily (i : Puncture) (n : ℕ) :
    (singularHomologyMap originalRegularInclusion n).comp
        (singularHomologyMap (overlapToRegularFamily i) n) =
      singularHomologyMap
        (subtypeInclusion ((liftedPatch none : Set Space) ∩ liftedPatch (some i))) n := by
  rw [← singularHomologyMap_comp, originalPieceInclusion_overlapToRegularFamily]

theorem originalPieceInclusion_homology_overlapToFilling (i : Puncture) (n : ℕ) :
    (singularHomologyMap (originalPieceInclusion (some i)) n).comp
        (singularHomologyMap (overlapToFilling i) n) =
      singularHomologyMap
        (subtypeInclusion ((liftedPatch none : Set Space) ∩ liftedPatch (some i))) n := by
  rw [← singularHomologyMap_comp, originalPieceInclusion_overlapToFilling]

/-- The previous-stage overlap map factors through the original regular
family in actual singular homology, in every degree. -/
theorem originalRegularToStage_homology_overlap (s : Finset Puncture) (i : Puncture)
    (n : ℕ) :
    (singularHomologyMap (originalRegularToStage s) n).comp
        (singularHomologyMap (overlapToRegularFamily i) n) =
      singularHomologyMap (overlapPreviousInclusion s i) n := by
  rw [← singularHomologyMap_comp, originalRegularToStage_overlap]

theorem originalFillingToStage_homology_overlap (s : Finset Puncture) (i : Puncture)
    (n : ℕ) :
    (singularHomologyMap (originalFillingToStage s i) n).comp
        (singularHomologyMap (overlapToFilling i) n) =
      (singularHomologyMap (fillingStageInclusion s i) n).comp
        (singularHomologyMap (overlapFillingInclusion i) n) := by
  rw [← singularHomologyMap_comp, ← singularHomologyMap_comp,
    originalFillingToStage_overlap]

/-- The two original geometric descriptions of the overlap give the same
map into the attached stage, not just equal maps on selected generators. -/
theorem originalFillingToStage_homology_overlap_previous
    (s : Finset Puncture) (i : Puncture) (n : ℕ) :
    (singularHomologyMap (originalFillingToStage s i) n).comp
        (singularHomologyMap (overlapToFilling i) n) =
      (singularHomologyMap (previousStageInclusion s i) n).comp
        (singularHomologyMap (overlapPreviousInclusion s i) n) := by
  rw [← singularHomologyMap_comp, ← singularHomologyMap_comp,
    originalFillingToStage_overlap_previous]

/-- Transporting the initial overlap map gives its map to the actual
regular quotient family. -/
theorem initialStageHomologyEquiv_overlap (i : Puncture) (n : ℕ) :
    (initialStageHomologyEquiv n).toLinearMap.comp
        (singularHomologyMap (overlapPreviousInclusion ∅ i) n) =
      singularHomologyMap (overlapToRegularFamily i) n := by
  rw [initialStageHomologyEquiv_toLinearMap, ← singularHomologyMap_comp,
    initialStageInverse_overlap]

/-- Transporting the filling overlap map gives its map to the original filling. -/
theorem originalFillingHomologyEquiv_overlap (i : Puncture) (n : ℕ) :
    (originalFillingHomologyEquiv i n).toLinearMap.comp
        (singularHomologyMap (overlapFillingInclusion i) n) =
      singularHomologyMap (overlapToFilling i) n := by
  rw [originalFillingHomologyEquiv_toLinearMap, ← singularHomologyMap_comp,
    overlapToFilling_eq]

/-- The original inclusion of the regular family is inverse to the
initial-stage homology equivalence. -/
theorem initialStageHomologyEquiv_originalRegularToStage (n : ℕ) :
    (initialStageHomologyEquiv n).toLinearMap.comp
        (singularHomologyMap (originalRegularToStage ∅) n) =
      LinearMap.id := by
  apply LinearMap.ext
  intro a
  change initialStageHomologyEquiv n
    (singularHomologyMap (originalRegularToStage ∅) n a) = a
  rw [originalRegularToStage_empty, ← initialStageHomologyEquiv_symm_apply]
  exact (initialStageHomologyEquiv n).apply_symm_apply a

theorem originalRegularToStage_initialStageHomologyEquiv (n : ℕ) :
    (singularHomologyMap (originalRegularToStage ∅) n).comp
        (initialStageHomologyEquiv n).toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro a
  change singularHomologyMap (originalRegularToStage ∅) n
    (initialStageHomologyEquiv n a) = a
  rw [originalRegularToStage_empty, ← initialStageHomologyEquiv_symm_apply]
  exact (initialStageHomologyEquiv n).symm_apply_apply a

/-- The native filling-to-stage homology map becomes the literal patch
inclusion map under the actual patch equivalence. -/
theorem originalFillingToStage_homology_patchInverse
    (s : Finset Puncture) (i : Puncture) (n : ℕ) :
    (singularHomologyMap (originalFillingToStage s i) n).comp
        (originalFillingHomologyEquiv i n).toLinearMap =
      singularHomologyMap (fillingStageInclusion s i) n := by
  rw [originalFillingHomologyEquiv_toLinearMap, ← singularHomologyMap_comp,
    originalFillingToStage_patchInverse]

theorem originalRegularToStage_homology_ambient (s : Finset Puncture) (n : ℕ) :
    (singularHomologyMap (subtypeInclusion (partialPatch s : Set Space)) n).comp
        (singularHomologyMap (originalRegularToStage s) n) =
      singularHomologyMap originalRegularInclusion n := by
  rw [← singularHomologyMap_comp, originalRegularToStage_ambient]

theorem originalFillingToStage_homology_ambient
    (s : Finset Puncture) (i : Puncture) (n : ℕ) :
    (singularHomologyMap (subtypeInclusion (partialPatch (insert i s) : Set Space)) n).comp
        (singularHomologyMap (originalFillingToStage s i) n) =
      singularHomologyMap (originalPieceInclusion (some i)) n := by
  rw [← singularHomologyMap_comp, originalFillingToStage_ambient]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
