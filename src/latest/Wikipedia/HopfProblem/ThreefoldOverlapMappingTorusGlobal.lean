import Wikipedia.HopfProblem.ThreefoldHomologyGluingOriginalPieces

/-!
# Literal original-piece coordinates on the global overlaps

The intersection of the regular patch and a filling patch is homeomorphic
to the full punctured part of the original filling.  Both comparison maps
are the original gluing maps, and their compositions with the two ambient
inclusions agree exactly.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus

open SpecialPeriods SpecialPeriods.Threefold SpecialPeriods.Threefold.Homology

/-- The full part of an original filling meeting the regular base. -/
abbrev PuncturedPiece (i : Puncture) :=
  {x : localPiece (some i) // localProjectionToBase (some i) x ∈ regularPatch}

theorem inclusion_mem_regular_iff (i : Puncture) (x : localPiece (some i)) :
    inclusion (some i) x ∈ liftedPatch none ↔
      localProjectionToBase (some i) x ∈ regularPatch := by
  change projection (inclusion (some i) x) ∈ regularPatch ↔ _
  rw [projection_inclusion]

/-- The actual full overlap written in original filling coordinates. -/
def overlapPieceHomeomorph (i : Puncture) : RegularOverlap i ≃ₜ PuncturedPiece i where
  toFun x := ⟨overlapToFilling i x, by
    apply (inclusion_mem_regular_iff i _).mp
    rw [inclusion_overlapToFilling]
    exact x.property.1⟩
  invFun x := ⟨inclusion (some i) x.val,
    (inclusion_mem_regular_iff i x.val).mpr x.property,
    (originalPatchHomeomorph (some i) x.val).property⟩
  left_inv x := Subtype.ext (inclusion_overlapToFilling i x)
  right_inv x := by
    apply Subtype.ext
    apply (inclusion_openEmbedding (some i)).injective
    exact inclusion_overlapToFilling i _
  continuous_toFun := (overlapToFilling i).continuous.subtype_mk _
  continuous_invFun := ((inclusion_openEmbedding (some i)).continuous.comp
    continuous_subtype_val).subtype_mk _

@[simp] theorem overlapPieceHomeomorph_val (i : Puncture) (x : RegularOverlap i) :
    (overlapPieceHomeomorph i x).val = overlapToFilling i x := rfl

@[simp] theorem overlapPieceHomeomorph_symm_val (i : Puncture) (x : PuncturedPiece i) :
    ((overlapPieceHomeomorph i).symm x : Space) = inclusion (some i) x.val := rfl

/-- The literal inclusion of the punctured part into its original filling. -/
def puncturedPieceInclusion (i : Puncture) : C(PuncturedPiece i, localPiece (some i)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The original analytic overlap, viewed only as a continuous map. -/
def puncturedPieceToRegular (i : Puncture) : C(PuncturedPiece i, SpecialRegularFamily) :=
  (overlapToRegularFamily i).comp
    ((overlapPieceHomeomorph i).symm : C(PuncturedPiece i, RegularOverlap i))

theorem overlapToFilling_symm (i : Puncture) :
    (overlapToFilling i).comp
        ((overlapPieceHomeomorph i).symm : C(PuncturedPiece i, RegularOverlap i)) =
      puncturedPieceInclusion i := by
  apply ContinuousMap.ext
  intro x
  exact congrArg Subtype.val ((overlapPieceHomeomorph i).apply_symm_apply x)

theorem puncturedPieceToRegular_inclusion (i : Puncture) (x : PuncturedPiece i) :
    inclusion none (puncturedPieceToRegular i x) = inclusion (some i) x.val :=
  inclusion_overlapToRegularFamily i ((overlapPieceHomeomorph i).symm x)

theorem puncturedPieceToRegular_ambient (i : Puncture) :
    originalRegularInclusion.comp (puncturedPieceToRegular i) =
      (originalPieceInclusion (some i)).comp (puncturedPieceInclusion i) := by
  apply ContinuousMap.ext
  exact puncturedPieceToRegular_inclusion i

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus
