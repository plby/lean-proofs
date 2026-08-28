import Wikipedia.HopfProblem.OrbitPairSliceQuotient
import Wikipedia.HopfProblem.OrbitPairTrivializationFromProduct

/-!
# Local trivializations of the actual free orbit projection

The source and base are the already defined open subspaces of the
original threefold and its literal quotient. The resulting native
`Bundle.Trivialization`s cover the entire free quotient.
-/

noncomputable section

open Set Topology Bundle

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.chartedSpace

namespace SmoothOrbitCharacter

variable (F : SmoothOrbitCharacter)

def freeBase : TopologicalSpace.Opens freeOrbitLocus :=
  ⟨Subtype.val ⁻¹' (F.orbitImage : Set CircleOrbitSpace.OrbitSpace),
    F.orbitImage.isOpen.preimage continuous_subtype_val⟩

def freeBaseHomeomorph : F.freeBase ≃ₜ F.orbitImage where
  toFun y := ⟨y.val.val, y.property⟩
  invFun y := ⟨⟨y.val, F.orbitImage_subset_freeOrbitLocus y.property⟩, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem mem_freePreimage_iff (x : freeLocus) :
    freeOrbitProjection x ∈ F.freeBase ↔ x.val ∈ F.nonzeroSet := by
  change CircleOrbitSpace.quotientMap x.val ∈ F.orbitImage ↔ _
  exact Set.ext_iff.mp F.quotientMap_preimage_orbitImage x.val

def freePreimageHomeomorph :
    (freeOrbitProjection ⁻¹' (F.freeBase : Set freeOrbitLocus)) ≃ₜ F.nonzeroSet where
  toFun x := ⟨x.val.val, (F.mem_freePreimage_iff x.val).mp x.property⟩
  invFun x := ⟨⟨x.val, F.nonzeroSet_subset_freeLocus x.property⟩,
    (F.mem_freePreimage_iff _).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def freeProductHomeomorph :
    (freeOrbitProjection ⁻¹' (F.freeBase : Set freeOrbitLocus)) ≃ₜ F.freeBase × Circle :=
  F.freePreimageHomeomorph.trans
    (F.orbitProductHomeomorph.trans
      (Homeomorph.prodCongr F.freeBaseHomeomorph.symm (Homeomorph.refl Circle)))

theorem freeProductHomeomorph_fst
    (x : freeOrbitProjection ⁻¹' (F.freeBase : Set freeOrbitLocus)) :
    (F.freeProductHomeomorph x).1.val = freeOrbitProjection x.val := by
  apply Subtype.ext
  exact F.orbitProductHomeomorph_fst (F.freePreimageHomeomorph x)

/-- A native trivialization of the original free orbit projection. -/
def freeTrivialization [Nonempty freeLocus] : Trivialization Circle freeOrbitProjection :=
  trivializationFromProduct freeOrbitProjection freeOrbitProjection_continuous
    F.freeBase F.freeProductHomeomorph F.freeProductHomeomorph_fst

@[simp] theorem freeTrivialization_baseSet [Nonempty freeLocus] :
    F.freeTrivialization.baseSet = F.freeBase := rfl

end SmoothOrbitCharacter

/-- Unconditional local triviality, at every point of the actual free quotient. -/
theorem exists_freeOrbitTrivialization (y : freeOrbitLocus) :
    ∃ e : Trivialization Circle freeOrbitProjection, y ∈ e.baseSet := by
  obtain ⟨x, rfl⟩ := freeOrbitProjection_surjective y
  let : Nonempty freeLocus := ⟨x⟩
  obtain ⟨F, hF⟩ := exists_smoothOrbitCharacter x
  exact ⟨F.freeTrivialization, (F.mem_freePreimage_iff x).mpr hF⟩

def freeOrbitTrivializationAt (y : freeOrbitLocus) :
    Trivialization Circle freeOrbitProjection := (exists_freeOrbitTrivialization y).choose

theorem mem_freeOrbitTrivializationAt (y : freeOrbitLocus) :
    y ∈ (freeOrbitTrivializationAt y).baseSet := (exists_freeOrbitTrivialization y).choose_spec

end Wikipedia.HopfProblem.OrbitPair
