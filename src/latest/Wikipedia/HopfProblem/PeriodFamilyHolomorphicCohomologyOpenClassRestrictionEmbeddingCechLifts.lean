import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingCechBasic
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSplittingLocal

/-!
# Original local extension sections after open-embedding restriction

Restrict the original local degree-one extension sections to the images of
the actual inverse-image opens. Their projected degrees and their original
later-minus-earlier differences remain literal native section identities.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.EmbeddingCech

open HolomorphicFunctionSheaf.SphereH1
open HolomorphicPicard.CechExtension

variable {T X : TopCat.{0}} (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)
  {F : TopCat.Sheaf AddCommGrpCat.{0} X} {ι : Type} {U : ι → Opens X}
  (c : CechOneCocycle F U)

/-- The literal restriction of the original local extension section to its
actual inverse-image cover open, in the original restricted extension sheaf. -/
def restrictedLocalSection (i : ι) :
    Section ((Embedding.restriction f hf).obj (extensionSheaf c)) (restrictedCover f U i) :=
  res (extensionSheaf c) (Embedding.imagePreimage_le f hf (U i)) (localDegreeOneSection c i)

/-- Its original degree projection is the original constant-one section on
the actual image open; no integer endpoint isomorphism is required. -/
theorem restrictedLocalSection_projection (i : ι) :
    ((Embedding.restriction f hf).map (projection c)).hom.app
        (op (restrictedCover f U i)) (restrictedLocalSection f hf c i) =
      (degreeUnit X).app (op ((Embedding.openImage f hf).obj (restrictedCover f U i)))
        (ULift.up (1 : ℤ)) := by
  change (projection c).hom.app
      (op ((Embedding.openImage f hf).obj (restrictedCover f U i)))
      (res (extensionSheaf c) (Embedding.imagePreimage_le f hf (U i))
        (localDegreeOneSection c i)) = _
  rw [← res_map, projection_localDegreeOneSection, res_degreeUnit]

/-- The restricted local sections retain the original second-minus-first
Čech difference, with the genuine restricted coefficient inclusion. -/
theorem restrictedLocalSection_difference (i j : ι) :
    res ((Embedding.restriction f hf).obj (extensionSheaf c)) inf_le_right
        (restrictedLocalSection f hf c j) -
      res ((Embedding.restriction f hf).obj (extensionSheaf c)) inf_le_left
        (restrictedLocalSection f hf c i) =
      ((Embedding.restriction f hf).map (inclusion c)).hom.app
        (op (restrictedCover f U i ⊓ restrictedCover f U j))
          ((restrictedCocycle f hf c).value i j) := by
  have h := congrArg (res (extensionSheaf c) (Embedding.imagePreimage_le f hf (U i ⊓ U j)))
    (localDegreeOneSection_difference c i j)
  let ri : restrictedCover f U i ⊓ restrictedCover f U j ⟶ restrictedCover f U i :=
    homOfLE inf_le_left
  let rj : restrictedCover f U i ⊓ restrictedCover f U j ⟶ restrictedCover f U j :=
    homOfLE inf_le_right
  change res (extensionSheaf c) ((Embedding.openImage f hf).map rj).le
      (res (extensionSheaf c) (Embedding.imagePreimage_le f hf (U j))
        (localDegreeOneSection c j)) -
    res (extensionSheaf c) ((Embedding.openImage f hf).map ri).le
      (res (extensionSheaf c) (Embedding.imagePreimage_le f hf (U i))
        (localDegreeOneSection c i)) =
    (inclusion c).hom.app
      (op ((Embedding.openImage f hf).obj (Embedding.preimageOpen f (U i ⊓ U j))))
        (res F (Embedding.imagePreimage_le f hf (U i ⊓ U j)) (c.value i j))
  simp only [map_sub, res_trans, res_map] at h
  simp only [res_trans]
  exact h

end OpenClassRestriction.EmbeddingCech
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
