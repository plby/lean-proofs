import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingCechLifts
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingUnit
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingClass

/-!
# Actual Čech extension comparison along an open embedding

The restricted original local extension sections give an actual glued map
from the extension of the restricted cocycle to the exact restriction of the
original extension. The left endpoint is the identity, and the right endpoint
is the genuine constant-presheaf integer unit with its proved section formula.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.EmbeddingCech

open HolomorphicFunctionSheaf.SphereH1
open HolomorphicPicard.CechExtension

variable {T X : TopCat.{0}} (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)
  {F : TopCat.Sheaf AddCommGrpCat.{0} X} {ι : Type} {U : ι → Opens X}
  (c : CechOneCocycle F U) (hU : ∀ x : X, ∃ i : ι, x ∈ U i)

/-- The original local gluing construction compares the actual two extension sheaves. -/
def restrictedExtensionMap :
    extensionSheaf (restrictedCocycle f hf c) ⟶
      (Embedding.restriction f hf).obj (extensionSheaf c) :=
  comparison (restrictedCocycle f hf c) (restrictedCover_covers f hU)
    ((Embedding.restriction f hf).map (inclusion c)) (restrictedLocalSection f hf c)
    (restrictedLocalSection_difference f hf c)

/-- The actual restricted coefficient inclusion is the left endpoint of the comparison. -/
theorem inclusion_restrictedExtensionMap :
    inclusion (restrictedCocycle f hf c) ≫ restrictedExtensionMap f hf c hU =
      (Embedding.restriction f hf).map (inclusion c) :=
  inclusion_comparison (restrictedCocycle f hf c) (restrictedCover_covers f hU)
    ((Embedding.restriction f hf).map (inclusion c)) (restrictedLocalSection f hf c)
    (restrictedLocalSection_difference f hf c)

/-- Actual exact restriction retains the original zero composite. -/
theorem restricted_inclusion_projection :
    (Embedding.restriction f hf).map (inclusion c) ≫
      (Embedding.restriction f hf).map (projection c) = 0 :=
  ((Embedding.restriction f hf).map_comp (inclusion c) (projection c)).symm.trans
    ((congrArg (Embedding.restriction f hf).map (inclusion_projection c)).trans
      ((Embedding.restriction f hf).map_zero _ _))

/-- Each literal restricted local section has the degree specified by the
actual integer endpoint, without an endpoint-isomorphism assumption. -/
theorem restrictedLocalSection_projection_unit (i : ι) :
    ((Embedding.restriction f hf).map (projection c)).hom.app
        (op (restrictedCover f U i)) (restrictedLocalSection f hf c i) =
      (Embedding.integerUnit f hf).hom.app (op (restrictedCover f U i))
        ((degreeUnit T).app (op (restrictedCover f U i)) (ULift.up (1 : ℤ))) :=
  (restrictedLocalSection_projection f hf c i).trans
    (Embedding.integerUnit_degreeUnit_app f hf (restrictedCover f U i)
      (ULift.up (1 : ℤ))).symm

/-- The original integer endpoint is the actual right endpoint of the extension map. -/
theorem restrictedExtensionMap_projection :
    restrictedExtensionMap f hf c hU ≫ (Embedding.restriction f hf).map (projection c) =
      projection (restrictedCocycle f hf c) ≫ Embedding.integerUnit f hf :=
  CechConnecting.comparison_projection_map (restrictedCocycle f hf c)
    (restrictedCover_covers f hU) ((Embedding.restriction f hf).map (inclusion c))
    ((Embedding.restriction f hf).map (projection c)) (Embedding.integerUnit f hf)
    (restricted_inclusion_projection f hf c) (restrictedLocalSection f hf c)
    (restrictedLocalSection_projection_unit f hf c) (restrictedLocalSection_difference f hf c)

/-- The genuine original short-complex morphism has identity coefficient
endpoint and the proved native integer endpoint. -/
def restrictedComplexMap :
    complex (restrictedCocycle f hf c) ⟶ (complex c).map (Embedding.restriction f hf) :=
  CechConnecting.comparisonComplexMap ((complex c).map (Embedding.restriction f hf))
    (restrictedCocycle f hf c) (restrictedCover_covers f hU) (Embedding.integerUnit f hf)
    (restrictedLocalSection f hf c) (restrictedLocalSection_projection_unit f hf c)
    (restrictedLocalSection_difference f hf c)

@[simp] theorem restrictedComplexMap_left :
    (restrictedComplexMap f hf c hU).τ₁ = 𝟙 ((Embedding.restriction f hf).obj F) := rfl

@[simp] theorem restrictedComplexMap_right :
    (restrictedComplexMap f hf c hU).τ₃ = Embedding.integerUnit f hf := rfl

end OpenClassRestriction.EmbeddingCech
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
