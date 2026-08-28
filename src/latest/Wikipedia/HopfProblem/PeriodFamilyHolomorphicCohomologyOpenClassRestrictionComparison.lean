import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingMaps

/-!
# The right endpoint of a Čech comparison in an arbitrary target sheaf

These compatibility names reuse the arbitrary-endpoint projection
identities proved in `CechConnecting`. No new comparison construction,
invertibility assumption, or exactness assumption is introduced.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension

variable {X : TopCat.{0}} {F G D : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X}
  (c : CechOneCocycle F U) (hU : ∀ x : X, ∃ i : ι, x ∈ U i)
  (ιF : F ⟶ G) (πG : G ⟶ D) (hzero : ιF ≫ πG = 0)
  (η : degreeSheaf X ⟶ D) (t : ∀ i : ι, Section G (U i))
  (hp : ∀ i : ι, πG.hom.app (op (U i)) (t i) =
    η.hom.app (op (U i)) ((degreeUnit X).app (op (U i)) (ULift.up (1 : ℤ))))
  (hdiff : ∀ i j : ι, res G inf_le_right (t j) - res G inf_le_left (t i) =
    ιF.hom.app (op (U i ⊓ U j)) (c.value i j))

include hzero hp in
/-- Projection of the actual glued section is the prescribed image of
its native integer degree, using the existing local comparison theorem. -/
theorem comparisonSectionHom_projection_to (V : Opens X) (s : ExtensionSection c V) :
    πG.hom.app (op V) (comparisonSectionHom c hU ιF t hdiff V s) =
      η.hom.app (op V) ((degreeUnit X).app (op V) (degreeHom c V s)) :=
  CechConnecting.comparisonSectionHom_projection_map c hU ιF πG η hzero t hp hdiff V s

include hzero hp in
/-- The projection identity for the actual presheaf comparison. -/
theorem comparisonPre_projection_to :
    comparisonPre c hU ιF t hdiff ≫ πG.hom =
      (projectionPre c ≫ degreeUnit X) ≫ η.hom :=
  (CechConnecting.comparisonPre_projection_map c hU ιF πG η hzero t hp hdiff).trans
    (Category.assoc _ _ _).symm

include hzero hp in
/-- The genuine sheafified comparison commutes with projection to any
target sheaf through the specified native integer-degree morphism. -/
theorem comparison_projection_to :
    comparison c hU ιF t hdiff ≫ πG = projection c ≫ η :=
  CechConnecting.comparison_projection_map c hU ιF πG η hzero t hp hdiff

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
