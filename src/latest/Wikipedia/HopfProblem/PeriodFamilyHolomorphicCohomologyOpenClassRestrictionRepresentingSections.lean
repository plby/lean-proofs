import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionRepresentingSectionsBasic

/-!
# Original representing-unit sections on every image open

The original representing unit sends degree one to the restriction of the
original free-open universal section. The same literal formula holds after
applying any original morphism out of that free-open sheaf.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.RepresentingSections

open HolomorphicSheafCohomology
open CuspNormalization.SheafCohomologyFinitePushforward
open HolomorphicPicard.CechExtension

variable {X : TopCat.{0}} (A : Opens X)

/-- The original representing unit carries each local degree-one section to
the literal restriction of the original free-open universal section. -/
theorem representingUnit_degreeUnit_app (V : Opens A) :
    (OpenRestriction.representingUnit A).hom.app (op V)
        ((degreeUnit (TopCat.of A)).app (op V) (ULift.up (1 : ℤ))) =
      (OpenRestriction.freeOpen A).obj.map
        (homOfLE (OpenRestriction.openImage_obj_le A V)).op
          (OpenRestriction.freeHomEquiv A (OpenRestriction.freeOpen A) (𝟙 _)) :=
  homRestrictionEquiv_degreeUnit_app A (OpenRestriction.freeOpen A) (𝟙 _) V

/-- After an actual ambient sheaf morphism, the representing-unit section is
still the literal restriction of that morphism's original universal section. -/
theorem representingUnit_comp_degreeUnit_app (F : AbelianSheaf X)
    (g : OpenRestriction.freeOpen A ⟶ F) (V : Opens A) :
    g.hom.app (op ((OpenRestriction.openImage A).obj V))
        ((OpenRestriction.representingUnit A).hom.app (op V)
          ((degreeUnit (TopCat.of A)).app (op V) (ULift.up (1 : ℤ)))) =
      F.obj.map (homOfLE (OpenRestriction.openImage_obj_le A V)).op
        (OpenRestriction.freeHomEquiv A F g) := by
  have h := congrArg
    (fun η : integerSheaf (TopCat.of A) ⟶ (OpenRestriction.restriction A).obj F =>
      η.hom.app (op V) ((degreeUnit (TopCat.of A)).app (op V) (ULift.up (1 : ℤ))))
    (OpenRestriction.representingUnit_comp A g)
  exact h.trans (homRestrictionEquiv_degreeUnit_app A F g V)

end OpenClassRestriction.RepresentingSections
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
