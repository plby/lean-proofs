import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSheafifyBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyFineBasic

/-!
# Native sheafification retains local vanishing

If a presheaf morphism vanishes on every smaller open set, its original
stalk map vanishes at every point of that open. The genuine sheafification
unit is an isomorphism on stalks, and its naturality therefore gives the
same local vanishing for the actual sheafified morphism.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.Sheafification

open HolomorphicSheafCohomology

variable {X : TopCat.{0}}
variable {P Q : TopCat.Presheaf AddCommGrpCat.{0} X}

/-- Local zero components give zero on the original presheaf stalk. -/
theorem stalkMap_eq_zero_of_app_eq_zero (f : P ⟶ Q) (U : Opens X)
    (hf : ∀ V : Opens X, V ≤ U → f.app (op V) = 0)
    (x : X) (hx : x ∈ U) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  obtain ⟨V, hVU, hxV, s, rfl⟩ := P.exists_le_germ_eq a hx
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hf V hVU]
  exact (Q.germ V x hxV).hom.map_zero

/-- Actual sheafification preserves vanishing on the specified open,
using the original stalk isomorphism of its unit. -/
theorem map_isZeroOn_of_app_eq_zero (f : P ⟶ Q) (U : Opens X)
    (hf : ∀ V : Opens X, V ≤ U → f.app (op V) = 0) :
    IsZeroOn ((presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).map f) U := by
  apply isZeroOn_of_stalkMap_eq_zero
  intro x hx
  let K := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  have hz : K.map f = 0 := stalkMap_eq_zero_of_app_eq_zero f U hf x hx
  have hnatural : unit P ≫
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map f).hom =
        f ≫ unit Q :=
    (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X) f).symm
  change K.map (((presheafToSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{0}).map f).hom) = 0
  apply (cancel_epi (K.map (unit P))).mp
  rw [comp_zero, ← K.map_comp, hnatural, K.map_comp, hz, zero_comp]

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.Sheafification
