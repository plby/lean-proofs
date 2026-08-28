import Wikipedia.HopfProblem.SheafSingularCupComparisonRowGlobalUnitComparison
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalCohomology

/-!
# The actual global unit induces isomorphisms on the row quotients

The maps were already defined from the original ring unit. The proved
global-cochain quasi-isomorphism and the exact comparison identities
show that those same maps are isomorphisms on normal paracompact spaces.
No new native Ext comparison is chosen.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal

open RingCochains ConstantSheafSingularComparison

variable (X : TopCat.{0}) [NormalSpace X] [ParacompactSpace X]

/-- The actual unit-induced first map is an isomorphism. -/
theorem unitOne_isIso : IsIso (AddCommGrpCat.ofHom (unitOne X)) := by
  let := globalCochainComparison_homology_isIso X (AddCommGrpCat.of ℂ) 0
  rw [← unitOne_original]
  infer_instance

/-- The actual unit-induced second map is an isomorphism. -/
theorem unitTwo_isIso : IsIso (AddCommGrpCat.ofHom (unitTwo X)) := by
  let := globalCochainComparison_homology_isIso X (AddCommGrpCat.of ℂ) 1
  rw [← unitTwo_original]
  infer_instance

/-- The already defined actual first unit map, bundled as an isomorphism. -/
def unitOneIso : (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 1 ≅
    AddCommGrpCat.of (globalData X).CohomologyOne := by
  let f : (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 1 ⟶
      AddCommGrpCat.of (globalData X).CohomologyOne := AddCommGrpCat.ofHom (unitOne X)
  letI : IsIso f := unitOne_isIso X
  exact asIso f

/-- The already defined actual second unit map, bundled as an isomorphism. -/
def unitTwoIso : (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 2 ≅
    AddCommGrpCat.of (globalData X).CohomologyTwo := by
  let f : (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 2 ⟶
      AddCommGrpCat.of (globalData X).CohomologyTwo := AddCommGrpCat.ofHom (unitTwo X)
  letI : IsIso f := unitTwo_isIso X
  exact asIso f

@[simp] theorem unitOneIso_hom : (unitOneIso X).hom = AddCommGrpCat.ofHom (unitOne X) := rfl

@[simp] theorem unitTwoIso_hom : (unitTwoIso X).hom = AddCommGrpCat.ofHom (unitTwo X) := rfl

/-- In particular, the original first unit-induced map is injective. -/
theorem unitOne_injective : Function.Injective (unitOne X) :=
  (unitOneIso X).addCommGroupIsoToAddEquiv.injective

/-- The original second unit-induced map can therefore cancel genuine cup-product identities. -/
theorem unitTwo_injective : Function.Injective (unitTwo X) :=
  (unitTwoIso X).addCommGroupIsoToAddEquiv.injective

end Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal
