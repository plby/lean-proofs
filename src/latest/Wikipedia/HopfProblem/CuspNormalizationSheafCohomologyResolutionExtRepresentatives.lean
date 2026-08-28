import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionHigher

/-!
# Actual cycle representatives of the Ext comparison
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace AugmentedResolution

variable (R : AugmentedResolution C) (P : C)

/-- The actual kernel inclusion gives cycles in the degree-zero
section complex. -/
def extCycleMap : AddCommGrpCat.of (Ext P R.K 0) ⟶ (R.extZeroComplex P).cycles :=
  (R.extZeroComplex P).liftCycles ((extFunctorObj P 0).map (kernel.ι R.complex.g))
    (R.second.map (extFunctorObj P 0)).zero

@[reassoc] theorem extCycleMap_i :
    R.extCycleMap P ≫ (R.extZeroComplex P).iCycles =
      (extFunctorObj P 0).map (kernel.ι R.complex.g) :=
  (R.extZeroComplex P).liftCycles_i _ _

theorem extOneHomologyData_cyclesIso_inv [Subsingleton (Ext P R.complex.X₁ 1)] :
    (R.extOneHomologyData P).cyclesIso.inv = R.extCycleMap P := by
  apply (cancel_mono (R.extZeroComplex P).iCycles).mp
  exact (R.extOneHomologyData P).cyclesIso_inv_comp_iCycles.trans (R.extCycleMap_i P).symm

/-- The degree-one comparison preserves the cycle given by the
actual kernel inclusion. -/
theorem extOneIso_connecting_cycle [Subsingleton (Ext P R.complex.X₁ 1)] :
    AddCommGrpCat.ofHom (connecting P R.first_shortExact 0) ≫ (R.extOneIso P).hom =
      R.extCycleMap P ≫ (R.extZeroComplex P).homologyπ :=
  (R.extOneIso_connecting P).trans
    (congrArg (fun f => f ≫ (R.extZeroComplex P).homologyπ)
      (R.extOneHomologyData_cyclesIso_inv P))

end AugmentedResolution

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution
