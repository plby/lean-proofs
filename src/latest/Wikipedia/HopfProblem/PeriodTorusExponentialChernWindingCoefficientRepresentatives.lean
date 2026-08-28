import Wikipedia.HopfProblem.PeriodTorusExponentialChernCoefficients
import Wikipedia.HopfProblem.SheafHigherDirectImageExtBasic
import Wikipedia.HopfProblem.SingularCohomologyFreeCycles

/-!
# Literal cocycle representatives under the native integral comparison

The canonical homology comparison for forgetting integer scalars sends
the actual additive kernel representative to the original native
integer-linear cocycle class.  This is proved from the genuine kernel
and homology projections, not from a classification by cohomology ranks.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern

open ConstantSheafSingularComparison SheafHigherDirectImage

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule

/-- The genuine exact-functor homology comparison preserves each
literal kernel representative of the original integral short complex. -/
theorem forgetIntegralShortHomologyIso_cycleClass
    (S : ShortComplex (ModuleCat.{0} ℤ))
    (c : FirstHurewicz.ChainHomology.ShortCycle S) :
    (S.mapHomologyIso integralForget).hom
        (ExtBridge.shortCycleClass (S.map integralForget) c.val c.property) =
      FirstHurewicz.ChainHomology.shortCycleClass S c := by
  let h := S.moduleCatLeftHomologyData.map integralForget
  have hc : h.cyclesIso.hom ((S.map integralForget).abCyclesIso.inv
      ⟨c.val, c.property⟩) = c := by
    apply (AddCommGrpCat.mono_iff_injective h.i).mp inferInstance
    rw [← ConcreteCategory.comp_apply,
      ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
      ShortComplex.abCyclesIso_inv_apply_iCycles]
    rfl
  rw [S.moduleCatLeftHomologyData.mapHomologyIso_eq integralForget]
  change integralForget.map S.moduleCatHomologyIso.inv
      (h.homologyIso.hom ((S.map integralForget).homologyπ
        ((S.map integralForget).abCyclesIso.inv ⟨c.val, c.property⟩))) = _
  rw [← ConcreteCategory.comp_apply,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    ConcreteCategory.comp_apply, hc]
  rfl

/-- In every degree the actual forgetful cohomology comparison sends
the literal additive cycle to the original native cocycle class. -/
theorem forgetIntegralHomologyIso_cycleClass
    (K : CochainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (c : SingularCohomologyFree.Cocycle K n) :
    (forgetIntegralHomologyIso K n).hom
        (ExtBridge.cycleClass (forgetIntegralCochains.obj K) n c.val c.property) =
      SingularCohomologyFree.cocycleClass K n c :=
  forgetIntegralShortHomologyIso_cycleClass (K.sc n) c

/-- The inverse comparison retains the original literal cocycle
representative, forgetting only its integer-linear scalar structure. -/
theorem forgetIntegralHomologyIso_inv_cocycleClass
    (K : CochainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (c : SingularCohomologyFree.Cocycle K n) :
    (forgetIntegralHomologyIso K n).inv
        (SingularCohomologyFree.cocycleClass K n c) =
      ExtBridge.cycleClass (forgetIntegralCochains.obj K) n c.val c.property := by
  rw [← forgetIntegralHomologyIso_cycleClass K n c]
  exact (forgetIntegralHomologyIso K n).addCommGroupIsoToAddEquiv.symm_apply_apply _

end Wikipedia.HopfProblem.PeriodTorusExponentialChern
