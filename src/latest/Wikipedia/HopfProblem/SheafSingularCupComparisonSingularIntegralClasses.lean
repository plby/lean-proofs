import Wikipedia.HopfProblem.SheafSingularCupComparisonSingularClasses
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonIntegralCoefficientExtCohomology
import Wikipedia.HopfProblem.SingularCohomologyFreeCycles

/-!
# Original integral classes under the actual complex coefficient map

The forgetful comparison preserves the canonical cycle projection. This
identifies the image of every original integral cocycle class under the
already defined integral-to-complex cohomology map.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.Singular

open FirstHurewicz ConstantSheafSingularComparison

/-- Forgetting scalar compatibility does not change an original integral cocycle. -/
def forgetCocycle (S : ShortComplex (ModuleCat.{0} ℤ)) :
    LinearMap.ker S.g.hom →+ (S.map integralForget).g.hom.ker where
  toFun a := ⟨a.val, a.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem integralForget_projection (S : ShortComplex (ModuleCat.{0} ℤ)) :
    (S.map integralForget).homologyπ ≫ (S.mapHomologyIso integralForget).hom =
      (S.mapCyclesIso integralForget).hom ≫ integralForget.map S.homologyπ := by
  let h := S.homologyData.left
  let eH : (S.map integralForget).homology ≅ integralForget.obj h.H :=
    (h.map integralForget).homologyIso
  let eK : (S.map integralForget).cycles ≅ integralForget.obj h.K :=
    (h.map integralForget).cyclesIso
  have hh : (S.mapHomologyIso integralForget).hom =
      eH.hom ≫ integralForget.map h.homologyIso.inv :=
    congrArg (fun e : (S.map integralForget).homology ≅
      integralForget.obj S.homology => e.hom) (h.mapHomologyIso_eq integralForget)
  have hc : (S.mapCyclesIso integralForget).hom =
      eK.hom ≫ integralForget.map h.cyclesIso.inv :=
    congrArg (fun e : (S.map integralForget).cycles ≅
      integralForget.obj S.cycles => e.hom) (h.mapCyclesIso_eq integralForget)
  have hp : (S.map integralForget).homologyπ ≫ eH.hom =
      eK.hom ≫ integralForget.map h.π :=
    (h.map integralForget).homologyπ_comp_homologyIso_hom
  rw [hh, hc, ← Category.assoc, hp, Category.assoc,
    ← integralForget.map_comp, h.π_comp_homologyIso_inv,
    integralForget.map_comp, Category.assoc]

theorem integralForget_cycles (S : ShortComplex (ModuleCat.{0} ℤ)) :
    AddCommGrpCat.ofHom (forgetCocycle S) ≫ (S.map integralForget).abCyclesIso.inv ≫
        (S.mapCyclesIso integralForget).hom =
      integralForget.map S.moduleCatCyclesIso.inv := by
  apply (cancel_mono (integralForget.map S.iCycles)).1
  ext a
  change S.iCycles ((S.mapCyclesIso integralForget).hom
    ((S.map integralForget).abCyclesIso.inv (forgetCocycle S a))) =
      S.iCycles (S.moduleCatCyclesIso.inv a)
  have h₁ : S.iCycles ((S.mapCyclesIso integralForget).hom
      ((S.map integralForget).abCyclesIso.inv (forgetCocycle S a))) = a.val :=
    (ConcreteCategory.congr_hom (S.mapCyclesIso_hom_iCycles integralForget)
      ((S.map integralForget).abCyclesIso.inv (forgetCocycle S a))).trans
        ((S.map integralForget).abCyclesIso_inv_apply_iCycles (forgetCocycle S a))
  have h₂ : S.iCycles (S.moduleCatCyclesIso.inv a) = a.val :=
    congrArg (fun f : S.moduleCatLeftHomologyData.K ⟶ S.X₂ => f.hom a)
      S.moduleCatCyclesIso_inv_iCycles
  exact h₁.trans h₂.symm

/-- The actual forgetful homology isomorphism preserves each original integral class. -/
theorem forgetCocycle_class (S : ShortComplex (ModuleCat.{0} ℤ))
    (a : LinearMap.ker S.g.hom) :
    (S.mapHomologyIso integralForget).hom
        (shortClass (S.map integralForget) (forgetCocycle S a)) =
      FirstHurewicz.ChainHomology.shortCycleClass S a := by
  calc
    _ = S.homologyπ ((S.mapCyclesIso integralForget).hom
        ((S.map integralForget).abCyclesIso.inv (forgetCocycle S a))) :=
      ConcreteCategory.congr_hom (integralForget_projection S)
        ((S.map integralForget).abCyclesIso.inv (forgetCocycle S a))
    _ = S.homologyπ (S.moduleCatCyclesIso.inv a) :=
      congrArg S.homologyπ (ConcreteCategory.congr_hom (integralForget_cycles S) a)
    _ = _ := ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_π a

variable (X : Type) [TopologicalSpace X]

/-- The literal complex-valued image of an original integral singular cocycle. -/
def integralToComplexCocycle (n : ℕ)
    (a : SingularCohomologyFree.Cocycle (SingularCohomologyFree.singularCochainComplex X) n) :
    Cocycle X ℂ n :=
  shortCocycleMap
    ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) n).map
      (integralToComplexCochainMap X))
    (forgetCocycle ((SingularCohomologyFree.singularCochainComplex X).sc n) a)

@[simp] theorem integralToComplexCocycle_apply (n : ℕ)
    (a : SingularCohomologyFree.Cocycle (SingularCohomologyFree.singularCochainComplex X) n)
    (c : Chains X n) :
    DFunLike.coe (F := Cochains X (AddCommGrpCat.of ℂ) n)
        (integralToComplexCocycle X n a).val c =
      (a.val c : ℂ) := rfl

/-- The already defined coefficient map preserves the actual cocycle class formula. -/
theorem integralToComplexCohomologyHom_class (n : ℕ)
    (a : SingularCohomologyFree.Cocycle (SingularCohomologyFree.singularCochainComplex X) n) :
    integralToComplexCohomologyHom X n
        (SingularCohomologyFree.cocycleClass
          (SingularCohomologyFree.singularCochainComplex X) n a) =
      classMap X ℂ n (integralToComplexCocycle X n a) := by
  let S := (SingularCohomologyFree.singularCochainComplex X).sc n
  have h : (forgetIntegralHomologyIso
      (SingularCohomologyFree.singularCochainComplex X) n).inv
        (SingularCohomologyFree.cocycleClass
          (SingularCohomologyFree.singularCochainComplex X) n a) =
      shortClass (S.map integralForget) (forgetCocycle S a) := by
    exact (congrArg (S.mapHomologyIso integralForget).inv
      (forgetCocycle_class S a)).symm.trans
        (ConcreteCategory.congr_hom (S.mapHomologyIso integralForget).hom_inv_id _)
  change HomologicalComplex.homologyMap (integralToComplexCochainMap X) n
    ((forgetIntegralHomologyIso _ n).inv _) = _
  exact (congrArg (HomologicalComplex.homologyMap (integralToComplexCochainMap X) n) h).trans
    (shortClass_naturality _ _)

end Wikipedia.HopfProblem.SheafSingularCupComparison.Singular
