import Wikipedia.HopfProblem.SheafSingularCupComparisonSingularComplex

/-!
# Original singular cocycles and their native classes

These class maps are the canonical cycle projection into the original
categorical homology. Their simplex-value formulas follow from the
proved short-complex isomorphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.Singular

open ConstantSheafSingularComparison

/-- The actual canonical class of a concrete cocycle in an additive short complex. -/
def shortClass (S : ShortComplex AddCommGrpCat.{0}) : S.g.hom.ker →+ S.homology :=
  (S.abCyclesIso.inv ≫ S.homologyπ).hom

theorem shortClass_surjective (S : ShortComplex AddCommGrpCat.{0}) :
    Function.Surjective (shortClass S) :=
  (AddCommGrpCat.epi_iff_surjective (S.abCyclesIso.inv ≫ S.homologyπ)).mp inferInstance

/-- The literal middle component of a short-complex map acts on original cocycles. -/
def shortCocycleMap {S T : ShortComplex AddCommGrpCat.{0}} (f : S ⟶ T) :
    S.g.hom.ker →+ T.g.hom.ker where
  toFun a := ⟨f.τ₂ a.val, by
    change T.g (f.τ₂ a.val) = 0
    rw [← ConcreteCategory.comp_apply, f.comm₂₃]
    change f.τ₃ (S.g a.val) = 0
    rw [show S.g a.val = 0 from a.property, map_zero]⟩
  map_zero' := Subtype.ext (map_zero f.τ₂.hom)
  map_add' a b := Subtype.ext (map_add f.τ₂.hom a.val b.val)

@[simp] theorem shortCocycleMap_val {S T : ShortComplex AddCommGrpCat.{0}}
    (f : S ⟶ T) (a : S.g.hom.ker) :
    (shortCocycleMap f a).val = f.τ₂ a.val := rfl

theorem shortCocycleMap_cycles {S T : ShortComplex AddCommGrpCat.{0}} (f : S ⟶ T) :
    S.abCyclesIso.inv ≫ ShortComplex.cyclesMap f =
      AddCommGrpCat.ofHom (shortCocycleMap f) ≫ T.abCyclesIso.inv := by
  apply (cancel_mono T.iCycles).1
  ext a
  change T.iCycles (ShortComplex.cyclesMap f (S.abCyclesIso.inv a)) =
    T.iCycles (T.abCyclesIso.inv (shortCocycleMap f a))
  rw [T.abCyclesIso_inv_apply_iCycles]
  exact (ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i f)
    (S.abCyclesIso.inv a)).trans
      (congrArg f.τ₂ (S.abCyclesIso_inv_apply_iCycles a))

/-- Native homology maps act on actual cocycle representatives by the actual map. -/
theorem shortClass_naturality {S T : ShortComplex AddCommGrpCat.{0}}
    (f : S ⟶ T) (a : S.g.hom.ker) :
    ShortComplex.homologyMap f (shortClass S a) = shortClass T (shortCocycleMap f a) := by
  have h : S.abCyclesIso.inv ≫ S.homologyπ ≫ ShortComplex.homologyMap f =
      AddCommGrpCat.ofHom (shortCocycleMap f) ≫ T.abCyclesIso.inv ≫ T.homologyπ := by
    rw [ShortComplex.homologyπ_naturality, ← Category.assoc, shortCocycleMap_cycles,
      Category.assoc]
  exact ConcreteCategory.congr_hom h a

variable (X : Type) [TopologicalSpace X] (R : Type) [CommRing R]

/-- The literal outgoing kernel in the original singular cochain complex. -/
abbrev Cocycle (n : ℕ) :=
  ((singularCochainComplex X (AddCommGrpCat.of R)).sc n).g.hom.ker

/-- The actual canonical class in the original singular cohomology group. -/
abbrev classMap (n : ℕ) :
    Cocycle X R n →+ (singularCochainComplex X (AddCommGrpCat.of R)).homology n :=
  shortClass ((singularCochainComplex X (AddCommGrpCat.of R)).sc n)

theorem classMap_surjective (n : ℕ) : Function.Surjective (classMap X R n) :=
  shortClass_surjective _

/-- Actual first cocycle evaluation on original singular simplices. -/
def oneCocycleEvaluation : Cocycle X R 1 →+ (cofaceData X R).CocycleOne :=
  shortCocycleMap (oneComplexIso X R).hom

/-- Actual second cocycle evaluation on original singular simplices. -/
def twoCocycleEvaluation : Cocycle X R 2 →+ (cofaceData X R).CocycleTwo :=
  shortCocycleMap (twoComplexIso X R).hom

@[simp] theorem oneCocycleEvaluation_val (a : Cocycle X R 1) :
    (oneCocycleEvaluation X R a).val = evaluation X R 1 a.val := rfl

@[simp] theorem twoCocycleEvaluation_val (a : Cocycle X R 2) :
    (twoCocycleEvaluation X R a).val = evaluation X R 2 a.val := rfl

/-- The proved comparison keeps the literal original first cocycle representative. -/
theorem oneHomologyEquiv_class (a : Cocycle X R 1) :
    oneHomologyEquiv X R (classMap X R 1 a) =
      (cofaceData X R).classOne (oneCocycleEvaluation X R a) := by
  change (SheafCupProductResolution.Coface.oneHomologyIso (cofaceData X R)).hom
    (ShortComplex.homologyMap (oneComplexIso X R).hom (shortClass _ a)) = _
  rw [shortClass_naturality]
  exact ConcreteCategory.congr_hom
    (SheafCupProductResolution.Coface.oneHomologyIso_class (cofaceData X R))
    (oneCocycleEvaluation X R a)

/-- The proved comparison keeps the literal original second cocycle representative. -/
theorem twoHomologyEquiv_class (a : Cocycle X R 2) :
    twoHomologyEquiv X R (classMap X R 2 a) =
      (cofaceData X R).classTwo (twoCocycleEvaluation X R a) := by
  change (SheafCupProductResolution.Coface.twoHomologyIso (cofaceData X R)).hom
    (ShortComplex.homologyMap (twoComplexIso X R).hom (shortClass _ a)) = _
  rw [shortClass_naturality]
  exact ConcreteCategory.congr_hom
    (SheafCupProductResolution.Coface.twoHomologyIso_class (cofaceData X R))
    (twoCocycleEvaluation X R a)

end Wikipedia.HopfProblem.SheafSingularCupComparison.Singular
