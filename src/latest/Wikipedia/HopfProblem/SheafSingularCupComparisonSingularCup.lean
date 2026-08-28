import Wikipedia.HopfProblem.SheafSingularCupComparisonSingularClasses
import Wikipedia.HopfProblem.SheafCupProductTransport
import Mathlib.Data.Complex.Basic

/-!
# Alexander–Whitney multiplication on original singular cohomology

The original cochain product evaluates a two-simplex on its first and
last edges. The proved native homology comparisons descend this actual
product to the original degree-one and degree-two cohomology groups.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.Singular

open FirstHurewicz ConstantSheafSingularComparison

variable (X : Type) [TopologicalSpace X] (R : Type) [CommRing R]

/-- The actual low-degree AW cochain, specified on the original simplex generators. -/
def cupCochain (a b : Cochains X (AddCommGrpCat.of R) 1) :
    Cochains X (AddCommGrpCat.of R) 2 :=
  (evaluation X R 2).symm
    ((cofaceData X R).cupOne (evaluation X R 1 a) (evaluation X R 1 b))

/-- The literal front-edge/back-edge formula on an original singular two-simplex. -/
theorem cupCochain_simplex (a b : Cochains X (AddCommGrpCat.of R) 1)
    (σ : SingularSimplex X 2) :
    cupCochain X R a b (simplexChain X 2 σ) =
      a (simplexChain X 1 (σ.comp (simplexFace 1 2))) *
        b (simplexChain X 1 (σ.comp (simplexFace 1 0))) :=
  congrFun ((evaluation X R 2).apply_symm_apply
    ((cofaceData X R).cupOne (evaluation X R 1 a) (evaluation X R 1 b))) σ

/-- The actual product cocycle in the original complex. -/
def cupCocycle (a b : Cocycle X R 1) : Cocycle X R 2 :=
  shortCocycleMap (twoComplexIso X R).inv
    ((cofaceData X R).cupCocycle
      (oneCocycleEvaluation X R a) (oneCocycleEvaluation X R b))

@[simp] theorem cupCocycle_val (a b : Cocycle X R 1) :
    (cupCocycle X R a b).val = cupCochain X R a.val b.val := rfl

theorem twoCocycleEvaluation_cupCocycle (a b : Cocycle X R 1) :
    twoCocycleEvaluation X R (cupCocycle X R a b) =
      (cofaceData X R).cupCocycle
        (oneCocycleEvaluation X R a) (oneCocycleEvaluation X R b) := by
  apply Subtype.ext
  exact (evaluation X R 2).apply_symm_apply _

/-- AW multiplication on the native singular cohomology with ring coefficients. -/
def ringCupProduct :
    (singularCochainComplex X (AddCommGrpCat.of R)).homology 1 →+
      (singularCochainComplex X (AddCommGrpCat.of R)).homology 1 →+
        (singularCochainComplex X (AddCommGrpCat.of R)).homology 2 :=
  SheafCupProduct.transportPairing (oneHomologyEquiv X R) (twoHomologyEquiv X R)
    (cofaceData X R).cup

theorem ringCupProduct_comparison
    (a b : (singularCochainComplex X (AddCommGrpCat.of R)).homology 1) :
    twoHomologyEquiv X R (ringCupProduct X R a b) =
      (cofaceData X R).cup (oneHomologyEquiv X R a) (oneHomologyEquiv X R b) :=
  SheafCupProduct.transportPairing_comparison _ _ _ _ _

/-- The native cohomology product has the literal original cocycle representative. -/
theorem ringCupProduct_class (a b : Cocycle X R 1) :
    ringCupProduct X R (classMap X R 1 a) (classMap X R 1 b) =
      classMap X R 2 (cupCocycle X R a b) := by
  apply (twoHomologyEquiv X R).injective
  rw [ringCupProduct_comparison, oneHomologyEquiv_class, oneHomologyEquiv_class,
    SheafCupProduct.Coface.Data.cup_classOne, twoHomologyEquiv_class,
    twoCocycleEvaluation_cupCocycle]

/-- The complex-valued AW product on the original additive singular cochain complex. -/
abbrev cupProduct :
    (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 1 →+
      (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 1 →+
        (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 2 :=
  ringCupProduct X ℂ

theorem cupProduct_class (a b : Cocycle X ℂ 1) :
    cupProduct X (classMap X ℂ 1 a) (classMap X ℂ 1 b) =
      classMap X ℂ 2 (cupCocycle X ℂ a b) :=
  ringCupProduct_class X ℂ a b

end Wikipedia.HopfProblem.SheafSingularCupComparison.Singular
