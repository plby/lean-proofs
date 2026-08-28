import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainIntegral
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Comparison with native integral singular cohomology

The actual forgetful functor from integer modules to additive commutative
groups is an equivalence, so it preserves kernels, cokernels, and homology.
Combining its canonical homology comparison with `integralCochainIso`
identifies the coefficient-general construction at `ℤ` with the existing
native integral singular cohomology, naturally for continuous pullbacks.
-/

noncomputable section

open CategoryTheory Opposite

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

/-- The original forgetful equivalence from integer modules to abelian groups. -/
abbrev integralForget : ModuleCat.{0} ℤ ⥤ AddCommGrpCat.{0} :=
  forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}

/-- The canonical kernel-and-cokernel comparison for the genuine forgetful
functor, with no exactness assumption on the complex. -/
def forgetIntegralHomologyIso (K : CochainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    (forgetIntegralCochains.obj K).homology n ≅ integralForget.obj (K.homology n) :=
  (K.sc n).mapHomologyIso integralForget

/-- Forgetful homology comparison commutes with the original complex maps. -/
@[reassoc]
theorem forgetIntegralHomologyIso_naturality
    {K L : CochainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (forgetIntegralCochains.map f) n ≫
        (forgetIntegralHomologyIso L n).hom =
      (forgetIntegralHomologyIso K n).hom ≫
        integralForget.map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n).map f)
    integralForget

/-- The additive coefficient-`ℤ` cohomology is the established native
integral singular cohomology with its scalar structure forgotten. -/
def integralCohomologyIso (X : Type) [TopologicalSpace X] (n : ℕ) :
    (singularCochainComplex X (AddCommGrpCat.of ℤ)).homology n ≅
      integralForget.obj (SingularCohomologyFree.SingularCohomology X n) :=
  HomologicalComplex.homologyMapIso (integralCochainIso X) n ≪≫
    forgetIntegralHomologyIso (SingularCohomologyFree.singularCochainComplex X) n

/-- The comparison is induced by the literal cochain map followed by the
canonical exact-functor homology comparison. -/
@[simp]
theorem integralCohomologyIso_hom (X : Type) [TopologicalSpace X] (n : ℕ) :
    (integralCohomologyIso X n).hom =
      HomologicalComplex.homologyMap (integralCochainIso X).hom n ≫
        (forgetIntegralHomologyIso (SingularCohomologyFree.singularCochainComplex X) n).hom :=
  rfl

@[simp]
theorem integralCohomologyIso_inv (X : Type) [TopologicalSpace X] (n : ℕ) :
    (integralCohomologyIso X n).inv =
      (forgetIntegralHomologyIso (SingularCohomologyFree.singularCochainComplex X) n).inv ≫
        HomologicalComplex.homologyMap (integralCochainIso X).inv n := rfl

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual additive and integer-linear cohomology pullbacks correspond
under the comparison, for the original continuous map. -/
@[reassoc]
theorem integralCohomologyIso_naturality (f : C(X, Y)) (n : ℕ) :
    HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℤ) f) n ≫
        (integralCohomologyIso X n).hom =
      (integralCohomologyIso Y n).hom ≫
        integralForget.map
          (HomologicalComplex.homologyMap (SingularCohomologyFree.singularPullback f) n) := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (integralCochainIso_naturality f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  simp only [integralCohomologyIso_hom]
  rw [← Category.assoc, h, Category.assoc, forgetIntegralHomologyIso_naturality,
    ← Category.assoc]

/-- The same comparison as an additive equivalence with the original
integral cohomology group. -/
def integralCohomologyEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    (singularCochainComplex X (AddCommGrpCat.of ℤ)).homology n ≃+
      SingularCohomologyFree.SingularCohomology X n :=
  (integralCohomologyIso X n).addCommGroupIsoToAddEquiv

@[simp]
theorem integralCohomologyEquiv_apply (X : Type) [TopologicalSpace X] (n : ℕ)
    (x : (singularCochainComplex X (AddCommGrpCat.of ℤ)).homology n) :
    integralCohomologyEquiv X n x = (integralCohomologyIso X n).hom x := rfl

/-- Pointwise naturality uses the established integral cohomology pullback,
not a newly defined substitute. -/
theorem integralCohomologyEquiv_naturality (f : C(X, Y)) (n : ℕ)
    (x : (singularCochainComplex Y (AddCommGrpCat.of ℤ)).homology n) :
    integralCohomologyEquiv X n
        (HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℤ) f) n x) =
      SingularCohomologyFree.singularCohomologyPullback f n (integralCohomologyEquiv Y n x) :=
  ConcreteCategory.congr_hom (integralCohomologyIso_naturality f n) x

/-- The comparison is an isomorphism of the actual contravariant
cohomology functors in every degree. -/
def integralCohomologyNatIso (n : ℕ) :
    singularCochainFunctor (AddCommGrpCat.of ℤ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) n ≅
      SingularCohomologyFree.singularCohomologyFunctor n ⋙ integralForget :=
  NatIso.ofComponents (fun X => integralCohomologyIso X.unop n)
    (fun f => integralCohomologyIso_naturality f.unop.hom n)

@[simp]
theorem integralCohomologyNatIso_app (X : Type) [TopologicalSpace X] (n : ℕ) :
    (integralCohomologyNatIso n).app (op (TopCat.of X)) = integralCohomologyIso X n := rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
