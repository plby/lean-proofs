import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractCore
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExtNaturality

/-!
# Naturality of the augmented low-degree sequence

The three maps commute with genuine maps of augmented resolutions.
In particular these statements apply to actual coefficient
endomorphisms, rather than to an abstractly chosen scalar action.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian
open Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract.Core

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  (A : C) {R S : AugmentedResolution C} (φ : AugmentedResolution.Hom R S)

/-- The induced map of the actual middle cokernels. -/
def middleMap : middle A R ⟶ middle A S :=
  ShortComplex.opcyclesMap (φ.extZeroMap A)

@[reassoc]
theorem edgeMap_naturality : middleMap A φ ≫ edgeMap A S =
    edgeMap A R ≫ (extFunctorObj A 0).map φ.complex.τ₃ :=
  ShortComplex.fromOpcycles_naturality (φ.extZeroMap A)

@[reassoc]
theorem transgression_naturality :
    (extFunctorObj A 0).map φ.complex.τ₃ ≫ transgression A S =
      transgression A R ≫ (extFunctorObj A 2).map φ.augmentation :=
  φ.connectingTwo_naturality A

/-- A genuine map of the right short complexes. -/
def secondComplexMap : secondComplex A R ⟶ secondComplex A S where
  τ₁ := middleMap A φ
  τ₂ := (extFunctorObj A 0).map φ.complex.τ₃
  τ₃ := (extFunctorObj A 2).map φ.augmentation
  comm₁₂ := edgeMap_naturality A φ
  comm₂₃ := transgression_naturality A φ

variable [Injective R.complex.X₁] [Injective S.complex.X₁]

@[reassoc]
theorem firstMap_naturality :
    (extFunctorObj A 1).map φ.augmentation ≫ firstMap A S =
      firstMap A R ≫ middleMap A φ := by
  let := Ext.subsingleton_of_injective A R.complex.X₁ 0
  let := Ext.subsingleton_of_injective A S.complex.X₁ 0
  apply AddCommGrpCat.ext
  intro x
  have h₁ := ConcreteCategory.congr_hom (φ.extOneIso_naturality A) x
  have h₂ := ConcreteCategory.congr_hom
    (ShortComplex.homologyι_naturality (φ.extZeroMap A)) ((R.extOneIso A).hom x)
  exact (congrArg (S.extZeroComplex A).homologyι h₁).trans h₂

/-- A genuine map of the left short complexes. -/
def firstComplexMap : firstComplex A R ⟶ firstComplex A S where
  τ₁ := (extFunctorObj A 1).map φ.augmentation
  τ₂ := middleMap A φ
  τ₃ := (extFunctorObj A 0).map φ.complex.τ₃
  comm₁₂ := firstMap_naturality A φ
  comm₂₃ := edgeMap_naturality A φ

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract.Core
