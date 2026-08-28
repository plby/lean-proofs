import Wikipedia.HopfProblem.SheafLerayCurveCyclesSequence
import Wikipedia.HopfProblem.SheafLerayCurveCyclesResolutionHomologyNaturality

/-!
# Coefficient-complex naturality of the actual cycles Leray sequence

The sequence uses the native cycles maps on its Ext terms and the
native homology maps on its Hom and Hom-complex-homology terms.
Every square is proved for the original cochain map.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite

namespace Wikipedia.HopfProblem.SheafLerayCurve.Abstract

open SheafLerayLowDegrees.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  (A : C) {K L : CochainComplex C ℕ} (φ : K ⟶ L) (n : ℕ)

/-- The native edge map commutes with every original cochain map. -/
@[reassoc] theorem cyclesEdgeMap_naturality :
    HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ) (n + 1) ≫
        cyclesEdgeMap A L n =
      cyclesEdgeMap A K n ≫ (preadditiveCoyoneda.obj (op A)).map
        (HomologicalComplex.homologyMap φ (n + 1)) := by
  apply AddCommGrpCat.ext
  intro x
  have h₀ := ConcreteCategory.congr_hom (cyclesMiddleIso_inv_naturality A φ n) x
  have h₁ := ConcreteCategory.congr_hom
    (Core.edgeMap_naturality A (cyclesResolutionMap φ n)) ((cyclesMiddleIso A K n).inv x)
  have h₂ := ConcreteCategory.congr_hom
    (extZeroHomIso_hom_naturality A (HomologicalComplex.homologyMap φ (n + 1)))
    (Core.edgeMap A (cyclesResolution K n) ((cyclesMiddleIso A K n).inv x))
  exact (congrArg (fun z => (extZeroHomIso A (L.homology (n + 1))).hom
    (Core.edgeMap A (cyclesResolution L n) z)) h₀).trans
      ((congrArg (extZeroHomIso A (L.homology (n + 1))).hom h₁).trans h₂)

/-- The two actual connecting maps commute with the native cycles map. -/
@[reassoc] theorem cyclesTransgression_naturality :
    (preadditiveCoyoneda.obj (op A)).map (HomologicalComplex.homologyMap φ (n + 1)) ≫
        cyclesTransgression A L n =
      cyclesTransgression A K n ≫ (extFunctorObj A 2).map
        (HomologicalComplex.cyclesMap φ n) := by
  apply AddCommGrpCat.ext
  intro x
  have h₀ := ConcreteCategory.congr_hom
    ((extZeroHomNatIso A).inv.naturality (HomologicalComplex.homologyMap φ (n + 1))) x
  have h₁ := ConcreteCategory.congr_hom
    (Core.transgression_naturality A (cyclesResolutionMap φ n))
    ((extZeroHomIso A (K.homology (n + 1))).inv x)
  exact (congrArg (Core.transgression A (cyclesResolution L n)) h₀).trans h₁

variable [Injective (K.X n)] [Injective (L.X n)]

/-- The native Ext injection commutes with the original cycles and Hom-complex maps. -/
@[reassoc] theorem cyclesFirstMap_naturality :
    (extFunctorObj A 1).map (HomologicalComplex.cyclesMap φ n) ≫ cyclesFirstMap A L n =
      cyclesFirstMap A K n ≫ HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ) (n + 1) := by
  let : Injective (cyclesResolution K n).complex.X₁ := inferInstanceAs (Injective (K.X n))
  let : Injective (cyclesResolution L n).complex.X₁ := inferInstanceAs (Injective (L.X n))
  apply AddCommGrpCat.ext
  intro x
  have h₁ := ConcreteCategory.congr_hom
    (Core.firstMap_naturality A (cyclesResolutionMap φ n)) x
  have h₂ := ConcreteCategory.congr_hom (cyclesMiddleIso_hom_naturality A φ n)
    (Core.firstMap A (cyclesResolution K n) x)
  exact (congrArg (cyclesMiddleIso A L n).hom h₁).trans h₂

end Wikipedia.HopfProblem.SheafLerayCurve.Abstract
