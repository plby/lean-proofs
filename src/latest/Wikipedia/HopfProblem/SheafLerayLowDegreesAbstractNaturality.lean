import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstract
import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractHomologyNaturality

/-!
# Naturality of the genuine low-degree Leray sequence

All three arrows commute with an actual cochain map.  The Ext arrows
use the actual maps on native degree-zero homology, while the edge
map uses the actual maps on native degree-one homology.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  (A : C) {K L : CochainComplex C ℕ} (φ : K ⟶ L)

/-- Naturality of the native edge map. -/
@[reassoc]
theorem edgeMap_naturality :
    HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ) 1 ≫
        edgeMap A L =
      edgeMap A K ≫ (preadditiveCoyoneda.obj (op A)).map
        (HomologicalComplex.homologyMap φ 1) := by
  apply AddCommGrpCat.ext
  intro x
  have h₀ := ConcreteCategory.congr_hom (middleIso_inv_naturality A φ) x
  have h₁ := ConcreteCategory.congr_hom
    (Core.edgeMap_naturality A (resolutionMap φ)) ((middleIso A K).inv x)
  have h₂ := ConcreteCategory.congr_hom
    (extZeroHomIso_hom_naturality A (HomologicalComplex.homologyMap φ 1))
    (Core.edgeMap A (resolution K) ((middleIso A K).inv x))
  exact (congrArg (fun z => (extZeroHomIso A (L.homology 1)).hom
    (Core.edgeMap A (resolution L) z)) h₀).trans
      ((congrArg (extZeroHomIso A (L.homology 1)).hom h₁).trans h₂)

/-- Naturality of the genuine composite Ext connecting map. -/
@[reassoc]
theorem transgression_naturality :
    (preadditiveCoyoneda.obj (op A)).map (HomologicalComplex.homologyMap φ 1) ≫
        transgression A L =
      transgression A K ≫ (extFunctorObj A 2).map
        (HomologicalComplex.homologyMap φ 0) := by
  apply AddCommGrpCat.ext
  intro x
  have h₀ := ConcreteCategory.congr_hom
    ((extZeroHomNatIso A).inv.naturality (HomologicalComplex.homologyMap φ 1)) x
  have h₁ := ConcreteCategory.congr_hom
    (Core.transgression_naturality A (resolutionMap φ))
    ((extZeroHomIso A (K.homology 1)).inv x)
  exact (congrArg (Core.transgression A (resolution L)) h₀).trans h₁

variable [Injective (K.X 0)] [Injective (L.X 0)]

/-- Naturality of the degree-one Ext injection. -/
@[reassoc]
theorem firstMap_naturality :
    (extFunctorObj A 1).map (HomologicalComplex.homologyMap φ 0) ≫ firstMap A L =
      firstMap A K ≫ HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ) 1 := by
  let : Injective (resolution K).complex.X₁ := inferInstanceAs (Injective (K.X 0))
  let : Injective (resolution L).complex.X₁ := inferInstanceAs (Injective (L.X 0))
  apply AddCommGrpCat.ext
  intro x
  have h₁ := ConcreteCategory.congr_hom (Core.firstMap_naturality A (resolutionMap φ)) x
  have h₂ := ConcreteCategory.congr_hom (middleIso_hom_naturality A φ)
    (Core.firstMap A (resolution K) x)
  exact (congrArg (middleIso A L).hom h₁).trans h₂

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract
