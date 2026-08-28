import Wikipedia.HopfProblem.SheafSingularCupComparisonRingCofaces
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSheafBasic

/-!
# The ring sheaves of actual singular cochains

The ring objects are native sheafifications of the function rings on
singular simplices. Forgetting multiplication gives the original
additive singular-cochain sheaves, by a canonical isomorphism preserving
the original units. Every coface is the sheafification of its actual
simplex pullback.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains

open ConstantSheafSingularComparison
open CuspNormalization.SheafForgetStalk (forgetToAdd)

variable (X : TopCat.{0})

/-- The actual ring sheafification of singular cochains in degree `n`. -/
abbrev sheaf (n : ℕ) : TopCat.Sheaf CommRingCat.{0} X :=
  (ringSheafification X).obj (presheaf X n)

/-- The original native sheafification unit of the ring cochains. -/
def unit (n : ℕ) : presheaf X n ⟶ (sheaf X n).obj :=
  toSheafify (Opens.grothendieckTopology X) (presheaf X n)

/-- Forgetting multiplication gives the previously defined additive sheaf. -/
def forgetSheafIso (n : ℕ) :
    (forgetSheaf X).obj (sheaf X n) ≅ cochainSheaf X (AddCommGrpCat.of ℂ) n :=
  forgetSheafificationIso X (presheaf X n) ≪≫
    (additiveSheafification X).mapIso (presheafAddIso X n)

/-- The comparison preserves the original singular-cochain unit. -/
@[reassoc] theorem forgetSheafIso_unit (n : ℕ) :
    Functor.whiskerRight (unit X n) forgetToAdd ≫ (forgetSheafIso X n).hom.hom =
      (presheafAddIso X n).hom ≫ cochainSheafUnit X (AddCommGrpCat.of ℂ) n := by
  change Functor.whiskerRight (unit X n) forgetToAdd ≫
      ((forgetSheafificationIso X (presheaf X n)).hom.hom ≫
        ((additiveSheafification X).map (presheafAddIso X n).hom).hom) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫
      ((additiveSheafification X).map (presheafAddIso X n).hom).hom)
        (forgetSheafificationIso_unit X (presheaf X n))).trans
      (toSheafify_naturality (Opens.grothendieckTopology X)
        (presheafAddIso X n).hom).symm)

/-- Each ring-sheaf coface is induced by the original simplex face map. -/
def coface (n : ℕ) (i : Fin (n + 2)) : sheaf X n ⟶ sheaf X (n + 1) :=
  (ringSheafification X).map (cofacePresheaf X n i)

/-- The original units intertwine the actual cofaces. -/
@[reassoc] theorem unit_coface (n : ℕ) (i : Fin (n + 2)) :
    unit X n ≫ (coface X n i).hom = cofacePresheaf X n i ≫ unit X (n + 1) :=
  (toSheafify_naturality (Opens.grothendieckTopology X) (cofacePresheaf X n i)).symm

/-- The actual cosimplicial identities persist under native sheafification. -/
theorem coface_comp (n : ℕ) (i j : Fin (n + 2)) (hij : i ≤ j) :
    coface X n i ≫ coface X (n + 1) j.succ =
      coface X n j ≫ coface X (n + 1) i.castSucc := by
  change (ringSheafification X).map (cofacePresheaf X n i) ≫
      (ringSheafification X).map (cofacePresheaf X (n + 1) j.succ) = _
  rw [← (ringSheafification X).map_comp, cofacePresheaf_comp X n i j hij,
    (ringSheafification X).map_comp]
  rfl

/-- The actual section rings and their actual singular cofaces. -/
def sectionData (U : Opens X) : SheafCupProduct.Coface.Data
    ((sheaf X 0).obj.obj (op U)) ((sheaf X 1).obj.obj (op U))
    ((sheaf X 2).obj.obj (op U)) ((sheaf X 3).obj.obj (op U)) where
  δ0 i := ((coface X 0 i).hom.app (op U)).hom
  δ1 i := ((coface X 1 i).hom.app (op U)).hom
  δ2 i := ((coface X 2 i).hom.app (op U)).hom
  coface01 i j hij := by
    exact congrArg (fun f => (f.hom.app (op U)).hom) (coface_comp X 0 i j hij)
  coface12 i j hij := by
    exact congrArg (fun f => (f.hom.app (op U)).hom) (coface_comp X 1 i j hij)

/-- In particular, the actual global sections carry the singular cofaces. -/
abbrev globalData := sectionData X ⊤

end Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains
