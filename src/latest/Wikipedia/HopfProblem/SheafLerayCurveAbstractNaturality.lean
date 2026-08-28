import Wikipedia.HopfProblem.SheafLerayCurveAbstract
import Wikipedia.HopfProblem.SheafLerayCurveVanishingNaturality
import Wikipedia.HopfProblem.SheafLerayCurveCyclesSequenceNaturality

/-!
# Original-complex naturality of the curve-type short exact sequence

The injection uses the inverse of the proved actual quotient-induced
Ext comparison. Both original maps commute with native cochain maps;
no naturality premise on a replacement cohomology theory is introduced.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite

namespace Wikipedia.HopfProblem.SheafLerayCurve.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  (A : C) {K L : CochainComplex C ℕ} (φ : K ⟶ L) (n : ℕ)

/-- The right edge is natural even without any vanishing assumptions. -/
@[reassoc] theorem curveEdgeMap_naturality :
    HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ) (n + 2) ≫
      curveEdgeMap A L n =
    curveEdgeMap A K n ≫ (preadditiveCoyoneda.obj (op A)).map
      (HomologicalComplex.homologyMap φ (n + 2)) :=
  cyclesEdgeMap_naturality A φ (n + 1)

/-- The left edge is natural for actual complexes satisfying the stated
finite homology-object vanishings. -/
@[reassoc] theorem curveFirstMap_naturality
    (hIK : ∀ q : ℕ, Injective (K.X q)) (hIL : ∀ q : ℕ, Injective (L.X q))
    (hK : HigherVanishing A K (n + 3)) (hL : HigherVanishing A L (n + 3)) :
    (extFunctorObj A 1).map (HomologicalComplex.homologyMap φ (n + 1)) ≫
      curveFirstMap A L hIL n hL =
    curveFirstMap A K hIK n hK ≫ HomologicalComplex.homologyMap
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ) (n + 2) := by
  let : Injective (K.X (n + 1)) := hIK (n + 1)
  let : Injective (L.X (n + 1)) := hIL (n + 1)
  apply AddCommGrpCat.ext
  intro x
  have h₀ := ConcreteCategory.congr_hom
    (cyclesHomologyExtOneIso_inv_naturality A φ hIK hIL (n + 3) hK hL n le_rfl) x
  have h₁ := ConcreteCategory.congr_hom (cyclesFirstMap_naturality A φ (n + 1))
    ((cyclesHomologyExtOneIso A K hIK (n + 3) hK n le_rfl).inv x)
  exact (congrArg (cyclesFirstMap A L (n + 1)) h₀).trans h₁

end Wikipedia.HopfProblem.SheafLerayCurve.Abstract
