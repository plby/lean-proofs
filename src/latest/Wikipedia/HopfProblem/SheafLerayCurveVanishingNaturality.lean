import Wikipedia.HopfProblem.SheafLerayCurveVanishing
import Wikipedia.HopfProblem.SheafLerayLowDegreesTransportNaturality

/-!
# Naturality of the proved cycle-to-homology Ext comparison

The comparison is induced by the original homology quotient, so its
forward naturality is the native cycle/homology square under Ext. The
inverse square follows by inverting these actual isomorphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayCurve.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  (A : C) {K L : CochainComplex C ℕ} (φ : K ⟶ L)
  (hIK : ∀ q : ℕ, Injective (K.X q)) (hIL : ∀ q : ℕ, Injective (L.X q))
  (N : ℕ) (hK : HigherVanishing A K N) (hL : HigherVanishing A L N)
  (n : ℕ) (hn : n + 3 ≤ N)

/-- The original quotient-induced Ext comparison commutes with every
actual map of the original cochain complexes. -/
@[reassoc] theorem cyclesHomologyExtOneIso_hom_naturality :
    (extFunctorObj A 1).map (HomologicalComplex.cyclesMap φ (n + 1)) ≫
      (cyclesHomologyExtOneIso A L hIL N hL n hn).hom =
    (cyclesHomologyExtOneIso A K hIK N hK n hn).hom ≫
      (extFunctorObj A 1).map (HomologicalComplex.homologyMap φ (n + 1)) := by
  rw [cyclesHomologyExtOneIso_hom, cyclesHomologyExtOneIso_hom]
  let E := extFunctorObj A 1
  exact (E.map_comp _ _).symm.trans
    ((congrArg E.map (HomologicalComplex.homologyπ_naturality φ (n + 1)).symm).trans
      (E.map_comp _ _))

/-- Inverse comparisons retain the same native naturality square. -/
@[reassoc] theorem cyclesHomologyExtOneIso_inv_naturality :
    (extFunctorObj A 1).map (HomologicalComplex.homologyMap φ (n + 1)) ≫
      (cyclesHomologyExtOneIso A L hIL N hL n hn).inv =
    (cyclesHomologyExtOneIso A K hIK N hK n hn).inv ≫
      (extFunctorObj A 1).map (HomologicalComplex.cyclesMap φ (n + 1)) :=
  SheafLerayLowDegrees.inverse_naturality
    (cyclesHomologyExtOneIso A K hIK N hK n hn)
    (cyclesHomologyExtOneIso A L hIL N hL n hn) _ _
    (cyclesHomologyExtOneIso_hom_naturality A φ hIK hIL N hK hL n hn)

end Wikipedia.HopfProblem.SheafLerayCurve.Abstract
