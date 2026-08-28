import Wikipedia.HopfProblem.SheafLerayCurveCyclesResolution
import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractCore
import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractHomologyExtZero
import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractHomologyBasic

/-!
# Native homology of the cycles augmented resolution in every degree

Applying additive coyoneda to the original degree-`n` cycles resolution
gives a cokernel canonically isomorphic to degree `n + 1` homology of the
original Hom complex.  The degree-zero Ext comparison identifies the actual
middle term with the same homology.  The formulas below retain the original
cycle inclusion and homology quotient; no shifted complex is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Abelian Opposite HomologicalComplex

namespace Wikipedia.HopfProblem.SheafLerayCurve.Abstract

open SheafLerayLowDegrees.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C]

/-- Applying Hom to the original cycles short complex in degree `n`. -/
abbrev cyclesHomAugmentedComplex (A : C) (K : CochainComplex C ℕ) (n : ℕ) :
    ShortComplex AddCommGrpCat :=
  (cyclesComplex K n).map (preadditiveCoyoneda.obj (op A))

/-- The actual Hom-cokernel of the cycles resolution is native homology
in degree `n + 1` of the original Hom complex. -/
def cyclesHomMiddleIso (A : C) (K : CochainComplex C ℕ) (n : ℕ) :
    (cyclesHomAugmentedComplex A K n).opcycles ≅
      (homComplex A K).homology (n + 1) :=
  CokernelCofork.mapIsoOfIsColimit
    (cyclesHomAugmentedComplex A K n).opcyclesIsCokernel
    ((homComplex A K).homologyIsCokernel n (n + 1) (CochainComplex.prev_nat_succ n))
    (Arrow.isoMk (Iso.refl _) (homCyclesIso A K (n + 1))
      (by exact (id_comp _).trans (map_toCycles_homCyclesIso A K n (n + 1)).symm))

/-- The Hom-cokernel comparison sends each original cycle representative
to its native homology quotient class. -/
@[reassoc (attr := simp)]
theorem pOpcycles_cyclesHomMiddleIso_hom (A : C) (K : CochainComplex C ℕ) (n : ℕ) :
    (cyclesHomAugmentedComplex A K n).pOpcycles ≫ (cyclesHomMiddleIso A K n).hom =
      (homCyclesIso A K (n + 1)).hom ≫ (homComplex A K).homologyπ (n + 1) :=
  CokernelCofork.π_mapOfIsColimit (cyclesHomAugmentedComplex A K n).opcyclesIsCokernel _ _

/-- The inverse comparison recovers the original Hom-cokernel class. -/
@[reassoc (attr := simp)]
theorem homCyclesIso_hom_homologyπ_cyclesHomMiddleIso_inv
    (A : C) (K : CochainComplex C ℕ) (n : ℕ) :
    (homCyclesIso A K (n + 1)).hom ≫ (homComplex A K).homologyπ (n + 1) ≫
        (cyclesHomMiddleIso A K n).inv = (cyclesHomAugmentedComplex A K n).pOpcycles := by
  exact (assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (cyclesHomMiddleIso A K n).inv)
      (pOpcycles_cyclesHomMiddleIso_hom A K n).symm).trans
      ((assoc _ _ _).trans
        ((congrArg (fun f => (cyclesHomAugmentedComplex A K n).pOpcycles ≫ f)
          (cyclesHomMiddleIso A K n).hom_inv_id).trans (comp_id _))))

variable [HasExt.{0} C]

/-- The genuine degree-zero Ext cokernel of the cycles resolution is the
native degree-`n + 1` homology of the original Hom complex. -/
def cyclesMiddleIso (A : C) (K : CochainComplex C ℕ) (n : ℕ) :
    Core.middle A (cyclesResolution K n) ≅ (homComplex A K).homology (n + 1) :=
  extZeroHomOpcyclesIso A (cyclesComplex K n) ≪≫ cyclesHomMiddleIso A K n

/-- The actual middle comparison sends an original degree-zero Ext cycle
to its native Hom-complex homology class. -/
@[reassoc]
theorem pOpcycles_cyclesMiddleIso_hom (A : C) (K : CochainComplex C ℕ) (n : ℕ) :
    ((cyclesResolution K n).extZeroComplex A).pOpcycles ≫ (cyclesMiddleIso A K n).hom =
      (extZeroHomIso A (K.cycles (n + 1))).hom ≫ (homCyclesIso A K (n + 1)).hom ≫
        (homComplex A K).homologyπ (n + 1) := by
  change ((cyclesComplex K n).map (extFunctorObj A 0)).pOpcycles ≫
      ((extZeroHomOpcyclesIso A (cyclesComplex K n)).hom ≫
        (cyclesHomMiddleIso A K n).hom) = _
  exact (assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (cyclesHomMiddleIso A K n).hom)
      (pOpcycles_extZeroHomOpcyclesIso_hom A (cyclesComplex K n))).trans
      ((assoc _ _ _).trans
        (congrArg (fun f => (extZeroHomIso A (K.cycles (n + 1))).hom ≫ f)
          (pOpcycles_cyclesHomMiddleIso_hom A K n))))

end Wikipedia.HopfProblem.SheafLerayCurve.Abstract
