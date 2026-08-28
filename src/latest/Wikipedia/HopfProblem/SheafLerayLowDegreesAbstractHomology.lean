import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractCore
import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractHomologyExtZero
import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractHomologyBasic

/-!
# The native middle term in the low-degree Leray sequence

The middle cokernel obtained from the genuine Ext exact sequences is
canonically the first homology of the actual Hom complex.  No injectivity
assumption on the initial term is needed for this identification.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Abelian Opposite

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]

/-- The actual Ext cokernel is the native first homology of the section complex. -/
def middleIso (A : C) (K : CochainComplex C ℕ) :
    Core.middle A (resolution K) ≅ (homComplex A K).homology 1 :=
  extZeroHomOpcyclesIso A (complex K) ≪≫ homMiddleIso A K

/-- The middle comparison carries each degree-zero Ext cycle to its native homology class. -/
@[reassoc]
theorem pOpcycles_middleIso_hom (A : C) (K : CochainComplex C ℕ) :
    ((resolution K).extZeroComplex A).pOpcycles ≫ (middleIso A K).hom =
      (extZeroHomIso A (K.cycles 1)).hom ≫ (homCyclesIso A K 1).hom ≫
        (homComplex A K).homologyπ 1 := by
  change ((complex K).map (extFunctorObj A 0)).pOpcycles ≫
      ((extZeroHomOpcyclesIso A (complex K)).hom ≫ (homMiddleIso A K).hom) = _
  exact (assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (homMiddleIso A K).hom)
      (pOpcycles_extZeroHomOpcyclesIso_hom A (complex K))).trans
      ((assoc _ _ _).trans
        (congrArg (fun f => (extZeroHomIso A (K.cycles 1)).hom ≫ f)
          (pOpcycles_homMiddleIso_hom A K))))

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract
