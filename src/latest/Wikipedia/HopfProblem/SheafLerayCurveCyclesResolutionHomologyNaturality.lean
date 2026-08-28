import Wikipedia.HopfProblem.SheafLerayCurveCyclesResolutionHomology
import Wikipedia.HopfProblem.SheafLerayCurveCyclesResolutionMap
import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractHomologyNaturality

/-!
# Naturality of the all-degree cycles middle comparison

The comparison of the cycles-resolution middle term with degree `n + 1`
homology commutes with actual coefficient-complex maps.  It uses the native
maps on the original cycles and original Hom-complex homology, in both
directions, rather than a reindexing or a transported replacement complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Abelian Opposite
open HomologicalComplex

namespace Wikipedia.HopfProblem.SheafLerayCurve.Abstract

open SheafLerayLowDegrees.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  (A : C) {K L : CochainComplex C ℕ} (φ : K ⟶ L)

/-- The actual cycles-resolution cokernel comparison is natural for every
coefficient-complex map and every degree. -/
@[reassoc]
theorem cyclesMiddleIso_hom_naturality (n : ℕ) :
    Core.middleMap A (cyclesResolutionMap φ n) ≫ (cyclesMiddleIso A L n).hom =
      (cyclesMiddleIso A K n).hom ≫ homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ) (n + 1) := by
  let F := preadditiveCoyoneda.obj (op A)
  let ψ := (F.mapHomologicalComplex (.up ℕ)).map φ
  apply (cancel_epi ((cyclesResolution K n).extZeroComplex A).pOpcycles).mp
  apply AddCommGrpCat.ext
  intro x
  have h₀ := ConcreteCategory.congr_hom
    (ShortComplex.p_opcyclesMap ((cyclesResolutionMap φ n).extZeroMap A)) x
  have h₁ := ConcreteCategory.congr_hom (pOpcycles_cyclesMiddleIso_hom A L n)
    ((extFunctorObj A 0).map (cyclesMap φ (n + 1)) x)
  have h₂ := ConcreteCategory.congr_hom
    (extZeroHomIso_hom_naturality A (cyclesMap φ (n + 1))) x
  have h₃ := ConcreteCategory.congr_hom (homCyclesIso_hom_naturality A φ (n + 1))
    ((extZeroHomIso A (K.cycles (n + 1))).hom x)
  have h₄ := ConcreteCategory.congr_hom (homologyπ_naturality ψ (n + 1))
    ((homCyclesIso A K (n + 1)).hom ((extZeroHomIso A (K.cycles (n + 1))).hom x))
  have h₅ := ConcreteCategory.congr_hom (pOpcycles_cyclesMiddleIso_hom A K n) x
  exact (congrArg (cyclesMiddleIso A L n).hom h₀).trans
    (h₁.trans
      ((congrArg (fun z => (homComplex A L).homologyπ (n + 1)
          ((homCyclesIso A L (n + 1)).hom z)) h₂).trans
        ((congrArg ((homComplex A L).homologyπ (n + 1)) h₃).trans
          (h₄.symm.trans (congrArg (homologyMap ψ (n + 1)) h₅.symm)))))

/-- The inverse native cycles middle comparison commutes with the actual
coefficient-complex maps as well. -/
@[reassoc]
theorem cyclesMiddleIso_inv_naturality (n : ℕ) :
    homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ) (n + 1) ≫
        (cyclesMiddleIso A L n).inv =
      (cyclesMiddleIso A K n).inv ≫ Core.middleMap A (cyclesResolutionMap φ n) := by
  apply (cancel_epi (cyclesMiddleIso A K n).hom).mp
  rw [← assoc, ← cyclesMiddleIso_hom_naturality, assoc, Iso.hom_inv_id, comp_id,
    ← assoc, Iso.hom_inv_id, id_comp]

end Wikipedia.HopfProblem.SheafLerayCurve.Abstract
